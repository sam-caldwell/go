// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package noder

import (
	"cmp"
	"fmt"
	"go/constant"
	"internal/pkgbits"
	"internal/types/errors"
	"io"
	"runtime"
	"slices"
	"strings"
	"strconv"
    "cmd/internal/objabi"

	"cmd/compile/internal/base"
	"cmd/compile/internal/inline"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/pgoir"
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"cmd/compile/internal/syntax"
	"cmd/compile/internal/types2"
	"cmd/internal/src"
)

// localPkgReader holds the package reader used for reading the local
// package. It exists so the unified IR linker can refer back to it
// later.
var localPkgReader *pkgReader

// LookupFunc returns the ir.Func for an arbitrary full symbol name if
// that function exists in the set of available export data.
//
// This allows lookup of arbitrary functions and methods that aren't otherwise
// referenced by the local package and thus haven't been read yet.
//
// TODO(prattmic): Does not handle instantiation of generic types. Currently
// profiles don't contain the original type arguments, so we won't be able to
// create the runtime dictionaries.
//
// TODO(prattmic): Hit rate of this function is usually fairly low, and errors
// are only used when debug logging is enabled. Consider constructing cheaper
// errors by default.
func LookupFunc(fullName string) (*ir.Func, error) {
	pkgPath, symName, err := ir.ParseLinkFuncName(fullName)
	if err != nil {
		return nil, fmt.Errorf("error parsing symbol name %q: %v", fullName, err)
	}

	pkg, ok := types.PkgMap()[pkgPath]
	if !ok {
		return nil, fmt.Errorf("pkg %s doesn't exist in %v", pkgPath, types.PkgMap())
	}

	// Symbol naming is ambiguous. We can't necessarily distinguish between
	// a method and a closure. e.g., is foo.Bar.func1 a closure defined in
	// function Bar, or a method on type Bar? Thus we must simply attempt
	// to lookup both.

	fn, err := lookupFunction(pkg, symName)
	if err == nil {
		return fn, nil
	}

	fn, mErr := lookupMethod(pkg, symName)
	if mErr == nil {
		return fn, nil
	}

	return nil, fmt.Errorf("%s is not a function (%v) or method (%v)", fullName, err, mErr)
}

// PostLookupCleanup performs cleanup operations needed
// after a series of calls to LookupFunc, specifically invoking
// readBodies to post-process any funcs on the "todoBodies" list
// that were added as a result of the lookup operations.
func PostLookupCleanup() {
	readBodies(typecheck.Target, false)
}

func lookupFunction(pkg *types.Pkg, symName string) (*ir.Func, error) {
	sym := pkg.Lookup(symName)

	// TODO(prattmic): Enclosed functions (e.g., foo.Bar.func1) are not
	// present in objReader, only as OCLOSURE nodes in the enclosing
	// function.
	pri, ok := objReader[sym]
	if !ok {
		return nil, fmt.Errorf("func sym %v missing objReader", sym)
	}

	node, err := pri.pr.objIdxMayFail(pri.idx, nil, nil, false)
	if err != nil {
		return nil, fmt.Errorf("func sym %v lookup error: %w", sym, err)
	}
	name := node.(*ir.Name)
	if name.Op() != ir.ONAME || name.Class != ir.PFUNC {
		return nil, fmt.Errorf("func sym %v refers to non-function name: %v", sym, name)
	}
	return name.Func, nil
}

func lookupMethod(pkg *types.Pkg, symName string) (*ir.Func, error) {
	// N.B. readPackage creates a Sym for every object in the package to
	// initialize objReader and importBodyReader, even if the object isn't
	// read.
	//
	// However, objReader is only initialized for top-level objects, so we
	// must first lookup the type and use that to find the method rather
	// than looking for the method directly.
	typ, meth, err := ir.LookupMethodSelector(pkg, symName)
	if err != nil {
		return nil, fmt.Errorf("error looking up method symbol %q: %v", symName, err)
	}

	pri, ok := objReader[typ]
	if !ok {
		return nil, fmt.Errorf("type sym %v missing objReader", typ)
	}

	node, err := pri.pr.objIdxMayFail(pri.idx, nil, nil, false)
	if err != nil {
		return nil, fmt.Errorf("func sym %v lookup error: %w", typ, err)
	}
	name := node.(*ir.Name)
	if name.Op() != ir.OTYPE {
		return nil, fmt.Errorf("type sym %v refers to non-type name: %v", typ, name)
	}
	if name.Alias() {
		return nil, fmt.Errorf("type sym %v refers to alias", typ)
	}
	if name.Type().IsInterface() {
		return nil, fmt.Errorf("type sym %v refers to interface type", typ)
	}

	for _, m := range name.Type().Methods() {
		if m.Sym == meth {
			fn := m.Nname.(*ir.Name).Func
			return fn, nil
		}
	}

	return nil, fmt.Errorf("method %s missing from method set of %v", symName, typ)
}

// unified constructs the local package's Internal Representation (IR)
// from its syntax tree (AST).
//
// The pipeline contains 2 steps:
//
//  1. Generate the export data "stub".
//
//  2. Generate the IR from the export data above.
//
// The package data "stub" at step (1) contains everything from the local package,
// but nothing that has been imported. When we're actually writing out export data
// to the output files (see writeNewExport), we run the "linker", which:
//
//   - Updates compiler extensions data (e.g. inlining cost, escape analysis results).
//
//   - Handles re-exporting any transitive dependencies.
//
//   - Prunes out any unnecessary details (e.g. non-inlineable functions, because any
//     downstream importers only care about inlinable functions).
//
// The source files are typechecked twice: once before writing the export data
// using types2, and again after reading the export data using gc/typecheck.
// The duplication of work will go away once we only use the types2 type checker,
// removing the gc/typecheck step. For now, it is kept because:
//
//   - It reduces the engineering costs in maintaining a fork of typecheck
//     (e.g. no need to backport fixes like CL 327651).
//
//   - It makes it easier to pass toolstash -cmp.
//
//   - Historically, we would always re-run the typechecker after importing a package,
//     even though we know the imported data is valid. It's not ideal, but it's
//     not causing any problems either.
//
//   - gc/typecheck is still in charge of some transformations, such as rewriting
//     multi-valued function calls or transforming ir.OINDEX to ir.OINDEXMAP.
//
// Using the syntax tree with types2, which has a complete representation of generics,
// the unified IR has the full typed AST needed for introspection during step (1).
// In other words, we have all the necessary information to build the generic IR form
// (see writer.captureVars for an example).
func unified(m posMap, noders []*noder) {
	inline.InlineCall = unifiedInlineCall
	typecheck.HaveInlineBody = unifiedHaveInlineBody
	pgoir.LookupFunc = LookupFunc
	pgoir.PostLookupCleanup = PostLookupCleanup

	data := writePkgStub(m, noders)

	target := typecheck.Target

	localPkgReader = newPkgReader(pkgbits.NewPkgDecoder(types.LocalPkg.Path, data))
	readPackage(localPkgReader, types.LocalPkg, true)

	r := localPkgReader.newReader(pkgbits.SectionMeta, pkgbits.PrivateRootIdx, pkgbits.SyncPrivate)
	r.pkgInit(types.LocalPkg, target)

    readBodies(target, false)

    // Apply decorator wrappers (split to $orig and wrapper + composition).
    applyDecoratorWrappers(target)

    // If wrapper composition caused any imported functions to be looked up,
    // finalize reading of any queued bodies.
    PostLookupCleanup()

	// Check that nothing snuck past typechecking.
	for _, fn := range target.Funcs {
		if fn.Typecheck() == 0 {
			base.FatalfAt(fn.Pos(), "missed typecheck: %v", fn)
		}

		// For functions, check that at least their first statement (if
		// any) was typechecked too.
		if len(fn.Body) != 0 {
			if stmt := fn.Body[0]; stmt.Typecheck() == 0 {
				base.FatalfAt(stmt.Pos(), "missed typecheck: %v", stmt)
			}
		}
	}

	// For functions originally came from package runtime,
	// mark as norace to prevent instrumenting, see issue #60439.
	for _, fn := range target.Funcs {
		if !base.Flag.CompilingRuntime && types.RuntimeSymName(fn.Sym()) != "" {
			fn.Pragma |= ir.Norace
		}
	}

	base.ExitIfErrors() // just in case
}

// funcDecorators holds parsed decorator expressions keyed by fully-qualified
// function name (package path + "." + function name). Populated during decl
// collection in writer.
type decoRec struct {
    Exprs   []syntax.Expr
    Imports map[string]string // alias -> package path
}

var funcDecorators map[string]decoRec

// applyDecoratorWrappers rewrites decorated functions into wrappers that call
// a synthesized $orig function containing the original body. MVP: no actual
// decorator composition yet; wrapper simply forwards to $orig.
func applyDecoratorWrappers(target *ir.Package) {
    if len(funcDecorators) == 0 {
        return
    }
    for _, fn := range target.Funcs {
        sym := fn.Sym()
        if sym == nil || sym.Pkg != types.LocalPkg {
            continue
        }
        // Lookup decorators for function or method.
        key := types.LocalPkg.Path + "." + sym.Name
        rec, ok := funcDecorators[key]
        if !ok && strings.HasPrefix(sym.Name, "init") {
            // Writer records init under plain source name "init".
            key2 := types.LocalPkg.Path + ".init"
            if rec2, ok2 := funcDecorators[key2]; ok2 {
                rec, ok = rec2, ok2
            }
        }
        if !ok {
            // Try method key form: pkg.(Recv).Name
            if recv := fn.Type().Recv(); recv != nil {
                rtyp := recv.Type
                star := ""
                if rtyp.IsPtr() {
                    star = "*"
                    rtyp = rtyp.Elem()
                }
                if rtyp.Sym() != nil {
                    mkey := types.LocalPkg.Path + ".(" + star + rtyp.Sym().Name + ")." + sym.Name
                    if rec2, ok2 := funcDecorators[mkey]; ok2 {
                        rec, ok = rec2, ok2
                    }
                }
            }
        }
        if !ok || len(rec.Exprs) == 0 {
            continue
        }

        // Disallow init (including compiler-suffixed forms like init.0) and main.main decorations.
        if sym.Name == "init" || strings.HasPrefix(sym.Name, "init.") || (types.LocalPkg.Name == "main" && sym.Name == "main") {
            base.ErrorfAt(fn.Pos(), 0, "invalid decorator target: %s cannot be decorated", sym.Name)
            continue
        }

        // Read a fresh copy of the original body into a new function $orig.
        pri, ok := bodyReaderFor(fn)
        if !ok {
            base.ErrorfAt(fn.Pos(), 0, "cannot decorate assembly or cgo-declared function")
            continue
        }

        // Build $orig symbol and function using collision-free mangling.
        origSym := lookupFreeOrigSym(sym.Name)
        if origSym == nil {
            // Could not find a free symbol name; skip for safety.
            continue
        }

        origFn := ir.NewFunc(fn.Pos(), fn.Nname.Pos(), origSym, fn.Type())
        // Register function without redeclaring params twice; reader will declare params.
        origFn.Nname.Defn = origFn
        target.Funcs = append(target.Funcs, origFn)
        // Provide a bodyReader entry so inliner/analysis can retrieve inline body if needed.
        bodyReader[origFn] = pri
        pri.funcBody(origFn)

        // Build wrapper body that forwards to $orig with same params.
        ir.WithFunc(fn, func() {
            pos := fn.Pos()
            var args ir.Nodes
            // Build args from current function's parameter decls in order.
            for _, nn := range fn.Dcl {
                if nn.Class == ir.PPARAM {
                    args.Append(nn)
                }
            }

            // Compose decorators bottom→top (closest first). MVP: bare identifiers only.
            var fun ir.Node = origFn.Nname
            if n := len(rec.Exprs); n > 0 {
                for i := n - 1; i >= 0; i-- {
                    switch dx := rec.Exprs[i].(type) {
                    case *syntax.Name:
                        if d := findDecoratorCallee(dx, rec.Imports); d != nil {
                            // Validate signature: func(S) S
                            if !checkDecoratorSignature(fn, pos, d, fun.Type()) {
                                // emit error and skip this decorator
                                break
                            }
                            fun = typecheck.Call(pos, d, []ir.Node{fun}, false)
                        } else {
                            base.ErrorfAt(fn.Pos(), 0, "unknown decorator: %s", dx.Value)
                        }
                    case *syntax.CallExpr:
                        // Parameterized decorator: D(args...)(fun)
                        cal := buildDecoratorCall(pos, dx, rec.Imports)
                        if cal == nil {
                            base.ErrorfAt(fn.Pos(), 0, "decorator argument is not compile-time evaluable")
                            continue
                        }
                        // Validate signature: func(S) S
                        if !checkDecoratorSignature(fn, pos, cal, fun.Type()) {
                            break
                        }
                        fun = typecheck.Call(pos, cal, []ir.Node{fun}, false)
                    default:
                        base.ErrorfAt(fn.Pos(), 0, "unsupported decorator form (qualified names not yet supported)")
                    }
                }
            }

            // Call composed function with args: fun(args...)
            call := typecheck.Call(pos, fun, args, fn.Type().IsVariadic())

            var body ir.Nodes
            if fn.Type().NumResults() == 0 {
                body.Append(typecheck.Stmt(call))
            } else {
                ret := ir.NewReturnStmt(pos, []ir.Node{call})
                body.Append(typecheck.Stmt(ret))
            }

            fn.Body = body
        })
        // Mark function as having been modified.
    }
}


// findDecoratorCallee resolves a bare name decorator in the local package.
// lookupFreeOrigSym returns a local package symbol for the synthesized
// original body with a collision-free name based on base (e.g., foo ->
// foo$orig, foo$orig1, foo$orig2, ...). Returns nil if a free name
// cannot be found within a reasonable bound (extremely unlikely).
func lookupFreeOrigSym(base string) *types.Sym {
    const maxAttempts = 1000
    baseName := base + "$orig"
    if s := types.LocalPkg.Lookup(baseName); s.Def == nil {
        return s
    }
    for i := 1; i <= maxAttempts; i++ {
        s := types.LocalPkg.Lookup(baseName + strconv.Itoa(i))
        if s.Def == nil {
            return s
        }
    }
    return nil
}

func findDecoratorCallee(n *syntax.Name, imports map[string]string) ir.Node {
    // Bare name: local function
    dsym := typecheck.Lookup(n.Value)
    if dname, ok := dsym.Def.(*ir.Name); ok {
        return dname
    }
    // Not found locally; cannot be bare from another package
    return nil
}

// buildDecoratorCall builds an IR call for a parameterized decorator factory with
// compile-time evaluable arguments. Supports basic literals and untyped bools.
func buildDecoratorCall(pos src.XPos, call *syntax.CallExpr, imports map[string]string) ir.Node {
    var callee ir.Node
    switch fun := call.Fun.(type) {
    case *syntax.Name:
        callee = findDecoratorCallee(fun, imports)
    case *syntax.SelectorExpr:
        // Qualified callee: alias.Dec
        if pkgName, ok := fun.X.(*syntax.Name); ok {
            if imports != nil {
                if path, ok := imports[pkgName.Value]; ok {
                    if name := fun.Sel.Value; name != "" {
                        if c := resolveImportedFunc(path, name); c != nil {
                            callee = c
                        }
                    }
                }
            }
        }
    default:
        // Qualified idents and complex expressions not yet supported.
        return nil
    }
    if callee == nil {
        return nil
    }
    // Convert arguments
    var args ir.Nodes
    for _, a := range call.ArgList {
        v := decoratorConstArg(pos, a, imports)
        if v == nil {
            return nil
        }
        args = append(args, v)
    }
    return typecheck.Call(pos, callee, args, false)
}

// decoratorConstArg converts a syntax.Expr to an IR constant node if possible.
func decoratorConstArg(pos src.XPos, e syntax.Expr, imports map[string]string) ir.Node {
    switch x := e.(type) {
    case *syntax.BasicLit:
        // string or integer literals only
        switch x.Kind {
        case syntax.StringLit:
            s, err := strconv.Unquote(x.Value)
            if err != nil {
                s = x.Value
            }
            return ir.NewString(pos, s)
        case syntax.IntLit:
            // parse as int64
            // Permit 0x / 0b / 0o? scanner normalized; use base autodetect
            // Use strconv.ParseInt with base 0
            val := x.Value
            // Strip underscores for readability separators
            val = strings.ReplaceAll(val, "_", "")
            n, err := strconv.ParseInt(val, 0, 64)
            if err != nil {
                return nil
            }
            return ir.NewInt(pos, n)
        }
        return nil
    case *syntax.Name:
        if x.Value == "true" {
            return ir.NewBool(pos, true)
        }
        if x.Value == "false" {
            return ir.NewBool(pos, false)
        }
        // Local package const?
        if n := resolveLocalConst(x.Value); n != nil {
            return n
        }
        return nil
    case *syntax.ParenExpr:
        return decoratorConstArg(pos, x.X, imports)
    case *syntax.Operation:
        if x.Y == nil {
            // Unary
            if v, ok := evalConstInt64(x, imports); ok {
                return ir.NewInt(pos, v)
            }
            return nil
        }
        if v, ok := evalConstInt64(x, imports); ok {
            return ir.NewInt(pos, v)
        }
        return nil
    case *syntax.SelectorExpr:
        // Imported constant selector: alias.Const
        if pkgName, ok := x.X.(*syntax.Name); ok {
            if imports != nil {
                if path, ok := imports[pkgName.Value]; ok {
                    return resolveImportedConst(pos, path, x.Sel.Value)
                }
            }
        }
        return nil
    case *syntax.CompositeLit:
        // Composite literal of constants: require resolvable type
        typ := resolveTypeFromSyntax(x.Type, imports)
        if typ == nil {
            return nil
        }
        // Elements
        var list ir.Nodes
        isStruct := typ.Kind() == types.TSTRUCT
        for _, el := range x.ElemList {
            switch kv := el.(type) {
            case *syntax.KeyValueExpr:
                if isStruct {
                    // Struct keyed element: field name or embedded type: value
                    var fld *types.Field
                    switch key := kv.Key.(type) {
                    case *syntax.Name:
                        fld = findStructField(typ, key.Value)
                    case *syntax.SelectorExpr:
                        if alias, ok := key.X.(*syntax.Name); ok {
                            if imports != nil {
                                if path, ok := imports[alias.Value]; ok {
                                    fld = findEmbeddedFieldBySelector(typ, path, key.Sel.Value)
                                }
                            }
                        }
                    }
                    if fld == nil {
                        return nil
                    }
                    val := decoratorConstArg(pos, kv.Value, imports)
                    if val == nil {
                        return nil
                    }
                    list = append(list, ir.NewStructKeyExpr(pos, fld, val))
                    break
                }
                // Non-struct keyed literal (array/map): key and value must be const-evaluable
                key := decoratorConstArg(pos, kv.Key, imports)
                val := decoratorConstArg(pos, kv.Value, imports)
                if key == nil || val == nil {
                    return nil
                }
                list = append(list, ir.NewKeyExpr(pos, key, val))
            default:
                val := decoratorConstArg(pos, el, imports)
                if val == nil {
                    return nil
                }
                list = append(list, val)
            }
        }
        return ir.NewCompLitExpr(pos, ir.OCOMPLIT, typ, list)
    case *syntax.CallExpr:
        // Typed conversion of constant: Type(const)
        toType := resolveTypeFromSyntax(x.Fun, imports)
        if toType == nil || len(x.ArgList) != 1 {
            return nil
        }
        arg := decoratorConstArg(pos, x.ArgList[0], imports)
        if arg == nil {
            return nil
        }
            return typecheck.Expr(ir.NewConvExpr(pos, ir.OCONV, toType, arg))
    default:
        return nil
    }
}

// resolveImportedFunc locates an imported function by package path and name,
// returning an ir.Node suitable as a call callee. It uses export data if needed.
func resolveImportedFunc(pkgPath, name string) ir.Node {
    // Try to find an existing ir.Name for the function.
    if pkg := types.PkgMap()[pkgPath]; pkg != nil {
        if sym := pkg.Lookup(name); sym != nil {
            if def, ok := sym.Def.(*ir.Name); ok {
                return def
            }
        }
    }
    // Fallback: ask the unified linker to read the function body/signature.
    full := objabi.PathToPrefix(pkgPath) + "." + name
    if fn, err := LookupFunc(full); err == nil && fn != nil && fn.Nname != nil {
        return fn.Nname
    }
    return nil
}

// resolveImportedConst returns an ir.Node representing a referenced
// imported constant (as a name node with value), if available.
func resolveImportedConst(pos src.XPos, alias, name string) ir.Node {
    // Alias is used in source, but we need package path; we cannot recover it here.
    // Callers must use imports map to compute full path. This helper assumes alias is actually a path.
    // In our call sites, we pass alias from imports map value instead of alias.
    pkgPath := alias
    if pkg := types.PkgMap()[pkgPath]; pkg != nil {
        if sym := pkg.Lookup(name); sym != nil {
            if def, ok := sym.Def.(*ir.Name); ok {
                if def.Op() == ir.OLITERAL {
                    return def
                }
            }
        }
    }
    // If not yet loaded, try to force importing the package constant by referencing it in a synthetic way.
    // There is no direct helper for constants like LookupFunc; without it, we cannot force load here.
    // Fallback: return nil; callers may bail or require richer const eval in writer.
    return nil
}

// resolveLocalConst looks up a const in the local package by name.
func resolveLocalConst(name string) ir.Node {
    sym := typecheck.Lookup(name)
    if n, ok := sym.Def.(*ir.Name); ok && n.Op() == ir.OLITERAL {
        return n
    }
    return nil
}

// evalConstInt64 evaluates a constant int64 expression for simple unary/binary ops.
func evalConstInt64(e *syntax.Operation, imports map[string]string) (int64, bool) {
    // helper to extract int64 from syntax.Expr
    var val func(syntax.Expr) (int64, bool)
    val = func(ex syntax.Expr) (int64, bool) {
        switch t := ex.(type) {
        case *syntax.BasicLit:
            if t.Kind == syntax.IntLit {
                s := strings.ReplaceAll(t.Value, "_", "")
                n, err := strconv.ParseInt(s, 0, 64)
                if err == nil {
                    return n, true
                }
            }
            return 0, false
        case *syntax.Name:
            if t.Value == "true" {
                return 1, true
            }
            if t.Value == "false" {
                return 0, true
            }
            if n := resolveLocalConst(t.Value); n != nil {
                if iv, ok := constant.Int64Val(n.(*ir.Name).Val()); ok {
                    return iv, true
                }
                if uv, ok := constant.Uint64Val(n.(*ir.Name).Val()); ok {
                    return int64(uv), true
                }
            }
            return 0, false
        case *syntax.SelectorExpr:
            if alias, ok := t.X.(*syntax.Name); ok {
                if imports != nil {
                    if path, ok := imports[alias.Value]; ok {
                        if n := resolveImportedConst(src.NoXPos, path, t.Sel.Value); n != nil {
                            if iv, ok := constant.Int64Val(n.(*ir.Name).Val()); ok {
                                return iv, true
                            }
                            if uv, ok := constant.Uint64Val(n.(*ir.Name).Val()); ok {
                                return int64(uv), true
                            }
                        }
                    }
                }
            }
            return 0, false
        case *syntax.ParenExpr:
            return val(t.X)
        case *syntax.Operation:
            if t.Y == nil {
                // unary
                if v, ok := val(t.X); ok {
                    switch t.Op {
                    case syntax.Add:
                        return +v, true
                    case syntax.Sub:
                        return -v, true
                    case syntax.Xor:
                        return ^v, true
                    }
                }
                return 0, false
            }
            // binary
            lv, ok1 := val(t.X)
            rv, ok2 := val(t.Y)
            if !ok1 || !ok2 {
                return 0, false
            }
            switch t.Op {
            case syntax.Add:
                return lv + rv, true
            case syntax.Sub:
                return lv - rv, true
            case syntax.Mul:
                return lv * rv, true
            case syntax.Div:
                if rv == 0 {
                    return 0, false
                }
                return lv / rv, true
            case syntax.Rem:
                if rv == 0 {
                    return 0, false
                }
                return lv % rv, true
            case syntax.Shl:
                if rv < 0 || rv > 63 {
                    return 0, false
                }
                return lv << uint64(rv), true
            case syntax.Shr:
                if rv < 0 || rv > 63 {
                    return 0, false
                }
                return lv >> uint64(rv), true
            case syntax.And:
                return lv & rv, true
            case syntax.Or:
                return lv | rv, true
            case syntax.Xor:
                return lv ^ rv, true
            case syntax.AndAnd, syntax.OrOr, syntax.Eql, syntax.Neq, syntax.Lss, syntax.Leq, syntax.Gtr, syntax.Geq:
                // not supported in const args for MVP
                return 0, false
            }
            return 0, false
        default:
            return 0, false
        }
    }

    return val(e)
}

// resolveTypeFromSyntax attempts to resolve a type from syntax using
// the local package scope and imports map.
func resolveTypeFromSyntax(t syntax.Expr, imports map[string]string) *types.Type {
    switch tt := t.(type) {
    case *syntax.Name:
        if bt := resolveBasicType(tt.Value); bt != nil {
            return bt
        }
        if sym := typecheck.Lookup(tt.Value); sym.Def != nil {
            if n, ok := sym.Def.(*ir.Name); ok && n.Op() == ir.OTYPE {
                return n.Type()
            }
        }
    case *syntax.SelectorExpr:
        if alias, ok := tt.X.(*syntax.Name); ok {
            if path := imports[alias.Value]; path != "" {
                if pkg := types.PkgMap()[path]; pkg != nil {
                    if sym := pkg.Lookup(tt.Sel.Value); sym != nil {
                        if n, ok := sym.Def.(*ir.Name); ok && n.Op() == ir.OTYPE {
                            return n.Type()
                        }
                    }
                }
            }
        }
    case *syntax.SliceType:
        if elem := resolveTypeFromSyntax(tt.Elem, imports); elem != nil {
            return types.NewSlice(elem)
        }
    case *syntax.ArrayType:
        // Array length must be constant integer
        if tt.Len == nil {
            return nil
        }
        // Only support integer literal lengths or simple const expr
        switch ln := tt.Len.(type) {
        case *syntax.BasicLit:
            if ln.Kind == syntax.IntLit {
                s := strings.ReplaceAll(ln.Value, "_", "")
                n, err := strconv.ParseInt(s, 0, 64)
                if err == nil {
                    if elem := resolveTypeFromSyntax(tt.Elem, imports); elem != nil {
                        return types.NewArray(elem, n)
                    }
                }
            }
        case *syntax.Operation:
            if v, ok := evalConstInt64(ln, imports); ok {
                if elem := resolveTypeFromSyntax(tt.Elem, imports); elem != nil {
                    return types.NewArray(elem, v)
                }
            }
        }
    case *syntax.MapType:
        key := resolveTypeFromSyntax(tt.Key, imports)
        val := resolveTypeFromSyntax(tt.Value, imports)
        if key != nil && val != nil {
            return types.NewMap(key, val)
        }
    }
    return nil
}

// resolveBasicType maps builtin type names to types.Type.
func resolveBasicType(name string) *types.Type {
    switch name {
    case "bool":
        return types.Types[types.TBOOL]
    case "string":
        return types.Types[types.TSTRING]
    case "int":
        return types.Types[types.TINT]
    case "int8":
        return types.Types[types.TINT8]
    case "int16":
        return types.Types[types.TINT16]
    case "int32", "rune":
        return types.Types[types.TINT32]
    case "int64":
        return types.Types[types.TINT64]
    case "uint":
        return types.Types[types.TUINT]
    case "uint8", "byte":
        return types.Types[types.TUINT8]
    case "uint16":
        return types.Types[types.TUINT16]
    case "uint32":
        return types.Types[types.TUINT32]
    case "uint64":
        return types.Types[types.TUINT64]
    case "uintptr":
        return types.Types[types.TUINTPTR]
    case "float32":
        return types.Types[types.TFLOAT32]
    case "float64":
        return types.Types[types.TFLOAT64]
    case "complex64":
        return types.Types[types.TCOMPLEX64]
    case "complex128":
        return types.Types[types.TCOMPLEX128]
    }
    return nil
}

// findStructField searches typ (which must be a struct or named struct type)
// for a field with the given name and returns the *types.Field if found.
func findStructField(typ *types.Type, name string) *types.Field {
    if typ.Kind() != types.TSTRUCT {
        return nil
    }
    n := typ.NumFields()
    for i := 0; i < n; i++ {
        if typ.Field(i).Sym != nil && typ.Field(i).Sym.Name == name {
            return typ.Field(i)
        }
    }
    return nil
}

// findEmbeddedFieldBySelector locates an embedded field by matching the
// underlying named type's package path and name (for selector keys like pkg.T).
func findEmbeddedFieldBySelector(typ *types.Type, pkgPath, name string) *types.Field {
    if typ.Kind() != types.TSTRUCT {
        return nil
    }
    n := typ.NumFields()
    for i := 0; i < n; i++ {
        f := typ.Field(i)
        // Unwrap pointer embeddings.
        ft := f.Type
        if ft.IsPtr() {
            ft = ft.Elem()
        }
        if ft.Sym() == nil || ft.Sym().Name != name {
            continue
        }
        // Compare package path of the named type.
        // If the type was defined in package path pkgPath, match.
        if ft.Sym().Pkg != nil && ft.Sym().Pkg.Path == pkgPath {
            return f
        }
    }
    return nil
}

// readBodies iteratively expands all pending dictionaries and
// function bodies.
//
// If duringInlining is true, then the inline.InlineDecls is called as
// necessary on instantiations of imported generic functions, so their
// inlining costs can be computed.
func readBodies(target *ir.Package, duringInlining bool) {
	var inlDecls []*ir.Func

	// Don't use range--bodyIdx can add closures to todoBodies.
	for {
		// The order we expand dictionaries and bodies doesn't matter, so
		// pop from the end to reduce todoBodies reallocations if it grows
		// further.
		//
		// However, we do at least need to flush any pending dictionaries
		// before reading bodies, because bodies might reference the
		// dictionaries.

		if len(todoDicts) > 0 {
			fn := todoDicts[len(todoDicts)-1]
			todoDicts = todoDicts[:len(todoDicts)-1]
			fn()
			continue
		}

		if len(todoBodies) > 0 {
			fn := todoBodies[len(todoBodies)-1]
			todoBodies = todoBodies[:len(todoBodies)-1]

			pri, ok := bodyReader[fn]
			assert(ok)
			pri.funcBody(fn)

			// Instantiated generic function: add to Decls for typechecking
			// and compilation.
			if fn.OClosure == nil && len(pri.dict.targs) != 0 {
				// cmd/link does not support a type symbol referencing a method symbol
				// across DSO boundary, so force re-compiling methods on a generic type
				// even it was seen from imported package in linkshared mode, see #58966.
				canSkipNonGenericMethod := !(base.Ctxt.Flag_linkshared && ir.IsMethod(fn))
				if duringInlining && canSkipNonGenericMethod {
					inlDecls = append(inlDecls, fn)
				} else {
					target.Funcs = append(target.Funcs, fn)
				}
			}

			continue
		}

		break
	}

	todoDicts = nil
	todoBodies = nil

	if len(inlDecls) != 0 {
		// If we instantiated any generic functions during inlining, we need
		// to call CanInline on them so they'll be transitively inlined
		// correctly (#56280).
		//
		// We know these functions were already compiled in an imported
		// package though, so we don't need to actually apply InlineCalls or
		// save the function bodies any further than this.
		//
		// We can also lower the -m flag to 0, to suppress duplicate "can
		// inline" diagnostics reported against the imported package. Again,
		// we already reported those diagnostics in the original package, so
		// it's pointless repeating them here.

		oldLowerM := base.Flag.LowerM
		base.Flag.LowerM = 0
		inline.CanInlineFuncs(inlDecls, nil)
		base.Flag.LowerM = oldLowerM

		for _, fn := range inlDecls {
			fn.Body = nil // free memory
		}
	}
}

// writePkgStub type checks the given parsed source files,
// writes an export data package stub representing them,
// and returns the result.
func writePkgStub(m posMap, noders []*noder) string {
	pkg, info, otherInfo := checkFiles(m, noders)

	pw := newPkgWriter(m, pkg, info, otherInfo)

	pw.collectDecls(noders)

	publicRootWriter := pw.newWriter(pkgbits.SectionMeta, pkgbits.SyncPublic)
	privateRootWriter := pw.newWriter(pkgbits.SectionMeta, pkgbits.SyncPrivate)

	assert(publicRootWriter.Idx == pkgbits.PublicRootIdx)
	assert(privateRootWriter.Idx == pkgbits.PrivateRootIdx)

	{
		w := publicRootWriter
		w.pkg(pkg)

		if w.Version().Has(pkgbits.HasInit) {
			w.Bool(false)
		}

		scope := pkg.Scope()
		names := scope.Names()
		w.Len(len(names))
		for _, name := range names {
			w.obj(scope.Lookup(name), nil)
		}

		w.Sync(pkgbits.SyncEOF)
		w.Flush()
	}

	{
		w := privateRootWriter
		w.pkgInit(noders)
		w.Flush()
	}

	var sb strings.Builder
	pw.DumpTo(&sb)

	// At this point, we're done with types2. Make sure the package is
	// garbage collected.
	freePackage(pkg)

	return sb.String()
}

// freePackage ensures the given package is garbage collected.
func freePackage(pkg *types2.Package) {
	// The GC test below relies on a precise GC that runs finalizers as
	// soon as objects are unreachable. Our implementation provides
	// this, but other/older implementations may not (e.g., Go 1.4 does
	// not because of #22350). To avoid imposing unnecessary
	// restrictions on the GOROOT_BOOTSTRAP toolchain, we skip the test
	// during bootstrapping.
	if base.CompilerBootstrap || base.Debug.GCCheck == 0 {
		*pkg = types2.Package{}
		return
	}

	// Set a finalizer on pkg so we can detect if/when it's collected.
	done := make(chan struct{})
	runtime.SetFinalizer(pkg, func(*types2.Package) { close(done) })

	// Important: objects involved in cycles are not finalized, so zero
	// out pkg to break its cycles and allow the finalizer to run.
	*pkg = types2.Package{}

	// It typically takes just 1 or 2 cycles to release pkg, but it
	// doesn't hurt to try a few more times.
	for i := 0; i < 10; i++ {
		select {
		case <-done:
			return
		default:
			runtime.GC()
		}
	}

	base.Fatalf("package never finalized")
}

// readPackage reads package export data from pr to populate
// importpkg.
//
// localStub indicates whether pr is reading the stub export data for
// the local package, as opposed to relocated export data for an
// import.
func readPackage(pr *pkgReader, importpkg *types.Pkg, localStub bool) {
	{
		r := pr.newReader(pkgbits.SectionMeta, pkgbits.PublicRootIdx, pkgbits.SyncPublic)

		pkg := r.pkg()
		// This error can happen if "go tool compile" is called with wrong "-p" flag, see issue #54542.
		if pkg != importpkg {
			base.ErrorfAt(base.AutogeneratedPos, errors.BadImportPath, "mismatched import path, have %q (%p), want %q (%p)", pkg.Path, pkg, importpkg.Path, importpkg)
			base.ErrorExit()
		}

		if r.Version().Has(pkgbits.HasInit) {
			r.Bool()
		}

		for i, n := 0, r.Len(); i < n; i++ {
			r.Sync(pkgbits.SyncObject)
			if r.Version().Has(pkgbits.DerivedFuncInstance) {
				assert(!r.Bool())
			}
			idx := r.Reloc(pkgbits.SectionObj)
			assert(r.Len() == 0)

			path, name, code := r.p.PeekObj(idx)
			if code != pkgbits.ObjStub {
				objReader[types.NewPkg(path, "").Lookup(name)] = pkgReaderIndex{pr, idx, nil, nil, nil}
			}
		}

		r.Sync(pkgbits.SyncEOF)
	}

	if !localStub {
		r := pr.newReader(pkgbits.SectionMeta, pkgbits.PrivateRootIdx, pkgbits.SyncPrivate)

		if r.Bool() {
			sym := importpkg.Lookup(".inittask")
			task := ir.NewNameAt(src.NoXPos, sym, nil)
			task.Class = ir.PEXTERN
			sym.Def = task
		}

		for i, n := 0, r.Len(); i < n; i++ {
			path := r.String()
			name := r.String()
			idx := r.Reloc(pkgbits.SectionBody)

			sym := types.NewPkg(path, "").Lookup(name)
			if _, ok := importBodyReader[sym]; !ok {
				importBodyReader[sym] = pkgReaderIndex{pr, idx, nil, nil, nil}
			}
		}

		r.Sync(pkgbits.SyncEOF)
	}
}

// writeUnifiedExport writes to `out` the finalized, self-contained
// Unified IR export data file for the current compilation unit.
func writeUnifiedExport(out io.Writer) {
	// Use V2 as the encoded version for aliastypeparams.
	version := pkgbits.V2
	l := linker{
		pw: pkgbits.NewPkgEncoder(version, base.Debug.SyncFrames),

		pkgs:   make(map[string]index),
		decls:  make(map[*types.Sym]index),
		bodies: make(map[*types.Sym]index),
	}

	publicRootWriter := l.pw.NewEncoder(pkgbits.SectionMeta, pkgbits.SyncPublic)
	privateRootWriter := l.pw.NewEncoder(pkgbits.SectionMeta, pkgbits.SyncPrivate)
	assert(publicRootWriter.Idx == pkgbits.PublicRootIdx)
	assert(privateRootWriter.Idx == pkgbits.PrivateRootIdx)

	var selfPkgIdx index

	{
		pr := localPkgReader
		r := pr.NewDecoder(pkgbits.SectionMeta, pkgbits.PublicRootIdx, pkgbits.SyncPublic)

		r.Sync(pkgbits.SyncPkg)
		selfPkgIdx = l.relocIdx(pr, pkgbits.SectionPkg, r.Reloc(pkgbits.SectionPkg))

		if r.Version().Has(pkgbits.HasInit) {
			r.Bool()
		}

		for i, n := 0, r.Len(); i < n; i++ {
			r.Sync(pkgbits.SyncObject)
			if r.Version().Has(pkgbits.DerivedFuncInstance) {
				assert(!r.Bool())
			}
			idx := r.Reloc(pkgbits.SectionObj)
			assert(r.Len() == 0)

			xpath, xname, xtag := pr.PeekObj(idx)
			assert(xpath == pr.PkgPath())
			assert(xtag != pkgbits.ObjStub)

			if types.IsExported(xname) {
				l.relocIdx(pr, pkgbits.SectionObj, idx)
			}
		}

		r.Sync(pkgbits.SyncEOF)
	}

	{
		var idxs []index
		for _, idx := range l.decls {
			idxs = append(idxs, idx)
		}
		slices.Sort(idxs)

		w := publicRootWriter

		w.Sync(pkgbits.SyncPkg)
		w.Reloc(pkgbits.SectionPkg, selfPkgIdx)

		if w.Version().Has(pkgbits.HasInit) {
			w.Bool(false)
		}

		w.Len(len(idxs))
		for _, idx := range idxs {
			w.Sync(pkgbits.SyncObject)
			if w.Version().Has(pkgbits.DerivedFuncInstance) {
				w.Bool(false)
			}
			w.Reloc(pkgbits.SectionObj, idx)
			w.Len(0)
		}

		w.Sync(pkgbits.SyncEOF)
		w.Flush()
	}

	{
		type symIdx struct {
			sym *types.Sym
			idx index
		}
		var bodies []symIdx
		for sym, idx := range l.bodies {
			bodies = append(bodies, symIdx{sym, idx})
		}
		slices.SortFunc(bodies, func(a, b symIdx) int { return cmp.Compare(a.idx, b.idx) })

		w := privateRootWriter

		w.Bool(typecheck.Lookup(".inittask").Def != nil)

		w.Len(len(bodies))
		for _, body := range bodies {
			w.String(body.sym.Pkg.Path)
			w.String(body.sym.Name)
			w.Reloc(pkgbits.SectionBody, body.idx)
		}

		w.Sync(pkgbits.SyncEOF)
		w.Flush()
	}

	base.Ctxt.Fingerprint = l.pw.DumpTo(out)
}
// checkDecoratorSignature enforces that callee has type func(S) S for S equal to funType.
// It emits precise diagnostics if the shape doesn't match.
func checkDecoratorSignature(owner *ir.Func, pos src.XPos, callee ir.Node, funType *types.Type) bool {
    t := callee.Type()
    if t == nil || t.Kind() != types.TFUNC {
        base.ErrorfAt(pos, 0, "decorator does not produce a function; got %v", t)
        return false
    }
    if t.NumParams() != 1 || t.NumResults() != 1 {
        base.ErrorfAt(pos, 0, "decorator must have type func(%v) %v; got %v", funType, funType, t)
        return false
    }
    p := t.Param(0).Type
    r := t.Result(0).Type
    if !types.IdenticalStrict(p, funType) || !types.IdenticalStrict(r, funType) {
        base.ErrorfAt(pos, 0, "decorator type mismatch: expected func(%v) %v; got %v", funType, funType, t)
        return false
    }
    return true
}
