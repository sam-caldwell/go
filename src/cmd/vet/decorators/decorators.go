package decorators

import (
    "go/ast"
    "go/token"
    "go/types"

    "golang.org/x/tools/go/analysis"
    "golang.org/x/tools/go/analysis/passes/inspect"
    "golang.org/x/tools/go/ast/inspector"
)

// Analyzer reports basic issues with decorator usage.
//
// Currently, it flags obviously non-constant decorator arguments, such as
// direct function calls or references to non-const identifiers inside
// @D(...). This is a conservative lint and may produce false negatives; it
// does not attempt full compile-time evaluation.
var Analyzer = &analysis.Analyzer{
    Name: "decorators",
    Doc:  "reports basic decorator issues (e.g., non-constant arguments)",
    Run:  run,
    Requires: []*analysis.Analyzer{
        inspect.Analyzer,
    },
}

func run(pass *analysis.Pass) (interface{}, error) {
    insp := pass.ResultOf[inspect.Analyzer].(*inspector.Inspector)
    nodeFilter := []ast.Node{(*ast.FuncDecl)(nil)}
    insp.Preorder(nodeFilter, func(n ast.Node) {
        fd := n.(*ast.FuncDecl)
        if len(fd.Decorators) == 0 {
            return
        }
        for _, dec := range fd.Decorators {
            if call, ok := dec.(*ast.CallExpr); ok {
                for _, arg := range call.Args {
                    if definitelyNonConst(pass, arg) {
                        pass.Reportf(arg.Pos(), "decorator argument may not be compile-time constant")
                    }
                }
            }
        }
    })
    return nil, nil
}

// definitelyNonConst reports true if e definitely contains non-constant
// computation (e.g., function call) or references a non-const identifier.
// It is conservative and may return false for complex constant expressions.
func definitelyNonConst(pass *analysis.Pass, e ast.Expr) bool {
    switch x := e.(type) {
    case *ast.BasicLit:
        return false
    case *ast.Ident:
        if obj, ok := pass.TypesInfo.Uses[x]; ok {
            _, isConst := obj.(*types.Const)
            return !isConst
        }
        return true
    case *ast.SelectorExpr:
        // Allow pkg.CONST
        if id, ok := x.X.(*ast.Ident); ok {
            if _, ok := pass.TypesInfo.Uses[id].(*types.PkgName); ok {
                if _, ok := pass.TypesInfo.Uses[x.Sel].(*types.Const); ok {
                    return false
                }
            }
        }
        // Otherwise, conservatively flag as non-const.
        return true
    case *ast.ParenExpr:
        return definitelyNonConst(pass, x.X)
    case *ast.UnaryExpr:
        return definitelyNonConst(pass, x.X)
    case *ast.BinaryExpr:
        // Non-const if either side is non-const.
        return definitelyNonConst(pass, x.X) || definitelyNonConst(pass, x.Y)
    case *ast.CompositeLit:
        // Composite literals of constants are accepted by the compiler in this fork,
        // but go/types can't express them as constants; avoid warning to reduce FPs.
        return false
    case *ast.CallExpr:
        return true
    default:
        // Be conservative for any other expression kinds.
        return true
    }
}

