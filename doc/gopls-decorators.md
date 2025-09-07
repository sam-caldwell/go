gopls Support for Decorators (@)

Overview

This fork adds first‑class syntax for Python‑style decorators in the stdlib:

- Scanner: `@` tokenized as `_At` (see cmd/compile/internal/syntax/scanner.go).
- Parser (stdlib): `go/parser` accepts `@` lines immediately above the next `func` and attaches them to `ast.FuncDecl.Decorators []ast.Expr`.
- Printer: `go/printer` preserves and formats decorator lines.

These surfaces are sufficient for gopls to provide:

- Syntax highlighting for `@` lines and decorator expressions
- Completion after `@` for in‑scope identifiers, and after `@pkg.` to complete exported names from `pkg`
- Hover/signature help to show the resolved type of a decorator expression

Implementation Notes (gopls/x/tools)

1) Parser and AST

- Build gopls against this fork so it picks up the new `go/scanner`, `go/parser`, and `go/ast` changes. In particular:
  - `ast.FuncDecl.Decorators []ast.Expr` carries the parsed decorator expressions.
  - The `@` token appears in the file token stream, but gopls should rely on AST for structure.

2) Highlighting

- Treat each `decor` in `FuncDecl.Decorators` as an expression context:
  - `@ident` → highlight `@` as punctuation/operator and `ident` as identifier
  - `@pkg.Sel` → highlight `pkg` as package and `Sel` as selector
  - `@D(args…)` → standard call highlighting (parentheses, commas, literals)

3) Completion

- Trigger completion after `@` at the start of a decorator line:
  - Offer in‑scope identifiers of function type or parameterless generic decorators `D[S funcsig]`.
  - Offer imported package names.

- Trigger completion after `@pkg.`:
  - Offer exported function names from `pkg`.

- Trigger completion within `@D(` and after commas inside the arg list using existing expression completion logic; arguments are ordinary constant expressions.

4) Hover / Signature Help

- Reuse existing hover/signature help on the `ast.Expr` nodes in `FuncDecl.Decorators`.
- When available, display resolved type as `Decorator[S]` or `func(S) S` (both are valid in this fork).

5) Formatting / Edits

- `go/printer` already preserves and formats decorator lines; gopls can delegate formatting to `go/format`.

6) Edge cases / Guards

- Only treat contiguous `@` lines immediately above a `func` as decorators. This is already enforced by the stdlib parser.
- Do not suggest completions in comment contexts; rely on AST and positions to avoid false positives.

Test Plan

- Parse and index files that contain:
  - `@D` and `@pkg.D` stacked above a non‑method function and a method
  - Parameterized decorators `@D(123, "x")` (const args)
  - Generic decorators `@Identity` where `Identity[S funcsig]`

- Verify:
  - Completion list after `@` contains in‑scope decorator identifiers and package names
  - Completion list after `@pkg.` contains exported names from the package
  - Hover on `D` shows `func(S) S` or `Decorator[S]`
  - Formatting preserves `@` lines; positions map correctly for diagnostics

References

- Parser: src/go/parser/parser.go (funcDecl + decorator collection)
- AST: src/go/ast/ast.go (FuncDecl.Decorators)
- Printer: src/go/printer/nodes.go (decorator emission)

