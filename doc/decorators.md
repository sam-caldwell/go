# Decorators (Draft Feature Overview)

This fork proposes Python-style `@decorator` syntax for Go functions and methods.
This page gives a short, practical overview with examples and links to the full spec.

- Syntax: `@name` or `@name(args...)` lines stacked immediately above `func`.
- Order: bottom-to-top (closest to the function applies first).
- Semantics: compiles to a wrapper around the original body (desugaring).
- Types: decorators are signature-preserving; see the spec for `Decorator[S]` and shape-lambdas.

See SPECIFICATION-decorators.md for details.

## Quick Examples

Proposed source (illustrative):

```go
@log
@retry(tries=3)
func Work(x int) error { /* body */ }
```

Equivalent desugaring today (manual wrapper) for illustration:

```go
// f$orig holds the original body.
var Work$orig = func(x int) error { /* body */ }

// Work forwards through composed decorators bottom→top.
func Work(x int) error {
    // compose: retry then log
    w := log(retry(3)(Work$orig))
    return w(x)
}
```

A method remains in the method set and continues to satisfy interfaces because the wrapper keeps the original method
name and type:

```go
type S struct{}

// Proposed
// @trace
// func (s *S) Do(x int) string { /* body */ }

// Desugared (illustrative)
func (s *S) Do$orig(x int) string { /* body */ }
func (s *S) Do(x int) string {
    w := trace((s).Do$orig) // receiver-lifted
    return w(s, x)
}
```

For more background, constraints, and compiler details, read SPECIFICATION-decorators.md.

## Disabling Decoration

To opt out of decorator processing for a specific function or method, place the pragma on a blank line immediately above it:

```go
//go:nodecorate
func F() { /* decorators, if present above, are ignored for this function */ }
```

This is useful for bisecting, debugging, or temporarily bypassing decoration. The pragma applies only to the function it precedes.

To disable decoration globally for a build, pass the compiler flag via go build or go run:

```
go build -gcflags=all=-decorators=off ./...
```

Use `on` to force-enable if needed (the default is enabled): `-gcflags=all=-decorators=on`.
