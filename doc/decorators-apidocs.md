# Decorators in API Docs (Concept Preview)

This page illustrates how exported decorators would appear in rendered API documentation (e.g., `go doc`/godoc style). It serves as a reference for documentation writers and users while the tooling support lands.

## Package Example

Given a package with a decorated exported function and method:

```go
package calc

// @log
// @retry(tries=3, initial=50*time.Millisecond)
func Add(x, y int) int { return x + y }

// @trace
func (c *Counter) Inc(delta int) int { c.n += delta; return c.n }
```

Rendered API docs should surface decorators directly above the declaration they apply to, preserving bottom→top order and formatting similar to source:

```
PACKAGE DOCUMENTATION

package calc // import "example.org/calc"

Decorators:
  - Decorators appear above functions and methods in the order written
    in source, bottom-to-top. Parameterized decorator arguments are
    shown verbatim.

FUNCTIONS

@retry(tries=3, initial=50*time.Millisecond)
@log
func Add(x, y int) int

METHODS

@trace
func (*Counter) Inc(delta int) int
```

Notes:
- The `@` lines are part of the rendered documentation, not comments.
- Stacked decorators keep alignment; long argument lists may wrap similarly to function signatures.
- Links: Qualified decorators (e.g., `@pkg.Decorator`) link to their definitions, just like identifiers in signatures.

## Rationale

- Discoverability: Seeing decorators in docs communicates important behavior modifiers (e.g., logging, retries) at a glance.
- Consistency: Mirrors the proposed source syntax and compiler model; no hidden behavior.
- Minimalism: Keeps output compact by placing decorators with their targets rather than in a separate section.

For details on semantics, typing, and desugaring, see SPECIFICATION-decorators.md and doc/decorators.md.

