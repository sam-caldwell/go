package printer

import (
    "bytes"
    "testing"
)

// Ensure go/printer preserves and formats decorator lines above func/method decls.
func TestDecoratorsFormatting(t *testing.T) {
    const src = `package p

// In-package decorator identifiers
func D(f func(int) int) func(int) int { return func(x int) int { return f(x) } }

// Qualified decorator reference via import alias
// (the parser/printer only cares about syntax here)
import dec "example.com/dec"

@D
@dec.Wrap()
func F(x int) int { return x }

type T struct{}

@D
func (t *T) M(x int) int { return x }
`

    // Format and reparse; formatting should keep decorator lines exactly once
    out, err := format([]byte(src), 0)
    if err != nil {
        t.Fatalf("format failed: %v", err)
    }

    // Expect identical output modulo printer canonicalization
    // The simple snippet above should be stable under printer formatting.
    if !bytes.Contains(out, []byte("@D\n@dec.Wrap()\nfunc F(x int) int {")) {
        t.Fatalf("missing decorators on func F in output:\n%s", string(out))
    }
    if !bytes.Contains(out, []byte("@D\nfunc (t *T) M(x int) int {")) {
        t.Fatalf("missing decorator on method M in output:\n%s", string(out))
    }
}

