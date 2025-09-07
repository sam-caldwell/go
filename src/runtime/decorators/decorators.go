// Package decorators provides optional metadata for decorated functions.
//
// Registration is driven by the compiler: decorated wrappers call Register
// on first invocation (or on every invocation in this MVP) to record their
// applied decorators. List can then retrieve the recorded metadata.
package decorators

import (
    "reflect"
    "sync"
)

// Info describes a single applied decorator.
type Info struct {
    // Name is the pretty-printed decorator expression, e.g., "D" or "pkg.D(123)".
    Name string
    // Args (optional) may list pretty-printed arguments if available.
    Args []string
}

var reg sync.Map // key uintptr (func entry) -> []string pretty forms

// Register records metadata for fn. The info slice contains pretty-printed
// decorator expressions (closest last). It is intended for compiler use.
//
// It returns the zero value to allow patterns like:
//   var _ = decorators.Register(f, []string{"D", "pkg.Dec(1)"})
// or to be called in a wrapper body without assigning the result.
func Register(fn any, info []string) struct{} {
    p := reflect.ValueOf(fn).Pointer()
    // We store the most recent info, avoiding repeated re-allocation.
    reg.Store(p, info)
    return struct{}{}
}

// List returns applied decorator metadata for fn, or nil if none recorded.
func List(fn any) []Info {
    p := reflect.ValueOf(fn).Pointer()
    if v, ok := reg.Load(p); ok {
        ss := v.([]string)
        out := make([]Info, len(ss))
        for i, s := range ss {
            out[i] = Info{Name: s}
        }
        return out
    }
    return nil
}

