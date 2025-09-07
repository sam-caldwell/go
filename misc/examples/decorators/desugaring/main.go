package main

import (
    "fmt"
)

// This example demonstrates the effect of stacked decorators by
// using manual wrappers equivalent to the proposed desugaring.

// Original body (would be f$orig in the compiler lowering)
func Work$orig(x int) int {
    fmt.Println("orig")
    return x + 1
}

// Decorator functions (hand-written), signature-preserving
func log(next func(int) int) func(int) int {
    return func(x int) int {
        fmt.Println("log: before")
        r := next(x)
        fmt.Println("log: after")
        return r
    }
}

func twice(next func(int) int) func(int) int {
    return func(x int) int {
        fmt.Println("twice")
        return next(next(x))
    }
}

// Wrapper with original exported name, composes bottom→top
// Proposed source equivalent:
// @log
// @twice
// func Work(x int) int { return x + 1 }
func Work(x int) int {
    w := log(twice(Work$orig))
    return w(x)
}

func main() {
    fmt.Println("res:", Work(1))
}

