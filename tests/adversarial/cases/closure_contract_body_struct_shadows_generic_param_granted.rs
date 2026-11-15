//@ expect: reject
//@ also-verified: f
//@ mechanism: a closure's contract inside `f<W: Tr>`, whose body declares a struct `W`, calls
//@ mechanism: `W::k()`. A closure's clauses are resolved inside the enclosing body, where the body's
//@ mechanism: struct shadows `f`'s generic parameter, so Rust reads the struct's inherent `k` (0). The
//@ mechanism: resolver walks from the closure's generics to `f`'s, finds the parameter `W`, reads
//@ mechanism: Tr's declaration (10), and the closure, which returns 10, is credited. `f` claims
//@ mechanism: nothing, so its credit is true.
//@ fixed-by: D-198 — a generic parameter's name is read as the parameter only where no block
//@ fixed-by: between the clause and the item that declares it binds the name
//@ fixed-by: (`identity::visible_generic_type_param`, `block_scope::lookup_within`); otherwise the
//@ fixed-by: scope lookup reads it, or it is refused.
//@ accept-means: the closure claims `result@ == W::k()` with Rust's `W` the body's struct (0) and
//@ accept-means: returns 10; ACCEPTED means its credit is printed.
//@ teeth: MEASURED: `f::{closure#1} verified ✓` with D-197 in force (`f` refused: its call of the
//@ teeth: closure reads the marker the closure's contract left).
//@ teeth: With D-198: `f::{closure#1} FAILED ✗ (postcondition)`, `f verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result == 10)]
    fn k() -> Int;
}

pub fn f<W: Tr>() -> u32 {
    struct W;
    impl W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    let c = #[ensures(result@ == W::k())]
    || -> u32 { 10 };
    c()
}
