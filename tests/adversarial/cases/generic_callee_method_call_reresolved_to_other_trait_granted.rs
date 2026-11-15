//@ expect: reject
//@ mechanism: a generic callee's contract `result == x.m()` with `T: Tr1`: Rust reads `x.m()` as
//@ mechanism: `<T as Tr1>::m`, the bound trait's method, and at `T = S` that is Tr1's default body
//@ mechanism: (10). The callee-text resolver spells a generic receiver with a generic MARKER that
//@ mechanism: each call site re-resolves at the call's type argument, and the re-resolution searches
//@ mechanism: the whole family `m` at `S`, not Tr1's: it takes the only impl member defined for `S`,
//@ mechanism: `<S as Tr2>::m` (0). `caller`, which returns `g(s)` (10 by `g`'s contract), is
//@ mechanism: credited with `result == 0`. `g` returns 10, which no `T` whose impl overrides `m`
//@ mechanism: satisfies, so it is refuted and the per-function gate is what reports the caller.
//@ fixed-by: D-197 — a generic marker carries the bound trait whose method the call is, and a call
//@ fixed-by: site re-resolves it among that trait's definitions at the call's type: its impl, or its
//@ fixed-by: default body there (`identity_typed::instantiate_generic_markers`).
//@ accept-means: `caller` claims `result == 0` and returns 10; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` with D-196 in force.
//@ teeth: With D-197: `caller FAILED ✗ (postcondition)`: the call site reads Tr1's default (10).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1: Sized {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}
impl Tr1 for S {}

pub trait Tr2 {
    #[logic]
    fn m(self) -> u32;
}
impl Tr2 for S {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 0u32 }
    }
}

#[ensures(result == x.m())]
pub fn g<T: Tr1>(x: T) -> u32 {
    let _ = x;
    10
}

#[ensures(result == 0u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
