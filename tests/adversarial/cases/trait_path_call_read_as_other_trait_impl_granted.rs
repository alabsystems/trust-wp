//@ expect: reject
//@ mechanism: trait_path_call_read_as_inherent_method_granted.rs with the competing definition an impl
//@ mechanism: of ANOTHER trait: `Tr1::m(s)` is Tr1's default body (10), and the resolver picks the
//@ mechanism: only impl member for `S`, `<S as Tr2>::m` (0).
//@ fixed-by: D-196 — `Tr::m(x)` and `<S as Tr>::m(x)` are read among Tr's own definitions: its impl
//@ fixed-by: for the type, or its default body there (`resolve_on_trait_path`, `resolve_qualified`).
//@ accept-means: `f` claims `result == Tr1::m(s)` (10), returns 0, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `f FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1 {
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

#[ensures(result == Tr1::m(s))]
pub fn f(s: S) -> u32 {
    0
}
