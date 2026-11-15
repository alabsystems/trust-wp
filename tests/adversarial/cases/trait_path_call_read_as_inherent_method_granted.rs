//@ expect: reject
//@ mechanism: `Tr1::m(s)` names the trait: Rust calls `<S as Tr1>::m`, which `S` inherits from the
//@ mechanism: trait's default body (10). `S` also has an inherent logic `m` (0). The resolver
//@ mechanism: resolves the path's trait (`PathTarget::Trait`) and then picks the family member on
//@ mechanism: `s`'s type without asking which trait it belongs to: the only impl member for `S` is
//@ mechanism: the inherent one, so `f`, which returns 0, is credited against a contract whose
//@ mechanism: `Tr1::m(s)` Rust evaluates to 10.
//@ fixed-by: D-196 — `Tr::m(x)` and `<S as Tr>::m(x)` are read among Tr's own definitions: its impl
//@ fixed-by: for the type, or its default body there (`resolve_on_trait_path`, `resolve_qualified`).
//@ accept-means: `f` claims `result == Tr1::m(s)` (10), returns 0, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `f FAILED ✗ (postcondition)`: `Tr1::m(s)` is read as Tr1's default (10).
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

impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 0u32 }
    }
}

#[ensures(result == Tr1::m(s))]
pub fn f(s: S) -> u32 {
    0
}
