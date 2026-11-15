//@ expect: reject
//@ mechanism: `<S as Tr1>::m(s)` is Tr1's default body (10): `impl Tr1 for S` does not override it.
//@ mechanism: `resolve_qualified` looks only for an impl member of Tr1 for `S`, finds none and leaves
//@ mechanism: the call unresolved; the encoder then dispatches the colliding name on the receiver's
//@ mechanism: sort to the only member defined for `S`, the inherent `m` (0), and `f`, which
//@ mechanism: returns 0, is credited.
//@ fixed-by: D-196 — `Tr::m(x)` and `<S as Tr>::m(x)` are read among Tr's own definitions: its impl
//@ fixed-by: for the type, or its default body there (`resolve_on_trait_path`, `resolve_qualified`).
//@ accept-means: `f` claims `result == <S as Tr1>::m(s)` (10), returns 0, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `f FAILED ✗ (postcondition)`: the default is read at `S`.
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

#[ensures(result == <S as Tr1>::m(s))]
pub fn f(s: S) -> u32 {
    0
}
