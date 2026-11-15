//@ expect: reject
//@ also-verified: g
//@ mechanism: the one-literal twin of generic_callee_sealed_default_at_call_site_control.rs: `g<T: Tr1>`
//@ mechanism: claims `result == x.m()` with Tr1's SEALED default (10) and verifies at the abstract `T`,
//@ mechanism: a true credit. At the call `g(s)` Rust's `<S as Tr1>::m` is that default, but the call
//@ mechanism: site re-resolves the generic marker over the whole family `m` at `S` and takes
//@ mechanism: `<S as Tr2>::m` (0): `caller`, which returns 10, is credited with `result == 0` and
//@ mechanism: the crate exits 0.
//@ fixed-by: D-197 — a generic marker carries the bound trait whose method the call is, and a call
//@ fixed-by: site re-resolves it among that trait's definitions at the call's type: its impl, or its
//@ fixed-by: default body there (`identity_typed::instantiate_generic_markers`).
//@ accept-means: `caller` claims `result == 0`, returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`caller verified ✓`) with D-196 in force.
//@ teeth: With D-197: `caller FAILED ✗ (postcondition)`; the twin verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1: Sized {
    #[logic(open, sealed)]
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
