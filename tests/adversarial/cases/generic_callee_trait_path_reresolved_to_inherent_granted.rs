//@ expect: reject
//@ mechanism: generic_callee_method_call_reresolved_to_other_trait_granted.rs spelled `Tr1::m(x)` in the
//@ mechanism: callee's contract, and the competing definition an INHERENT logic `m` of `S` (0): the
//@ mechanism: call site re-resolves the marker over the whole family at `S` and takes the inherent
//@ mechanism: method, where Rust's `<S as Tr1>::m` is Tr1's default (10).
//@ fixed-by: D-197 — a generic marker carries the bound trait whose method the call is, and a call
//@ fixed-by: site re-resolves it among that trait's definitions at the call's type: its impl, or its
//@ fixed-by: default body there (`identity_typed::instantiate_generic_markers`).
//@ accept-means: `caller` claims `result == 0` and returns 10; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` with D-196 in force.
//@ teeth: With D-197: `caller FAILED ✗ (postcondition)`.
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

impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 0u32 }
    }
}

#[ensures(result == Tr1::m(x))]
pub fn g<T: Tr1>(x: T) -> u32 {
    let _ = x;
    10
}

#[ensures(result == 0u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
