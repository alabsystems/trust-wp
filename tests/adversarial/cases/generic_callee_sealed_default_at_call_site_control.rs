//@ expect: verify
//@ mechanism: control for the generic-callee cases: `g<T: Tr1>` claims `result == x.m()` with Tr1's
//@ mechanism: SEALED default (10), which every `T` takes, so `g` verifies at the abstract `T`. At the
//@ mechanism: call `g(s)` the marker is re-resolved among Tr1's definitions at `S`: its default, not
//@ mechanism: `<S as Tr2>::m` (0), and `caller` claims 10.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `caller FAILED ✗ (postcondition)` with D-196 in force,
//@ teeth: `caller verified ✓` with D-197). The isolating twin of
//@ teeth: generic_callee_sealed_default_reresolved_to_other_trait_granted.rs.
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

#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
