//@ expect: verify
//@ mechanism: control: `f` returns 10, which is `Tr1::m(s)`, the trait's default body. The isolating twin
//@ mechanism: of trait_path_call_read_as_inherent_method_granted.rs (one literal differs).
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` before D-196 and
//@ teeth: `f verified ✓` with it)
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
    10
}
