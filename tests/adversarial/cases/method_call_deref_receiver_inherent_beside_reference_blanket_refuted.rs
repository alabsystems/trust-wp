//@ expect: reject
//@ mechanism: the refuted twin of method_call_deref_receiver_inherent_beside_reference_blanket_control.rs:
//@ mechanism: without `requires(b)`, `(*a).invariant(b)` (`A::invariant`, which is `b`) can be false.
//@ fixed-by: n/a (twin; refused before D-201, refuted with it)
//@ accept-means: `f` claims `b` for every `b` and the crate exits 0.
//@ teeth: MEASURED: `f FAILED ✗ (postcondition)` with D-201.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A {}
impl A {
    #[logic(open)]
    pub fn invariant(self, b: bool) -> bool {
        pearlite! { b }
    }
}

#[ensures((*a).invariant(b))]
pub fn f(a: &mut A, b: bool) {}
