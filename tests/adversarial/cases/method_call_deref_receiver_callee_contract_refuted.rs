//@ expect: reject
//@ also-verified: g
//@ mechanism: the refuted twin of method_call_deref_receiver_callee_contract_control.rs: `caller` claims
//@ mechanism: `result == !b` of `g(a, b)`, whose contract says `result == b`.
//@ fixed-by: n/a (twin; refused before D-201, refuted with it)
//@ accept-means: `caller` claims `result == !b`, returns `b`, and the crate exits 0.
//@ teeth: MEASURED: `caller FAILED ✗ (postcondition)` with D-201.
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

#[ensures(result == (*a).invariant(b))]
pub fn g(a: &mut A, b: bool) -> bool {
    let _ = a;
    b
}

#[ensures(result == !b)]
pub fn caller(a: &mut A, b: bool) -> bool {
    g(a, b)
}
