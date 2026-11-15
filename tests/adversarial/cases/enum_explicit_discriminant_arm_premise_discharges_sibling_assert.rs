//@ expect: reject
//@ mechanism: an enum match's arm premises are scoped to the arm's edge (D-169), spelled over the switch's
//@ mechanism: VALUES, which here are the declared discriminants (`A = 1`, `B = 0`) in the opposite order
//@ mechanism: to the variants. `below(x)` runs on `A`; the `assert!(x < 100)` on `B` must not read its
//@ mechanism: postcondition. An edge spelled over variant indices would hand `A`'s premise to `B`.
//@ accept-means: a body that panics on the `B` arm is verified against its contract, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, E::B)` panics, and a function with a contract must not panic.
//@ teeth: ACCEPTED at the campaign tip, where the arm's premise is unscoped; rejected with D-169.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && result == x)]
pub fn below(x: u32) -> u32 {
    #[invariant(true)]
    while x >= 100 {}
    x
}

pub enum E {
    A = 1,
    B = 0,
}

#[requires(true)]
pub fn f(x: u32, e: E) {
    match e {
        E::A => { below(x); }
        E::B => { assert!(x < 100); }
    }
}
