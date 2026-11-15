//@ expect: reject
//@ mechanism: the block-slice walker (`collect_call_effects_for_blocks`) recorded both arms' callee postconditions,
//@ mechanism: `x@ < 50` from `below50` and `x@ < 100` from `below`, as premises of every goal of the function VC, so the
//@ mechanism: stronger one proved a postcondition only the arm calling `below50` establishes. The two-call spelling of
//@ mechanism: loop_invariant_fn_callee_post_on_other_arm_discharges_ensures.rs, found probing sideways from D-243.
//@ accept-means: a postcondition only one arm establishes is verified on both, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(70, false)` returns with `x == 70`.
//@ also-verified: below, below50
//@ fixed-by: D-243: each premise of the walker is stated under a formula that holds only where its block runs.
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(x@ < 50)]
pub fn below50(x: u32) {
    #[invariant(true)]
    while x >= 50 {}
}

#[ensures(x@ < 50)]
pub fn f(x: u32, flag: bool) {
    if flag {
        below50(x);
    } else {
        below(x);
    }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
