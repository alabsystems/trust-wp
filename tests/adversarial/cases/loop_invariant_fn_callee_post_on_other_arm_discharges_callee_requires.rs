//@ expect: reject
//@ mechanism: before the loop, `if flag { below(x) }` then `need_small(x)`: the block-slice walker recorded
//@ mechanism: `below`'s postcondition as a premise of every goal, and the precondition of the later call, owed on both
//@ mechanism: paths, was discharged by it. The callee-requires spelling of
//@ mechanism: loop_invariant_fn_callee_post_on_other_arm_discharges_panic_goal.rs, found probing sideways from D-243.
//@ accept-means: a precondition owed on the path that skips the call establishing it is discharged, and the crate
//@ accept-means: exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` calls `need_small(200)`.
//@ also-verified: below, need_small
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

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

pub fn f(x: u32, flag: bool) {
    if flag {
        below(x);
    }
    need_small(x);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
