//@ expect: reject
//@ mechanism: after the loop, `if c { below(x) }` then `need_small(x)`: the block-slice walker recorded `below`'s
//@ mechanism: postcondition as a premise of the goals after the loop unguarded, and the later precondition, owed on
//@ mechanism: both paths, was discharged by it. The post-loop spelling of
//@ mechanism: loop_invariant_fn_callee_post_on_other_arm_discharges_callee_requires.rs.
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

pub fn f(x: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    if c {
        below(x);
    }
    need_small(x);
}
