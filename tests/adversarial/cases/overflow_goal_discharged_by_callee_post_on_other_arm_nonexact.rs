//@ expect: reject
//@ mechanism: a callee postcondition assumed while walking ONE arm of a switch (`below(x)` on the `flag`
//@ mechanism: arm) was a premise of every goal of the function. Here the write through `a` makes the primary
//@ mechanism: walk's arithmetic inexact (`primary_arithmetic_is_exact`), so the `x + 1` goal is owed by
//@ mechanism: the region walk and the premise reached it from the other arm. Each premise an arm records is
//@ mechanism: now `edge ==> premise` (`guard_branch_assumptions`). The exact-arithmetic spelling is
//@ mechanism: overflow_goal_discharged_by_callee_post_on_other_arm.rs.
//@ accept-means: an addition that overflows on the path that skips the call is verified, and the crate
//@ accept-means: exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(u32::MAX, &mut 0, false)` overflows.
//@ teeth: ACCEPTED before D-169; rejected with it.
//@ also-verified: below
//@ fixed-by: D-169 (a premise recorded on a switch arm is scoped to that arm's edge).
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

#[ensures(true)]
pub fn f(x: u32, a: &mut u32, flag: bool) -> u32 {
    *a = 0;
    if flag {
        below(x);
    }
    x + 1
}
