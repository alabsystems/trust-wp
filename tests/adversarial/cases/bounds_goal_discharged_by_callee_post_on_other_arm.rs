//@ expect: reject
//@ mechanism: a callee postcondition assumed while walking ONE arm of a switch (`in_range(a, i)` on the
//@ mechanism: `flag` arm, `ensures(i@ < a@.len())`) was a premise of every goal of the function, the bounds
//@ mechanism: check of `a[i]` on the path that skips the call included. `in_range` diverges when `i` is out
//@ mechanism: of range, so its postcondition is true, but it says nothing about an execution that never
//@ mechanism: calls it. Each premise an arm records is now `edge ==> premise` (`guard_branch_assumptions`).
//@ accept-means: an index that is out of range on the path that skips the call is verified, and the crate
//@ accept-means: exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(&[], 0, false)` panics at `a[i]`.
//@ teeth: ACCEPTED before D-169; rejected with it.
//@ also-verified: in_range
//@ fixed-by: D-169 (a premise recorded on a switch arm is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(i@ < a@.len())]
pub fn in_range(a: &[u32], i: usize) {
    #[invariant(true)]
    while i >= a.len() {}
}

#[ensures(true)]
pub fn f(a: &[u32], i: usize, flag: bool) -> u32 {
    if flag {
        in_range(a, i);
    }
    a[i]
}
