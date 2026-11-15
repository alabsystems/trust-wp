//@ expect: reject
//@ mechanism: an inner loop's post-loop return walk left through the outer loop's header and re-ran
//@ mechanism: the outer body as straight-line code, so its last assignment of `k` was the outer
//@ mechanism: body's `k = 0`, and the function's return value was `0`. Which loop's walk the fold
//@ mechanism: used depended on the order loop detection returned the loops in.
//@ accept-means: `f()` returns 5, so `ensures(result == 0u32)` is FALSE, and trust-wp proved it.
//@ fixed-by: D-165 (the post-loop return walk is path-sensitive); this branch's own walk (D-223), dropped at the merge with D-165, closed it first
//@ teeth: ACCEPTED at exit 0 in most runs before D-223, when this case was committed RED;
//@ teeth: the other runs used the outer loop's walk and refuted it.
//@ verdict: failed
//@ fn-failed: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn f() -> u32 {
    let mut k: u32 = 0;
    let mut i: u32 = 0;
    #[invariant(i <= 1u32)]
    #[invariant(i == 0u32 || k == 5u32)]
    while i < 1 {
        k = 0;
        #[invariant(true)]
        while k != 0 {}
        k = 5;
        i += 1;
    }
    k
}
