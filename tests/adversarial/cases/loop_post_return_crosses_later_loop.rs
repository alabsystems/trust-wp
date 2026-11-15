//@ expect: reject
//@ mechanism: the first loop's post-loop return walk crossed the second loop's blocks as straight-line
//@ mechanism: code, applying `k = 0` before it and never the second loop's `k = 7` it had already
//@ mechanism: visited, so the first loop's return value was `0`. The fold over loops kept the last
//@ mechanism: loop's value only when it had one.
//@ accept-means: `f(0)` returns 7, so `ensures(result == 0u32)` is FALSE, and trust-wp proved it.
//@ fixed-by: D-165 (the post-loop return walk is path-sensitive); this branch's own walk (D-223), dropped at the merge with D-165, closed it first
//@ teeth: ACCEPTED at exit 0 before D-223, when this case was committed RED.
//@ verdict: failed
//@ fn-failed: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn f(n: u32) -> u32 {
    let mut k: u32 = 0;
    let mut i: u32 = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    k = 0;
    let mut j: u32 = 0;
    #[invariant(true)]
    loop {
        if j >= 3 {
            break;
        }
        k = 7;
        j += 1;
    }
    k
}
