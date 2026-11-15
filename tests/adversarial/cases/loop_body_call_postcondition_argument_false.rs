//@ expect: reject
//@ mechanism: reject twin of loop_body_call_postcondition_argument_control: the call reads `i`
//@ mechanism: BEFORE `i += 1`, so its postcondition says only `x > i - 1` of the new `i`. A clause
//@ mechanism: stated at the post-iteration value of its argument would prove `x > i`.
//@ accept-means: with `above` returning `k + 1`, `go(1)` ends its first iteration with `x == 1` and
//@ accept-means: `i == 1`, so `x > i` is FALSE, and trust-wp proved the invariant preserved.
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: above
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k < 1000u32)]
#[ensures(result > k)]
pub fn above(k: u32) -> u32 { k + 1 }

#[requires(n < 1000u32)]
pub fn go(n: u32) {
    let mut i: u32 = 0;
    let mut x: u32 = 1;
    #[invariant(i <= n)]
    #[invariant(x > i)]
    while i < n {
        x = above(i);
        i += 1;
    }
}
