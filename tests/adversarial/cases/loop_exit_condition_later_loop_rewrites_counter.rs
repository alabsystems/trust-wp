//@ expect: reject
//@ mechanism: a function with several loops assumes, at its return, the negated condition of each
//@ mechanism: loop every return passes through (D-224), unless a block reachable from that loop's
//@ mechanism: exit rewrites a name the condition reads. Here the second loop's body resets the first
//@ mechanism: loop's counter, so `!(i < 10u32)` holds at the first loop's exit and not at the return.
//@ accept-means: `f()` returns 0 (the second loop sets `i = 0`), so `result >= 10u32` is FALSE,
//@ accept-means: and trust-wp proved it.
//@ verdict: failed
//@ fn-failed: f
//@ teeth: ACCEPTED at exit 0 on a build whose several-loop exit condition (D-224) skips both
//@ teeth: the every-return test and the rewritten-name filter; `failed` with them.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result >= 10u32)]
pub fn f() -> u32 {
    let mut i: u32 = 0;
    #[invariant(i <= 10u32)]
    while i < 10 { i += 1; }
    let mut j: u32 = 0;
    #[invariant(j <= 5u32)]
    while j < 5 { j += 1; i = 0; }
    i
}
