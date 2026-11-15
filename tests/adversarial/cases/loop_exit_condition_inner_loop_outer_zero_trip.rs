//@ expect: reject
//@ mechanism: a loop's negated condition is a premise at the return only when every path from entry
//@ mechanism: to a return passes through that loop (D-224). The inner loop runs only when the outer loop
//@ mechanism: runs, so with `n == 0` the return never saw `!(j < 3u32)`.
//@ accept-means: `f(0)` returns 0, so `result >= 3u32` is FALSE, and trust-wp proved it.
//@ verdict: failed
//@ fn-failed: f
//@ teeth: ACCEPTED at exit 0 on a build whose several-loop exit condition (D-224) skips both
//@ teeth: the every-return test and the rewritten-name filter; `failed` with them.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result >= 3u32)]
pub fn f(n: u32) -> u32 {
    let mut j: u32 = 0;
    let mut i: u32 = 0;
    #[invariant(i <= n)]
    while i < n {
        #[invariant(j <= 3u32)]
        while j < 3 { j += 1; }
        i += 1;
    }
    j
}
