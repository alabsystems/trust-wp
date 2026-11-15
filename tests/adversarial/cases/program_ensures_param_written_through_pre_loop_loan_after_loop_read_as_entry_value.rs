//@ expect: reject
//@ mechanism: a program function borrows its `mut` parameter `y` mutably, runs an annotated loop, writes its input `x` through the borrow and returns `y`, claiming `result == 0` under `requires(y == 0)`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, forgets a local at a loan made after the loop, but a loan made before it is still live after it, and a write through that loan names the loan, never the local, so `y` is read as its entry value, which the precondition fixes at `0`.
//@ fixed-by: D-165
//@ accept-means: a function that returns its input `x` is credited with a postcondition saying it returns `0`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 0, 1)` returns `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with the datatype binding fixed: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (incomplete loop: no single post-loop return value)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(y == 0u32)]
#[ensures(result == 0u32)]
pub fn prog(n: u32, mut y: u32, x: u32) -> u32 {
    let r = &mut y;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    *r = x;
    y
}
