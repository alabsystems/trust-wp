//@ expect: reject
//@ mechanism: the loop lane's function-level continuation replaces the function's result with the
//@ mechanism: value the walk from the loop's exit states, on every path: the early return of the
//@ mechanism: parameter `n` before the loop was discarded for the loop path's constant.
//@ accept-means: `f(11)` returns 11, so `ensures(result == 0u32)` is FALSE, and trust-wp proved it.
//@ fixed-by: D-224 (a loop's exit facts and exit value are the function's only when every return passes through it)
//@ teeth: ACCEPTED at exit 0 with D-223 in force and D-224 open, when this case was committed RED.
//@ teeth: ACCEPTED at exit 0 at the campaign tip, whose post-loop walk (D-165) states the loop path's
//@ teeth: value for every return; `failed` on this branch while the primary walk's merged result stood in
//@ teeth: for a loop no return passes through. Since the merge with D-165, D-224 gives the loop no exit
//@ teeth: value, so `result` is unbound and the rejection is `f`'s own withheld line.
//@ verdict: unknown
//@ refused-with: f unknown (incomplete loop: no single post-loop return value)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn f(n: u32) -> u32 {
    if n > 10 {
        return n;
    }
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    0
}
