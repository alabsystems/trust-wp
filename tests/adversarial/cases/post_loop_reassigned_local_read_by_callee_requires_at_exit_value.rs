//@ expect: reject
//@ mechanism: `i` is declared before a loop that never writes it, and assigned `i = 0` after the
//@ mechanism: loop, right before `need7(i)`. The post-loop call lane names the argument by the bare
//@ mechanism: user variable `i` (the pinning post_loop_callee_requires_control.rs records) and the
//@ mechanism: post-loop assignment does not reach that name, so `i` keeps the value the state at
//@ mechanism: the loop's exit gives it, 7, and the precondition `k == 7u32` is discharged. Passing
//@ mechanism: a copy (`let k = i; need7(k)`) is refuted, and so is the same assignment with no loop
//@ mechanism: before it.
//@ accept-means: a callee's precondition after a loop was discharged with the value a local held
//@ accept-means: before a later assignment. Concretely: `go()` calls `need7(0)`.
//@ also-verified: need7
//@ fixed-by: D-235 (`PastLoopNames`): code after a loop reads a local by its loop-exit
//@ fixed-by: name only where nothing changed it since the exit, or fails closed.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-235's post-loop rule disabled;
//@ teeth: `unknown` with D-235 (the call fails closed).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 7u32)]
pub fn need7(k: u32) {}

pub fn go() {
    let mut n = 0u32;
    let mut i = 7u32;
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
    i = 0;
    need7(i);
}
