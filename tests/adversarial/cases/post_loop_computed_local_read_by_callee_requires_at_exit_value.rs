//@ expect: reject
//@ mechanism: `i` is declared before a loop that never writes it, and assigned `i = n - 3` after
//@ mechanism: the loop, right before `need7(i)`. The post-loop call lane names the argument by the
//@ mechanism: bare user variable `i`, which the post-loop assignment does not reach, so `i` keeps
//@ mechanism: the value the state at the loop's exit gives it, 7, and the precondition `k == 7u32`
//@ mechanism: is discharged.
//@ accept-means: a callee's precondition after a loop was discharged with the value a local held
//@ accept-means: before a later assignment. Concretely: `go()` calls `need7(0)`.
//@ also-verified: need7
//@ fixed-by: D-235 (`PastLoopNames`): code after a loop reads a local by its loop-exit
//@ fixed-by: name only where nothing changed it since the exit, or fails closed.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-235's post-loop rule disabled;
//@ teeth: `unknown` with D-235 (the call fails closed).
//@ teeth: post_loop_reassigned_local_read_by_callee_requires_at_exit_value.rs assigns a constant.
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
    i = n - 3;
    need7(i);
}
