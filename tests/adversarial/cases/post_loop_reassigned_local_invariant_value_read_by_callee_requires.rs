//@ expect: reject
//@ mechanism: the loop writes `i = 7` and its invariant states `i == 7u32`; after the loop
//@ mechanism: `i = 0; need7(i)`. The post-loop call lane names the argument by the bare user
//@ mechanism: variable `i`, which the loop's exit state binds to the invariant's value, and the
//@ mechanism: post-loop assignment does not reach that name, so `k == 7u32` is discharged.
//@ accept-means: a callee's precondition after a loop was discharged with the value the loop's
//@ accept-means: invariant gives a local the code after the loop overwrote. Concretely: `go()`
//@ accept-means: calls `need7(0)`.
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
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    while n < 3 {
        i = 7;
        n += 1;
    }
    i = 0;
    need7(i);
}
