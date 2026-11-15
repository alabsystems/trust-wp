//@ expect: reject
//@ mechanism: after a loop that never writes `i`, `need7(i); i = 0; need7(i)`. The post-loop call
//@ mechanism: lane names both calls' argument by the bare user variable `i`, which the assignment
//@ mechanism: between them does not reach, so the second call's precondition is discharged with
//@ mechanism: the exit value 7, as the first call's rightly is.
//@ accept-means: a callee's precondition after a loop was discharged with the value a local held
//@ accept-means: before a later assignment. Concretely: `go()`'s second call is `need7(0)`.
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
    need7(i);
    i = 0;
    need7(i);
}
