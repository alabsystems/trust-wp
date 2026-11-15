//@ expect: reject
//@ mechanism: after a loop that never writes `i` (7), `i = 0; let k = id(i); need7(k)`. The
//@ mechanism: post-loop call lane names `id`'s argument by the bare user variable `i`, which the
//@ mechanism: post-loop assignment does not reach, so `id`'s postcondition `result == x` is
//@ mechanism: stated as `k == 7` and discharges `need7(k)`. The defect is in the premise the
//@ mechanism: lane takes from the first call, not in the second call's own argument.
//@ accept-means: a callee's postcondition after a loop was assumed about the value its argument
//@ accept-means: held before a later assignment. Concretely: `go()` calls `need7(0)`.
//@ also-verified: need7, id
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

#[ensures(result == x)]
pub fn id(x: u32) -> u32 {
    x
}

pub fn go() {
    let mut n = 0u32;
    let mut i = 7u32;
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
    i = 0;
    let k = id(i);
    need7(k);
}
