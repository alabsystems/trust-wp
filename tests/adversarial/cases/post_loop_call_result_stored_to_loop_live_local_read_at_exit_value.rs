//@ expect: reject
//@ mechanism: `k` is 7 before and through the loop (the invariant states `k == 7u32`), and after
//@ mechanism: the loop `k = zero(); need7(k)`. The post-loop call lane names the call's result by
//@ mechanism: the bare user variable `k`, the same name the loop's exit state binds to 7, so the
//@ mechanism: argument of `need7` is read at the exit value and `zero`'s postcondition is stated
//@ mechanism: about that same name.
//@ accept-means: a callee's precondition after a loop was discharged with the value a local held
//@ accept-means: before a call's result was stored to it. Concretely: `go()` calls `need7(0)`.
//@ also-verified: need7, zero
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

#[ensures(result == 0u32)]
pub fn zero() -> u32 {
    0
}

pub fn go() {
    let mut n = 0u32;
    let mut k = 7u32;
    #[invariant(k == 7u32)]
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
    k = zero();
    need7(k);
}
