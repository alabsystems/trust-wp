//@ expect: reject
//@ mechanism: `i` is 7 before a loop whose body sets `i = 0`, and `need7(i)` follows the loop. The
//@ mechanism: block-slice walker that states the call obligations outside the loops binds `i` to 7
//@ mechanism: in its entry walk, which cannot pass the loop, and resolved the copy of `i` the call is
//@ mechanism: handed after the loop through that binding, so the precondition read `7 == 7`
//@ mechanism: whatever the loop did.
//@ accept-means: a callee's precondition after a loop was discharged with the value a local held
//@ accept-means: before the loop overwrote it. Concretely: `go()` calls `need7(0)`.
//@ also-verified: need7
//@ fixed-by: D-235 (`PastLoopNames`): code after a loop reads a local by its loop-exit
//@ fixed-by: name only where nothing changed it since the exit, or fails closed.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-235's post-loop rule disabled;
//@ teeth: `failed` with D-235: the call reads `i` at its loop-exit name, which the loop writes and
//@ teeth: no invariant states, and the precondition is refuted.
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
        i = 0;
        n += 1;
    }
    need7(i);
}
