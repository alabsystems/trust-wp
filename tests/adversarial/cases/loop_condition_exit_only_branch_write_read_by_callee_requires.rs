//@ expect: reject
//@ mechanism: the block condition `{ let b = n < 3; if !b { i = 0 } b }` writes `i` only on the
//@ mechanism: pass that leaves the loop, inside a branch before the exit switch. The first switch
//@ mechanism: after the header is that branch, which has no exit arm, so `loop_exit_edge` resolves
//@ mechanism: no exit edge and D-229's `loop_condition_exit_write` reports no write. The loop lane
//@ mechanism: takes `n < 3` from the real exit switch and reads the exit at the header state,
//@ mechanism: where the invariant `i == 7u32` holds, so the post-loop call's precondition is
//@ mechanism: discharged with `i == 7`.
//@ accept-means: a callee's precondition after a loop was discharged with the header value of a
//@ accept-means: local the condition overwrote on the pass that left. Concretely: `go()` calls
//@ accept-means: `need7(0)`.
//@ also-verified: need7
//@ fixed-by: D-234 (`loop_lane_exit`): the refusals read the exit switch the loop lane
//@ fixed-by: takes its condition from, so the write on the pass that leaves is seen.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-234's lane exit disabled; `unknown`
//@ teeth: with D-234 (the loop call-obligation groups fail closed).
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
    while { let b = n < 3; if !b { i = 0 } b } {
        i = 7;
        n += 1;
    }
    need7(i);
}
