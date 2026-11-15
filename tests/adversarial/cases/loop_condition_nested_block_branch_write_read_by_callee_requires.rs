//@ expect: reject
//@ mechanism: the block condition `{ { { if n == 3 { i = 0 } } } n < 3 }` nests its branch in
//@ mechanism: blocks before the switch that leaves the loop, and the branch writes `i` on the pass
//@ mechanism: that leaves. The first switch after the header is that branch, which has no exit
//@ mechanism: arm, so `loop_exit_edge` resolves no exit edge and D-229's `loop_condition_exit_write`
//@ mechanism: reports no write. The loop lane takes `n < 3` from the real exit switch and reads the
//@ mechanism: exit at the header state, where the invariant `i == 7u32` holds, so the post-loop
//@ mechanism: call's precondition is discharged with `i == 7`.
//@ accept-means: a callee's precondition after a loop was discharged with the header value of a
//@ accept-means: local the condition overwrote on the pass that left. Concretely: `go()` calls
//@ accept-means: `need7(0)`.
//@ also-verified: need7
//@ fixed-by: D-234 (`loop_lane_exit`): the refusals read the exit switch the loop lane
//@ fixed-by: takes its condition from, so the write on the pass that leaves is seen.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-234's lane exit disabled; `unknown`
//@ teeth: with D-234 (the loop call-obligation groups fail closed).
//@ teeth: loop_condition_branch_write_before_exit_divides_after.rs is the spelling without the
//@ teeth: nested blocks.
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
    while { { { if n == 3 { i = 0 } } } n < 3 } {
        i = 7;
        n += 1;
    }
    need7(i);
}
