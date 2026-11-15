//@ expect: reject
//@ mechanism: the block condition `{ if n == 3 { i = 0 } n < 3 }` branches before the switch that
//@ mechanism: leaves the loop, and its branch writes `i` on the pass that leaves. The first switch
//@ mechanism: after the header is that inner branch, which has no exit arm, so `loop_exit_edge`
//@ mechanism: resolves no exit edge and D-229's `loop_condition_exit_write` reports no write. The
//@ mechanism: loop lane takes `n < 3` from the real exit switch (`find_body_break_condition`) and
//@ mechanism: reads the exit at the header state, where the invariant `i == 7u32` holds, so the
//@ mechanism: post-loop division's divisor is read as 7.
//@ accept-means: the exit-pass write D-229 refuses for a straight-line condition is read at the
//@ accept-means: header state when the condition branches first. Concretely: `go()` divides 100
//@ accept-means: by 0 and panics; the panic-freedom obligation was discharged.
//@ fixed-by: D-234 (`loop_lane_exit`): the refusals read the exit switch the loop lane
//@ fixed-by: takes its condition from, so the write on the pass that leaves is seen.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-234's lane exit disabled; `unknown`
//@ teeth: with D-234 (the loop call-obligation groups fail closed).
//@ teeth: loop_condition_block_write_before_exit_read_after.rs is the straight-line spelling D-229
//@ teeth: refuses.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn go() -> u32 {
    let mut n = 0u32;
    let mut i = 7u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    while { if n == 3 { i = 0 } n < 3 } {
        i = 7;
        n += 1;
    }
    100 / i
}
