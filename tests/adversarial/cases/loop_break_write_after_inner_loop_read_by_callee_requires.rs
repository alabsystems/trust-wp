//@ expect: reject
//@ mechanism: a `loop` whose exit is `if n >= 3 { break }`, preceded by `i = 0` and, before that,
//@ mechanism: an inner `while k < 2` loop. The first switch after the outer header is the inner
//@ mechanism: loop's, which has no arm leaving the outer loop, so `loop_exit_edge` resolves no
//@ mechanism: exit edge and D-229's `loop_condition_exit_write` reports no write; the outer loop
//@ mechanism: lane takes the break switch as its condition and reads the exit at the header state,
//@ mechanism: where the invariant `i == 7u32` holds.
//@ accept-means: a callee's precondition after a loop was discharged with the header value of a
//@ accept-means: local the pass that broke out overwrote. Concretely: `go()` calls `need7(0)`.
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
    let mut k = 0u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    loop {
        #[invariant(true)]
        while k < 2 {
            k += 1;
        }
        i = 0;
        if n >= 3 {
            break;
        }
        i = 7;
        n += 1;
    }
    need7(i);
}
