//@ expect: reject
//@ mechanism: a `loop` whose exit is `if n >= 3 { break }`, preceded by `i = 0` and, before that,
//@ mechanism: an unrelated branch `if n == 100 { m = 1 }`. The first switch after the header is
//@ mechanism: that branch, which has no exit arm, so `loop_exit_edge` resolves no exit edge and
//@ mechanism: D-229's `loop_condition_exit_write` reports no write; the loop lane takes the break
//@ mechanism: switch as the loop's condition and reads the exit at the header state, where the
//@ mechanism: invariant `i == 7u32` holds. Without the leading branch the same loop is refused
//@ mechanism: by D-229's marker.
//@ accept-means: a callee's precondition after a loop was discharged with the header value of a
//@ accept-means: local the pass that broke out overwrote. Concretely: `go()` calls `need7(0)`.
//@ also-verified: need7
//@ fixed-by: D-234 (`loop_lane_exit`): the refusals read the exit switch the loop lane
//@ fixed-by: takes its condition from, so the write on the pass that leaves is seen.
//@ teeth: ACCEPTED at exit 0 at the wp-campaign tip and with D-234's lane exit disabled; `unknown`
//@ teeth: with D-234 (the loop call-obligation groups fail closed). The spelling without
//@ teeth: `if n == 100 { m = 1; }` is `unknown` with D-229 alone.
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
    let mut m = 0u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    loop {
        if n == 100 {
            m = 1;
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
