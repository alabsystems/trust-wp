//@ expect: reject
//@ mechanism: the condition's call writes `b`, a variable declared before the loop: `while { b =
//@ mechanism: lt3(n); b }`. At every header `b` holds the previous evaluation's `true`, so
//@ mechanism: `#[invariant(b)]` is TRUE; at the exit the call has just stored `false`. The exit and
//@ mechanism: continuation read `b` at the header state.
//@ accept-means: the loop lane proved a postcondition over the header value of a variable the
//@ accept-means: condition's call overwrote before the loop left. Concretely: `go()` returns
//@ accept-means: `lt3(3)`, which is false.
//@ also-verified: lt3
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: ACCEPTED at exit 0 on this branch's merge of the campaign without D-229, with D-222 in
//@ teeth: force; `unknown` with D-229 (the `loop-condition-exit-write` marker). Refuted `failed`
//@ teeth: before D-222, when the condition read the call's destination as a free placeholder.
//@ teeth: loop_condition_block_destination_read_after.rs is the same write with no call.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 3u32))]
pub fn lt3(k: u32) -> bool { k < 3 }

#[ensures(result)]
pub fn go() -> bool {
    let mut n = 0u32;
    let mut b = true;
    #[invariant(b)]
    #[invariant(n <= 3u32)]
    while { b = lt3(n); b } {
        n += 1;
    }
    b
}
