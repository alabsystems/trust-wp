//@ expect: reject
//@ mechanism: a block condition `{ let b = lt3(n); i = 0; b }` writes `i` after the call and before
//@ mechanism: the switch that leaves the loop, so the state at the exit is not the state at the
//@ mechanism: header: `i` is 0 there. The loop lane's exit and continuation read the header state,
//@ mechanism: where the invariant `i == 7u32` holds, and the write on the final pass is in no VC.
//@ mechanism: With the condition call's value stated (D-222) preservation no longer fails over a
//@ mechanism: free placeholder, and only D-229's refusal stands between that reading and a proof.
//@ accept-means: the loop lane proved a postcondition over the header state for a value the exit
//@ accept-means: path overwrote before the loop left. Concretely: `go()` evaluates the condition
//@ accept-means: four times; the fourth sets `i = 0`, `lt3(3)` is false, and `go` returns 0, not 7.
//@ also-verified: lt3
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: ACCEPTED at exit 0 on this branch's merge of the campaign without D-229, with D-222 in
//@ teeth: force; `unknown` with D-229 (the `loop-condition-exit-write` marker). Refuted `failed`
//@ teeth: before D-222, when the condition read the call's destination as a free placeholder.
//@ teeth: loop_condition_block_write_before_exit_read_after.rs is the same write with no call;
//@ teeth: loop_condition_call_write_before_exit_invariant_needs_no_condition.rs is this program with
//@ teeth: an invariant that needs no condition value.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 3u32))]
pub fn lt3(k: u32) -> bool { k < 3 }

#[ensures(result == 7u32)]
pub fn go() -> u32 {
    let mut n = 0u32;
    let mut i = 7u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    while { let b = lt3(n); i = 0; b } {
        i = 7;
        n += 1;
    }
    i
}
