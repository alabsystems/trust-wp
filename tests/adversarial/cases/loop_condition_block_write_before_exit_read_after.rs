//@ expect: reject
//@ mechanism: a block condition `{ let b = n < 3; i = 0; b }` writes `i` before the switch that
//@ mechanism: leaves the loop, with no call. The loop lane's exit and continuation read the header
//@ mechanism: state, where the invariant `i == 7u32` holds; the write on the final pass is in no
//@ mechanism: VC.
//@ accept-means: the loop lane proved a postcondition over the header state for a value the exit
//@ accept-means: path overwrote before the loop left. Concretely: `go()` returns 0: the fourth
//@ accept-means: condition evaluation stores `i = 0` and `n < 3` is false.
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: ACCEPTED at exit 0 at the campaign tip and on this branch's merge of it without D-229;
//@ teeth: `unknown` with D-229 (the `loop-condition-exit-write` marker).
//@ teeth: loop_condition_call_write_before_exit_read_after.rs is the call spelling.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7u32)]
pub fn go() -> u32 {
    let mut n = 0u32;
    let mut i = 7u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    while { let b = n < 3; i = 0; b } {
        i = 7;
        n += 1;
    }
    i
}
