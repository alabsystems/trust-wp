//@ expect: reject
//@ mechanism: loop_condition_call_write_before_exit_read_after with a callee whose contract is two
//@ mechanism: implications, so the condition reads the symbol D-222 mints for the call's result and
//@ mechanism: its clauses are stated at it. `i = 0` runs between the call and the exit switch; the
//@ mechanism: exit and continuation read the header state, where `i == 7u32`.
//@ accept-means: the loop lane proved a postcondition over the header state for a value the exit
//@ accept-means: path overwrote before the loop left. Concretely: `go()` returns 0: the last
//@ accept-means: condition evaluation stores `i = 0` and `lt3(3)` is false.
//@ also-verified: lt3
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: ACCEPTED at exit 0 on this branch's merge of the campaign without D-229, with D-222 in
//@ teeth: force; `unknown` with D-229 (the `loop-condition-exit-write` marker). Refuted `failed`
//@ teeth: before D-222, when the condition read the call's destination as a free placeholder.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result ==> k < 3u32)]
#[ensures(!result ==> k >= 3u32)]
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
