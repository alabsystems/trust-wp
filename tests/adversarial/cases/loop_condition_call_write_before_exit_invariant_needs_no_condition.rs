//@ expect: reject
//@ mechanism: loop_condition_call_write_before_exit_read_after.rs with an invariant that needs
//@ mechanism: nothing from the condition: the body stores `n = 5`, so preservation holds whatever
//@ mechanism: the call returned. `i = 0` runs between the call and the exit switch; the exit and
//@ mechanism: continuation read the header state, where `i == 7u32`. This spelling reaches the exit
//@ mechanism: modeling without D-222's stated condition value, so the call-condition reach of the
//@ mechanism: defect predates D-222.
//@ accept-means: the loop lane proved a postcondition over the header state for a value the exit
//@ accept-means: path overwrote before the loop left. Concretely: `go()` evaluates the condition
//@ accept-means: twice; the second sets `i = 0`, `lt3(5)` is false, and `go` returns 0, not 7.
//@ also-verified: lt3
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: UNVERIFIED as a D-229 gate on this branch: without D-229 `go` is already `unknown`, a
//@ teeth: preservation refutation of an invariant trust-wp synthesized being withheld so that the
//@ teeth: loop phase stays unproved (D-221); ACCEPTED at exit 0 at the campaign tip, before D-222.
//@ teeth: With D-229 the `loop-condition-exit-write` marker refuses it whatever the loop phases
//@ teeth: prove.
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
    while { let b = lt3(n); i = 0; b } {
        i = 7;
        n = 5;
    }
    i
}
