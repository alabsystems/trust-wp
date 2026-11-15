//@ expect: reject
//@ mechanism: a loop that exits when its float guard `y < 10.0` is false leaves `!(y < 10.0)` as the exit
//@ mechanism: fact, and the code after the loop claims `y >= 10.0`. Over reals the two are one fact; over
//@ mechanism: IEEE-754 floats they are not: a NaN entry value never enters the loop and `NaN >= 10.0` is
//@ mechanism: false. The loop-exit twin of f64_branch_not_ge_read_as_lt.rs, in a `while` guard and a
//@ mechanism: `loop`/`break` guard.
//@ accept-means: `while_exit(f64::NAN)` and `break_exit(f64::NAN)` return `false`; an accept claims each
//@ accept-means: returns `true`.
//@ fixed-by: D-215
//@ teeth: rejected on the campaign tip before D-215 too, but there only by the loop invariant's
//@ teeth: initialization (`while_exit FAILED ✗ (loop invariant)` of `#[invariant(true)]`, the over-refusal
//@ teeth: that also refutes this loop's `i64` twin); under D-215 the invariant is proved and each claim is
//@ teeth: FAILED (postcondition). A pin of the exit reading, not a hole measured open.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn while_exit(x: f64) -> bool {
    let mut y = x;
    #[invariant(true)]
    while y < 10.0 {
        y = 10.0;
    }
    y >= 10.0
}

#[ensures(result)]
pub fn break_exit(x: f64) -> bool {
    let mut y = x;
    #[invariant(true)]
    loop {
        if !(y < 10.0) {
            break;
        }
        y = 10.0;
    }
    y >= 10.0
}
