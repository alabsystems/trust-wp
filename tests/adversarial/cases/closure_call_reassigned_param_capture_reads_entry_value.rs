//@ expect: reject
//@ mechanism: a call of a closure owes its precondition over the value each capture holds at the
//@ mechanism: call. A parameter reassigned before the closure is built holds a value that is not a
//@ mechanism: bare variable (`5`); a capture binding read off that value names nothing, and the
//@ mechanism: clause's `x` then reads the caller's parameter symbol, its ENTRY value `0`.
//@ accept-means: a closure's precondition is checked against a reassigned capture's entry value.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: x is 5 when `c()` runs; the closure requires 0.
//@ fn-failed: caller
//@ also-verified: caller::{closure#2}
//@ fixed-by: fix(closure-call): a call binds each capture by the name the closure's own lane reads it by
//@ teeth: ACCEPTED at exit 0 with the capture bound by the value it holds (without the fix named
//@ teeth: in `fixed-by:`); `caller FAILED` with the capture bound by the closure's own table.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn caller(mut x: i32) -> i32 {
    x = 5;
    let c = #[requires(x@ == 0)]
    || -> i32 {
        x
    };
    c()
}
