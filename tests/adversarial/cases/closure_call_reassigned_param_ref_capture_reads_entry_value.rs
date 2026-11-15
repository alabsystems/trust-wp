//@ expect: reject
//@ mechanism: closure_call_reassigned_param_capture_reads_entry_value with the capture taken BY
//@ mechanism: REFERENCE (`|| x + 0` borrows `x`): the closure's state holds a borrow of the
//@ mechanism: reassigned parameter, and the call must owe the precondition over the value it points
//@ mechanism: at, not over the parameter's entry symbol.
//@ accept-means: a closure's precondition over a by-reference capture of a reassigned parameter is
//@ accept-means: checked against the parameter's entry value.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: x is 5 when `c()` runs; the closure requires 0.
//@ fn-failed: caller
//@ also-verified: caller::{closure#2}
//@ fixed-by: fix(closure-call): a call binds each capture by the names the closure's own contract lane reads it by
//@ teeth: ACCEPTED at exit 0 without the fix named in `fixed-by:`; `caller FAILED` with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn caller(mut x: i32) -> i32 {
    x = 5;
    let c = #[requires(x@ == 0)]
    || -> i32 { x + 0 };
    c()
}
