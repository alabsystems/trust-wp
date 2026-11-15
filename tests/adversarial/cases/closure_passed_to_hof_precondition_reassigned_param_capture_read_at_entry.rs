//@ expect: reject
//@ mechanism: the higher-order twin of closure_call_reassigned_param_capture_reads_entry_value: the
//@ mechanism: closure is not called here but handed to `call`, which owes `f.precondition(())`.
//@ mechanism: The capture-binding fix binds captures by the closure's own table only in the direct
//@ mechanism: call lane; the lane that instantiates `f.precondition(())` for this closure still
//@ mechanism: reads the clause's `x` as the caller's parameter symbol, its ENTRY value `0`.
//@ accept-means: a closure precondition owed through a higher-order callee's `precondition` is
//@ accept-means: checked against a reassigned capture's entry value.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: x is 5 when `call(c)` runs `c()`; the
//@ WHY THE CALL IS WRONG, as a concrete execution: closure requires 0.
//@ also-verified: call, caller::{closure#2}
//@ teeth: UNVERIFIED — ACCEPTED at exit 0 with and without the capture-binding fix; the defect is
//@ teeth: live. Its constant-capture twin (`let x = 5;` in the caller) is rejected.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(f.precondition(()))]
fn call<F: Fn() -> i32>(f: F) -> i32 {
    f()
}

#[requires(x@ == 0)]
pub fn caller(mut x: i32) -> i32 {
    x = 5;
    let c = #[requires(x@ == 0)]
    || -> i32 { x + 0 };
    call(c)
}
