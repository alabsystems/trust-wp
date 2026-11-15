//@ expect: reject
//@ mechanism: closure_passed_to_hof_precondition_reassigned_param_capture_read_at_entry with a
//@ mechanism: projected capture (`move || p.0` captures the field): `f.precondition(())` is
//@ mechanism: owed over the caller's parameter symbol, its ENTRY value.
//@ accept-means: a closure precondition owed through a higher-order callee's `precondition` reads a
//@ accept-means: projected capture at the caller's entry state.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: p.0 is 5 when `call(c)` runs `c()`; the
//@ WHY THE CALL IS WRONG, as a concrete execution: closure requires 0.
//@ also-verified: call, caller::{closure#2}
//@ teeth: UNVERIFIED — ACCEPTED at exit 0 with and without the capture-binding fix; the defect is live.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(f.precondition(()))]
fn call<F: Fn() -> i32>(f: F) -> i32 {
    f()
}

#[requires(p.0@ == 0)]
pub fn caller(mut p: (i32, i32)) -> i32 {
    p.0 = 5;
    let c = #[requires(p.0@ == 0)]
    move || -> i32 { p.0 };
    call(c)
}
