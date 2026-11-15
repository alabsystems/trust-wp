//@ expect: reject
//@ mechanism: the by-reference twin of closure_call_projected_capture_precondition_read_at_entry: a
//@ mechanism: non-`move` closure reading `p.0` captures `&p.0`, a projected capture the call's
//@ mechanism: binding leaves unbound, so the clause's `p.0` is owed over the caller's parameter
//@ mechanism: symbol, its ENTRY value.
//@ accept-means: a closure's precondition over a projected by-reference capture is owed at the
//@ accept-means: caller's entry state.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: p.0 is 5 when `c()` runs; the closure requires 0.
//@ also-verified: caller::{closure#2}
//@ teeth: UNVERIFIED — ACCEPTED at exit 0 with and without the capture-binding fix; the defect is live.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p.0@ == 0)]
pub fn caller(mut p: (i32, i32)) -> i32 {
    p.0 = 5;
    let c = #[requires(p.0@ == 0)]
    || -> i32 { p.0 + 0 };
    c()
}
