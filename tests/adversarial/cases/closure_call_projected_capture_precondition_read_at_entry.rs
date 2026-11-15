//@ expect: reject
//@ mechanism: a `move` closure that reads only `p.0` captures the FIELD (edition 2021 disjoint
//@ mechanism: capture), so the closure's own lane reads its clause's `p.0` through a projected
//@ mechanism: capture, and the call's capture binding (the closure's name table, then the names read
//@ mechanism: off the caller's value) binds no name to it: the table leaves projected captures out,
//@ mechanism: and the captured value `5` names nothing. The call then owes `p.0@ == 0` over the
//@ mechanism: caller's parameter symbol, its ENTRY value, which the caller's precondition fixes to 0.
//@ accept-means: a closure's precondition over a projected capture is owed at the caller's entry state.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: p.0 is 5 when `c()` runs; the closure requires 0.
//@ also-verified: caller::{closure#2}
//@ teeth: UNVERIFIED — ACCEPTED at exit 0 with and without the capture-binding fix (the
//@ teeth: `fixed-by:` of closure_call_reassigned_param_capture_reads_entry_value), which binds
//@ teeth: whole-variable captures only; the defect is live. It would reject if a projected capture
//@ teeth: were bound by the path the closure's own lane collapses it from.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p.0@ == 0)]
pub fn caller(mut p: (i32, i32)) -> i32 {
    p.0 = 5;
    let c = #[requires(p.0@ == 0)]
    move || -> i32 { p.0 };
    c()
}
