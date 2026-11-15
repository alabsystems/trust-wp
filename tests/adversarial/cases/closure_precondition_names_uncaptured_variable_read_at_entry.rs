//@ expect: reject
//@ mechanism: a closure's precondition names `x`, which its body does not capture (`let _ = x;`
//@ mechanism: reads nothing). The closure's own lane reads that `x` as an unconstrained name, and
//@ mechanism: the call owes the clause over the same name, which in the caller denotes its
//@ mechanism: parameter's ENTRY value; the reassignment before the call is never seen.
//@ accept-means: a closure clause naming an uncaptured variable is owed at the caller's entry state.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: x is 5 when `c()` runs; the clause says 0.
//@ also-verified: caller::{closure#2}
//@ teeth: UNVERIFIED — ACCEPTED at exit 0 with and without the capture-binding fix (the
//@ teeth: `fixed-by:` of closure_call_reassigned_param_capture_reads_entry_value), which binds only
//@ teeth: what the closure captures; the defect is live. It would reject if the call owed the
//@ teeth: clause at the call's state, or refused a clause name that is neither a capture nor a
//@ teeth: parameter.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn caller(mut x: i32) {
    x = 5;
    let c = #[requires(x@ == 0)]
    || {
        let _ = x;
    };
    c();
}
