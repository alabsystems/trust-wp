//@ expect: reject
//@ mechanism: a direct call of a closure owes the closure's precondition over the value each
//@ mechanism: capture holds at the call. A capture whose value is a constant (`let x = 2;`) is
//@ mechanism: bound to the name the closure's clauses read it by, the table its own lane assumes
//@ mechanism: those clauses with, so the call owes `2@ == 1`.
//@ accept-means: a closure's precondition is not owed at a call when a capture holds a constant.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: x is 2 at the call and the closure requires 1.
//@ fn-failed: caller
//@ also-verified: caller::{closure#1}
//@ also-verified-assertion: creusot_test::caller::{closure#1}
//@ teeth: rejected (`caller FAILED`) at the campaign tip, where the obligation was stated over a
//@ teeth: name no capture binding read, and with the capture bound.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn caller() {
    let x = 2i32;
    (#[requires(x@ == 1)]
    || {
        proof_assert!(x@ == 1);
    })();
}
