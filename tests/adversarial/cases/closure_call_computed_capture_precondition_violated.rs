//@ expect: reject
//@ mechanism: the capture `y` holds `a + 1`, a value that is not a bare variable, so a binding
//@ mechanism: read off the caller's value names nothing; the call owes the closure's precondition
//@ mechanism: over `a + 1` under the name the closure reads it by.
//@ accept-means: a closure's precondition is not owed at a call when a capture holds a computed value.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: y is a + 1, never a.
//@ fn-failed: caller
//@ also-verified: caller::{closure#2}
//@ also-verified-assertion: creusot_test::caller::{closure#2}
//@ teeth: rejected (`caller FAILED`) at the campaign tip and with the capture bound.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@ < 100)]
pub fn caller(a: i32) {
    let y = a + 1;
    (#[requires(y@ == a@)]
    || {
        proof_assert!(y@ == a@);
    })();
}
