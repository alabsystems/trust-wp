//@ expect: reject
//@ mechanism: the second call of a closure that writes its `&mut` capture owes the precondition
//@ mechanism: over the capture's value after the first call, not the constant it held at entry.
//@ accept-means: a second call of a mutating closure is checked against the capture's entry value.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: the first call leaves x at 1; the second requires 0.
//@ verdict: error
//@ refused-with: caller vacuous (contradictory premises)
//@ also-verified: caller::{closure#0}
//@ teeth: rejected at the campaign tip (`caller FAILED`, the obligation over an unbound name) and
//@ teeth: with the capture bound, where the first call's credit states the final value of the
//@ teeth: constant the capture held, and the premises that read it are refused as contradictory.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn caller() {
    let mut x = 0i32;
    let mut c = #[requires(x@ == 0)]
    #[ensures(x@ == 1)]
    || {
        x = 1;
    };
    c();
    c();
}
