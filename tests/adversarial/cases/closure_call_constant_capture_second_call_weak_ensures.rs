//@ expect: reject
//@ mechanism: the second call of a closure that writes its `&mut` capture owes the precondition
//@ mechanism: over the capture's value after the first call. With the capture bound at the call,
//@ mechanism: that value is the final value of the constant the capture held at entry, which has no
//@ mechanism: prophecy slot; folding it to the constant would owe `0@ == 0` and credit the call.
//@ accept-means: the final value of a constant-initialized capture is read as the constant.
//@
//@ WHY THE CALL IS WRONG, as a concrete execution: the first call leaves x at 1; the second requires 0.
//@ verdict: unknown
//@ refused-with: final-collapse refused (fail-closed)
//@ also-verified: caller::{closure#0}
//@ teeth: rejected at the campaign tip (`caller FAILED`, the obligation over an unbound name) and
//@ teeth: with the capture bound, by the constant-carrier arm of the final-collapse guard (D-14).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn caller() {
    let mut x = 0i32;
    let mut c = #[requires(x@ == 0)]
    #[ensures(x@ >= 0)]
    || {
        x = 1;
    };
    c();
    c();
}
