//@ expect: verify
//@ mechanism: control: an open logic function whose body is `i32` arithmetic, read by a caller's
//@ mechanism: postcondition. D-232 states the body's wrapping `+` as an `ite` term (a body is no
//@ mechanism: comparison to state it around).
//@ WHY THE CONTRACT IS TRUE: x < i32::MAX, so x + 1 does not wrap and the body returns it.
//@ xfail: ay computes the UNSAT and withholds it (`proof-trusted`): the `ite` of integers does
//@ xfail: not certify.
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
pub fn add_one_open(x: i32) -> i32 {
    x + 1i32
}

#[requires(x < i32::MAX)]
#[ensures(result == add_one_open(x))]
pub fn add_one_runtime(x: i32) -> i32 {
    x + 1
}
