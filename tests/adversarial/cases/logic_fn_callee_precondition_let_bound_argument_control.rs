//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_let_bound_argument, the caller's precondition raised by one: `y > 1` makes `z = y - 1` positive.
//@ accept-means: n/a (control) — the local's value is inside the callee's precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[requires(y > 1)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    let z = y - 1;
    needs_pos(z)
}
