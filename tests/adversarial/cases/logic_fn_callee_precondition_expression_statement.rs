//@ expect: reject
//@ mechanism: a call written as an expression statement (`needs_pos(x);`) is kept by the logic body parser as a `$stmt` binding and owes its precondition like any other call (`logic_fn_verify::callee_preconditions`, `PureExpr::Let`).
//@ accept-means: a statement's call is never owed.
//@ WHY IT IS FALSE: at `x == 0` the body evaluates `needs_pos(0)`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`, the call never examined.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
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
#[ensures(true)]
pub fn caller(x: Int) -> Int {
    needs_pos(x);
    0
}
