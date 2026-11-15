//@ expect: reject
//@ mechanism: a call whose argument is a `let`-bound local owes its callee's precondition at the local's VALUE; the goal keeps the binding (`logic_fn_verify::callee_preconditions`, `PureExpr::Let`).
//@ accept-means: a logic function that calls `needs_pos(y - 1)` at `y == 1`, which its precondition admits, is credited `verified`.
//@ WHY IT IS FALSE: at `y == 1` the local `z` is `0`, and `needs_pos` requires `z > 0`.
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
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    let z = y - 1;
    needs_pos(z)
}
