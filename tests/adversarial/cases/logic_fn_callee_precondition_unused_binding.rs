//@ expect: reject
//@ mechanism: a call bound to a name the rest of the body never reads still owes its precondition: the binding's value is walked whether or not the continuation uses it (`logic_fn_verify::callee_preconditions`, `PureExpr::Let`).
//@ accept-means: an unused binding's call is never owed.
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
    let z = needs_pos(x);
    0
}
