//@ expect: reject
//@ mechanism: a call inside a logic closure owes its callee's precondition for every value of the closure's parameters (Creusot's vcgen `Closure`: `forall x. VC(body, true)`); the goal wraps it in the parameters (`logic_fn_verify::callee_preconditions`, `PureExpr::Closure`).
//@ accept-means: a call inside a logic closure is never owed.
//@ WHY IT IS FALSE: the closure applies `needs_pos` at `i == 0`, where `i > 0` fails.
//@ teeth: MEASURED on the commit before D-119: not accepted, but only because the ensures lane demoted the closure encoding (`postcondition unverified (demoted: ... opaque_closure_value_fallback(1))`, exit 2); the call was never examined.
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
pub fn caller() -> Mapping<Int, Int> {
    |i: Int| needs_pos(i)
}
