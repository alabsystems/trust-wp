//@ expect: reject
//@ mechanism: a call under a quantifier owes its callee's precondition for EVERY value of the binder (Creusot's vcgen `Quant`: `forall x. VC(body, true)`); the goal the logic lane states wraps it in the binder (`logic_fn_verify::callee_preconditions`, `PureExpr::Forall`).
//@ accept-means: a logic predicate that applies `needs_pos` to every integer is credited `verified`.
//@ WHY IT IS FALSE: the body evaluates `needs_pos(i)` at `i == 0`, where its precondition `i > 0` fails.
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
pub fn caller() -> bool {
    pearlite! { forall<i: Int> needs_pos(i) == i }
}
