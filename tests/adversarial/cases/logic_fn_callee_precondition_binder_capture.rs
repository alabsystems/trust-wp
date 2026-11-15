//@ expect: reject
//@ mechanism: the callee's `requires` binds `i` and the caller's argument is the parameter `i`; the precondition owed at the call substitutes the argument capture-avoidingly (`logic_fn_verify::callee_preconditions`, `substitute_capture_avoiding`). A substitution that let the binder capture the argument would owe `forall i. 0 <= i && i < i ==> ..`, a tautology.
//@ accept-means: the precondition owed at a call was rewritten into a tautology by variable capture.
//@ WHY IT IS FALSE: at `i == 200` the callee requires every integer in `0..200` to be below 100, and 150 is not.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`, the call never examined.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(forall<i: Int> 0 <= i && i < x ==> i < 100)]
pub fn f(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(i: Int) -> Int {
    f(i)
}
