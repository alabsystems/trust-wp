//@ expect: reject
//@ mechanism: a `let` that shadows the parameter: the precondition owed at the call reads the shadowing binding, which the goal keeps around it (`logic_fn_verify::callee_preconditions`, `PureExpr::Let`). A goal that read the parameter would owe `y > 0`, which the caller's precondition gives.
//@ accept-means: the goal read the shadowed parameter instead of the binding the call sees.
//@ WHY IT IS FALSE: at `y == 1` the shadowing `y` is `0`, and `needs_pos` requires it positive.
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
    let y = y - 1;
    needs_pos(y)
}
