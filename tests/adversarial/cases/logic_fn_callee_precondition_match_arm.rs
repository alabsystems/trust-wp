//@ expect: reject
//@ mechanism: a call in a `match` arm owes its callee's precondition under the arm's pattern, with the arm's binder in scope (`logic_fn_verify::callee_preconditions`, `PureExpr::Match`).
//@ accept-means: a call in a match arm is never owed.
//@ WHY IT IS FALSE: at `o == Some(0)` the `Some` arm evaluates `needs_pos(0)`.
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
pub fn caller(o: Option<Int>) -> Int {
    match o {
        Some(v) => needs_pos(v),
        None => 0,
    }
}
