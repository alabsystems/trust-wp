//@ expect: reject
//@ mechanism: a call in the `else` arm of an `if` owes its callee's precondition under the NEGATED condition (`logic_fn_verify::callee_preconditions`, `PureExpr::Ite`). A goal that kept the condition itself, or dropped the call, credits this function.
//@ accept-means: a logic function that calls `needs_pos` exactly where its argument is not positive is credited `verified`.
//@ WHY IT IS FALSE: every call this body makes is at `y <= 0`, where `needs_pos` requires `y > 0`; Creusot's `vc_caller` carries that precondition under `not (y > 0)` and is invalid.
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
pub fn caller(y: Int) -> Int {
    if y > 0 {
        0
    } else {
        needs_pos(y)
    }
}
