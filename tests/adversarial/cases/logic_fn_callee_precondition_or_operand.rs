//@ expect: reject
//@ mechanism: the right operand of `||` is evaluated only where the left one FAILS, so a call in it owes its callee's precondition under the left operand's negation (Creusot's vcgen `Binary Or`: `if a then Q(true) else VC(b, Q)`). A goal that read `||` like `&&` would put this call under `y > 0` and credit it.
//@ accept-means: a logic predicate that calls `needs_pos` only where `y <= 0` is credited `verified`.
//@ WHY IT IS FALSE: the call is evaluated exactly when `y > 0` fails, where `needs_pos` requires `y > 0`.
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
pub fn caller(y: Int) -> bool {
    y > 0 || needs_pos(y) > 0
}
