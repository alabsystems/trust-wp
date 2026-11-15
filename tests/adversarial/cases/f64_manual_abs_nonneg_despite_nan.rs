//@ expect: reject
//@ mechanism: a hand-written absolute value, `if x < 0.0 { -x } else { x }`, is read over the reals, where
//@ mechanism: every value is below zero or not, so the result is never negative. Under IEEE-754 NaN fails
//@ mechanism: `x < 0.0` and takes the `else` arm unchanged, and `NaN >= 0.0` is false.
//@ accept-means: `abs_nonneg(f64::NAN)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`abs_nonneg verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn abs_nonneg(x: f64) -> bool {
    let y = if x < 0.0 { -x } else { x };
    y >= 0.0
}
