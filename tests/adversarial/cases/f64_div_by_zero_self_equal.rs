//@ expect: reject
//@ mechanism: f64 `/` reaches the solver as real division, whose value at a zero divisor is one
//@ mechanism: unconstrained term, so `x / 0.0 == x / 0.0` holds by congruence. IEEE-754 gives `0.0 / 0.0 == NaN`,
//@ mechanism: and NaN is unequal to itself.
//@ accept-means: `div_zero_self_equal(0.0)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`div_zero_self_equal verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn div_zero_self_equal(x: f64) -> bool {
    x / 0.0 == x / 0.0
}
