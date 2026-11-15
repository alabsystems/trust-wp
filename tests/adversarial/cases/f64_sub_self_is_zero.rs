//@ expect: reject
//@ mechanism: f64 `-` reaches the solver as real subtraction, so `x - x` is `0`. IEEE-754 gives
//@ mechanism: `NaN - NaN == NaN` and `inf - inf == NaN`, neither of which is the value `0.0` the contract names.
//@ accept-means: `sub_self(f64::INFINITY)` returns NaN; an accept claims it returns `0.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`sub_self verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0.0)]
pub fn sub_self(x: f64) -> f64 {
    x - x
}
