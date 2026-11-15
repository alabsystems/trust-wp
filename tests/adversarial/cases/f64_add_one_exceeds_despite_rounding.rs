//@ expect: reject
//@ mechanism: f64 `+` reaches the solver as exact real addition, under which `x + 1.0 > x` is a
//@ mechanism: tautology. IEEE-754 addition rounds: `1e16 + 1.0 == 1e16`, `inf + 1.0 == inf`, and every
//@ mechanism: comparison with NaN is false.
//@ accept-means: `add_one_exceeds(1e16)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`add_one_exceeds verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn add_one_exceeds(x: f64) -> bool {
    x + 1.0 > x
}
