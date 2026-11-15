//@ expect: reject
//@ mechanism: f32 `+` is read as exact real addition, so `x + 1.0 != x` is a tautology. In single
//@ mechanism: precision `16777216.0 + 1.0` rounds back to `16777216.0`, and NaN is unequal to everything.
//@ accept-means: `add_one_changes(16777216.0)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`add_one_changes verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn add_one_changes(x: f32) -> bool {
    x + 1.0 != x
}
