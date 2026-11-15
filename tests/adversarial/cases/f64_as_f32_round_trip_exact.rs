//@ expect: reject
//@ mechanism: `as` between float types is translated as the identity because both are reals, so a
//@ mechanism: narrowing `f64 as f32` and the widening back return the input. `0.1f64 as f32` rounds, and
//@ mechanism: `NaN` round-trips to NaN, which is unequal to itself.
//@ accept-means: `round_trip(0.1)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`round_trip verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn round_trip(x: f64) -> bool {
    (x as f32) as f64 == x
}
