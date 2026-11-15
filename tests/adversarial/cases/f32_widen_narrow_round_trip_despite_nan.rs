//@ expect: reject
//@ mechanism: `as` between float types is translated as the identity. Widening an `f32` to `f64` and
//@ mechanism: narrowing it back is exact for every value but NaN, which round-trips to a NaN that is
//@ mechanism: unequal to itself; the narrowing twin f64_as_f32_round_trip_exact.rs also fails by rounding.
//@ accept-means: `widen_narrow(f32::NAN)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`widen_narrow verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn widen_narrow(x: f32) -> bool {
    (x as f64) as f32 == x
}
