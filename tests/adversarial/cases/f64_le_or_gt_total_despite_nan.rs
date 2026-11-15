//@ expect: reject
//@ mechanism: an `f64` reaches the solver as a real number, and the order on the reals is total, so
//@ mechanism: `x <= y || x > y` reads as a tautology. Rust compares floats by IEEE-754, under which
//@ mechanism: every ordered comparison with a NaN operand is false; Creusot reads the comparisons
//@ mechanism: through Why3's IEEE floats and does not prove it. The ordered-comparison twin of
//@ mechanism: f64_eq_reflexive_despite_nan.rs.
//@ accept-means: `le_or_gt(f64::NAN, 0.0)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`le_or_gt verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn le_or_gt(x: f64, y: f64) -> bool {
    x <= y || x > y
}
