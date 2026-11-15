//@ expect: verify
//@ mechanism: the control for f64_add_zero_returns_input.rs: under round-to-nearest-even `-0.0 + 0.0` is
//@ mechanism: `+0.0`, so the sum is logically equal to `0.0` and not to the input `-0.0`.
//@ accept-means: n/a (control) — the function returns `+0.0` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (the real-number model has one zero).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0.0)]
pub fn sum_is_positive_zero() -> f64 {
    let z = -0.0f64;
    z + 0.0
}
