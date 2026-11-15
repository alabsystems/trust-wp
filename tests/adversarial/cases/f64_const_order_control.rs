//@ expect: verify
//@ mechanism: the control for f64_eq_reflexive_despite_nan.rs and f64_le_or_gt_total_despite_nan.rs:
//@ mechanism: a comparison of two finite float constants has one IEEE-754 answer, and a float model
//@ mechanism: that admits NaN must still decide it.
//@ accept-means: n/a (control) — `1.0 < 2.0` is `true` in every execution.
//@ fixed-by: n/a
//@ teeth: verified when committed, beside its two RED twins.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn const_lt() -> bool {
    1.0f64 < 2.0f64
}
