//@ expect: verify
//@ mechanism: the control for f32_literal_sum_absorbs_addend.rs, the same body under the true contract:
//@ mechanism: in single precision `16777216.0f32 + 1.0f32` is `16777216.0f32`.
//@ accept-means: n/a (control) — `absorbs()` returns `true` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: failed on the campaign tip before D-215 (a counterexample from exact real addition); verified
//@ teeth: after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn absorbs() -> bool {
    16777216.0f32 + 1.0f32 == 16777216.0f32
}
