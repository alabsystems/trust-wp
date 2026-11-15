//@ expect: verify
//@ mechanism: the control for f64_literal_sum_rounds_off_decimal.rs, one literal apart: the contract
//@ mechanism: names the value Rust's `0.1 + 0.2` rounds to, and the host fold computes it.
//@ accept-means: n/a (control) — `sum()` returns `0.30000000000000004` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: failed on the campaign tip before D-215 (the exact real sum is not the rounded one); verified
//@ teeth: after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0.30000000000000004)]
pub fn sum() -> f64 {
    0.1 + 0.2
}
