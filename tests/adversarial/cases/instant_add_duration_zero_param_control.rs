//@ expect: verify
//@ mechanism: the over-refusal half of the `Instant + Duration` pair, over a parameter. The operator
//@ mechanism: is `checked_add(rhs).expect(..)`, and `Instant::checked_add`'s spec promises `Some` for
//@ mechanism: a zero duration only (D-116), so the operator owes `rhs@ == 0`; a caller whose own
//@ mechanism: contract bounds the duration to zero discharges it.
//@ accept-means: n/a (control) — adding a zero duration returns the same instant.
//@ fixed-by: D-137
//@ teeth: verified before D-121, refused under D-121's `unmodelled_panic` marker, verified under
//@ teeth: D-137. The false twin is instant_duration_operators_param_unbounded_panics (`add_any`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[requires(d@ == 0)]
#[ensures(result == i)]
pub fn add_zero(i: Instant, d: Duration) -> Instant {
    i + d
}
