//@ expect: reject
//@ mechanism: the lower twin of duration_checked_add_max_boundary_control.rs: a sum equal to
//@ mechanism: `Duration::MAX` claimed `None`. A `checked_add` bound one nanosecond short (`<` for `<=`)
//@ mechanism: would prove it.
//@ accept-means: `Duration::checked_add`'s spec claims `None` for a sum `Duration` can hold.
//@ accept-means: `f()` returns false under stock rustc: the sum is exactly `Duration::MAX`, so `Some`.
//@ fixed-by: n/a — rejected when committed (D-138 is the spec it guards).
//@ teeth: rejected when committed; ACCEPTED with the bound made strict, rejected under the pre-D-138 spec.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Duration;

#[ensures(result)]
pub fn f() -> bool {
    Duration::from_secs(u64::MAX).checked_add(Duration::new(0, 999_999_999)).is_none()
}
