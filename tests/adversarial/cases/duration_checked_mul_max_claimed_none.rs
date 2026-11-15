//@ expect: reject
//@ mechanism: the lower twin of duration_checked_mul_max_boundary_control.rs: a product equal to
//@ mechanism: `Duration::MAX` claimed `None`. A `checked_mul` bound one nanosecond short (`<` for
//@ mechanism: `<=`) would prove it.
//@ accept-means: `Duration::checked_mul`'s spec claims `None` for a product `Duration` can hold.
//@ accept-means: `f()` returns false under stock rustc: the product is exactly `Duration::MAX`, so `Some`.
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
    Duration::new(6_148_914_691_236_517_205, 333_333_333).checked_mul(3).is_none()
}
