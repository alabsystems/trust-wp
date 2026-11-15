//@ expect: reject
//@ mechanism: the upper twin of duration_checked_mul_max_boundary_control.rs: `2^63` seconds times
//@ mechanism: two is `2^64` seconds, `Duration::MAX` and one nanosecond, claimed `Some`. A bound one
//@ mechanism: nanosecond long would prove it.
//@ accept-means: `Duration::checked_mul`'s spec claims `Some` for a product past `Duration::MAX`.
//@ accept-means: `f()` returns false under stock rustc: `secs * rhs` overflows, so `None`.
//@ fixed-by: n/a — rejected when committed (D-138 is the spec it guards).
//@ teeth: rejected when committed; ACCEPTED with the bound one nanosecond long, rejected under the pre-D-138 spec.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Duration;

#[ensures(result)]
pub fn f() -> bool {
    Duration::from_secs(9_223_372_036_854_775_808).checked_mul(2).is_some()
}
