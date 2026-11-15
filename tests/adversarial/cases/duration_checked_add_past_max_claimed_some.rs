//@ expect: reject
//@ mechanism: the upper twin of duration_checked_add_max_boundary_control.rs: a sum one nanosecond
//@ mechanism: past `Duration::MAX` claimed `Some`. A bound one nanosecond long, or a `Some` arm that
//@ mechanism: states no bound, would prove it.
//@ accept-means: `Duration::checked_add`'s spec claims `Some` for a sum past `Duration::MAX`.
//@ accept-means: `f()` returns false under stock rustc: the seconds carry overflows, so `None`.
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
    Duration::new(u64::MAX, 999_999_999).checked_add(Duration::from_nanos(1)).is_some()
}
