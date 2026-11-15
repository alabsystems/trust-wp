//@ expect: reject
//@ verdict: unknown
//@ refused-with: f unknown (refutation withheld: a phantom sort upgrade split
//@ mechanism: The two-conjunct twin of duration_checked_add_max_boundary_control.rs: the first sum lands on
//@ mechanism: `Duration::MAX` (`Some`), the second is one nanosecond past it and is claimed `Some`.
//@ mechanism: Its premise is scoped to the edge `$call.is_some()` of the first (D-169), which reads the
//@ mechanism: constant the phantom upgrade abandoned when the first call's postcondition matched it, so the
//@ mechanism: refutation is withheld (D-218) as its control's is: the program is false, the model is not
//@ mechanism: an execution of it.
//@ accept-means: `Duration::checked_add` past `Duration::MAX` is trusted to be `Some`.
//@ fixed-by: n/a — rejected before D-218 and with it.
//@ teeth: `f FAILED` before D-218; `f unknown (refutation withheld)` with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Duration;

#[ensures(result)]
pub fn f() -> bool {
    Duration::from_secs(u64::MAX).checked_add(Duration::new(0, 999_999_999)).is_some()
        && Duration::new(u64::MAX, 999_999_999).checked_add(Duration::from_nanos(1)).is_some()
}
