//@ expect: reject
//@ mechanism: the sideways twins of instant_add_overflow_panic_uncharged and
//@ mechanism: instant_sub_underflow_panic_uncharged: the operand is a parameter the contract leaves
//@ mechanism: unbounded, not a literal. `Instant + Duration` owes `rhs@ == 0` and `Instant - Duration`
//@ mechanism: owes `self@ >= rhs@` (D-137); neither contract states either, so both FAIL at the call.
//@ accept-means: an `Instant` operator's spec stopped owing its panic, so a contract that admits a
//@ accept-means: panicking input verifies. `add_any(Instant::now(), Duration::MAX)` and
//@ accept-means: `sub_any(Instant::now(), Duration::MAX)` panic (stock rustc on aarch64-apple-darwin).
//@ fixed-by: D-137
//@ teeth: both ACCEPTED before D-121 (the specs stated no precondition; `sub_any`'s disjunction is
//@ teeth: the saturating clause the old spec granted); `unknown` on D-121's marker; FAILED on the
//@ teeth: owed bound under D-137. The TRUE twins are instant_add_duration_zero_param_control and
//@ teeth: instant_sub_duration_after_checked_sub_control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result@ == i@ + d@)]
pub fn add_any(i: Instant, d: Duration) -> Instant {
    i + d
}

#[ensures(result@ == i@ - d@ || result@ == 0)]
pub fn sub_any(i: Instant, d: Duration) -> Instant {
    i - d
}
