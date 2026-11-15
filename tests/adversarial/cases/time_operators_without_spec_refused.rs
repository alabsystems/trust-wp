//@ expect: reject
//@ mechanism: the `Duration` and `Instant` operators that have no entry of their own: `Duration * u32`,
//@ mechanism: `Duration / u32`, the four `Duration` assignment operators, `Instant +=`/`-=` and
//@ mechanism: `Duration::from_secs_f64`. Each reaches the operator trait's opaque
//@ mechanism: `T::<op>.precondition(..)` or the opaque-call fallback's fail-closed `false`, as
//@ mechanism: Creusot refuses a std call it has no contract for. Every function here panics on
//@ mechanism: every call; a spec added for any of them without its panic condition is caught here.
//@ accept-means: a std spec for a `Duration`/`Instant` operator or for `from_secs_f64` states no
//@ accept-means: panic precondition, so a body that panics on every call verifies. Each function
//@ accept-means: below panics on every call (stock rustc, overflow checks on).
//@ fixed-by: n/a — rejected when committed; D-137 names the operators this guards.
//@ teeth: every function rejected (FAILED on the opaque trait precondition, or `unknown` on the
//@ teeth: fail-closed `false`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn dur_mul_overflows() -> bool {
    let _d = Duration::from_secs(u64::MAX) * 2;
    true
}

#[ensures(result)]
pub fn dur_div_by_zero() -> bool {
    let _d = Duration::from_secs(1) / 0;
    true
}

#[ensures(result)]
pub fn dur_add_assign_overflows() -> bool {
    let mut d = Duration::from_secs(u64::MAX);
    d += Duration::from_secs(1);
    d >= Duration::from_secs(0)
}

#[ensures(result)]
pub fn dur_sub_assign_underflows() -> bool {
    let mut d = Duration::from_secs(0);
    d -= Duration::from_secs(1);
    d >= Duration::from_secs(0)
}

#[ensures(result)]
pub fn dur_mul_assign_overflows() -> bool {
    let mut d = Duration::from_secs(u64::MAX);
    d *= 2;
    d >= Duration::from_secs(0)
}

#[ensures(result)]
pub fn dur_div_assign_by_zero() -> bool {
    let mut d = Duration::from_secs(1);
    d /= 0;
    d >= Duration::from_secs(0)
}

#[ensures(result)]
pub fn dur_from_negative_secs() -> bool {
    let _d = Duration::from_secs_f64(-1.0);
    true
}

#[ensures(result)]
pub fn inst_add_assign_overflows() -> bool {
    let i = Instant::now();
    let mut j = i;
    j += Duration::from_secs(u64::MAX);
    j > i
}

#[ensures(result)]
pub fn inst_sub_assign_underflows() -> bool {
    let i = Instant::now();
    let mut j = i;
    j -= Duration::from_secs(u64::MAX);
    j <= i
}
