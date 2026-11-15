//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: `Duration + Duration` panics ("overflow when adding durations") past
//@ mechanism: `Duration::MAX`, and its std spec stated only `result@ == self@ + rhs@` over the
//@ mechanism: unbounded nanosecond view, so an overflowing sum was trusted. The spec now owes the sum
//@ mechanism: within `u64::MAX` seconds and 999_999_999 nanoseconds, as Creusot's does.
//@ accept-means: `Duration::add`'s spec stopped owing its overflow panic.
//@ fixed-by: D-121 — a std spec owes every panic of its function it can state.
//@ WHY THE CONTRACT IS FALSE: `u64::MAX` seconds plus one second is past `Duration::MAX`, so the
//@ WHY THE CONTRACT IS FALSE: only call `f` makes panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_duration_add_in_range_control differs in the first operand alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Duration;

#[ensures(true)]
pub fn f() -> u64 {
    let d = Duration::from_secs(u64::MAX) + Duration::from_secs(1);
    d.as_secs()
}
