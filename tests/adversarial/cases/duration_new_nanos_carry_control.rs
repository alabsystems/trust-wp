//@ expect: verify
//@ mechanism: the over-refusal half of the `Duration::new` pair. `new(secs, nanos)` carries whole
//@ mechanism: seconds out of `nanos` and panics only when that carry overflows `u64` seconds, which
//@ mechanism: is Creusot's precondition. The spec used to require `nanos < 10^9`, which refused this
//@ mechanism: call although it returns 2.5 seconds; it now owes the carry bound alone.
//@ accept-means: n/a (control) — `Duration::new(1, 1_500_000_000)` is 2_500 milliseconds in every
//@ accept-means: execution.
//@ fixed-by: D-137
//@ teeth: FAILED on `nanos < 10^9` before D-137, verified after; its false twin
//@ teeth: duration_new_carry_overflow_panics is rejected before and after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::Duration;

#[ensures(result)]
pub fn new_carries_nanos() -> bool {
    let d = Duration::new(1, 1_500_000_000);
    d == Duration::from_millis(2_500)
}
