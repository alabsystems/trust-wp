//@ expect: verify
//@ mechanism: the control for instant_add_overflow_panic_uncharged.rs and
//@ mechanism: instant_sub_underflow_panic_uncharged.rs: adding or subtracting a zero duration
//@ mechanism: cannot overflow the clock, and a spec that charges the overflow must still discharge
//@ mechanism: it here.
//@ accept-means: n/a (control) — `i + 0s == i` and `i - 0s == i` for every clock reading.
//@ fixed-by: n/a (control); D-137 is the spec that owes the overflow and still verifies this.
//@ teeth: verified when committed, beside its two RED twins; `unknown` under D-121's refused
//@ teeth: marker (an over-refusal), verified again under D-137.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn add_sub_zero_same() -> bool {
    let i = Instant::now();
    let j = i + Duration::from_secs(0);
    let k = i - Duration::from_secs(0);
    j == i && k == i
}
