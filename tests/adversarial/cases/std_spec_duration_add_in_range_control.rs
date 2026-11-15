//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_duration_add_overflow_panics, identical but for the first
//@ mechanism: operand, and with the sum's value checked: the precondition is owed, not a refusal.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Duration;

#[ensures(result == 3)]
pub fn f() -> u64 {
    let d = Duration::from_secs(2) + Duration::from_secs(1);
    d.as_secs()
}
