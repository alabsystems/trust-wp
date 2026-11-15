//@ expect: verify
//@ mechanism: the control for duration_add_overflow_panic_uncharged.rs: a sum far below
//@ mechanism: `Duration::MAX` returns, and a spec that states the overflow precondition must still
//@ mechanism: discharge it for literal operands.
//@ accept-means: n/a (control) — one second plus two seconds is three seconds in every execution.
//@ fixed-by: n/a
//@ teeth: verified when committed, beside its RED twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::Duration;

#[ensures(result)]
pub fn dur_add_small() -> bool {
    let d = Duration::from_secs(1) + Duration::from_secs(2);
    d == Duration::from_secs(3)
}
