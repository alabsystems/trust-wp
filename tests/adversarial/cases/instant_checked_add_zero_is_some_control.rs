//@ expect: verify
//@ mechanism: the over-refusal half of the isolating pair for D-116. `Instant::checked_add` of a
//@ mechanism: zero duration cannot overflow, so it returns `Some`. D-116 keeps that fact while it
//@ mechanism: withdraws the claim that no call ever returns `None`.
//@ accept-means: n/a (control) — the contract is TRUE for every clock reading.
//@ fixed-by: D-116
//@ teeth: verified before and after D-116; its false twin
//@ teeth: instant_checked_add_overflow_claimed_some.rs is ACCEPTED before and FAILED after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn zero_is_some() -> bool {
    let i = Instant::now();
    i.checked_add(Duration::from_secs(0)).is_some()
}
