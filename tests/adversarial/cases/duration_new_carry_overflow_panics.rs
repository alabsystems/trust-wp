//@ expect: reject
//@ mechanism: the false half of the `Duration::new` pair. `new(u64::MAX, 10^9)` carries one second
//@ mechanism: into `u64::MAX` seconds and panics ("overflow in Duration::new"). D-137 replaced
//@ mechanism: `nanos < 10^9` by the carry bound `secs@ + nanos@ / 10^9 <= u64::MAX@`, which is
//@ mechanism: weaker; this pins that the weaker bound still charges the one input that panics.
//@ accept-means: `Duration::new`'s spec stopped owing the carry overflow, so a body that panics on
//@ accept-means: every call verifies. `new_carry_overflows()` panics on every call (stock rustc).
//@ fixed-by: D-137
//@ teeth: rejected (FAILED on the precondition) with the `nanos < 10^9` spec and with the carry
//@ teeth: bound; its twin duration_new_nanos_carry_control verifies only under the carry bound.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::Duration;

#[ensures(result)]
pub fn new_carry_overflows() -> bool {
    let d = Duration::new(u64::MAX, 1_000_000_000);
    d >= Duration::from_secs(0)
}
