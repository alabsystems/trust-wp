//@ expect: reject
//@ mechanism: `*x + 0.0` stored back through a `&mut f64` is read as the identity over the reals, so
//@ mechanism: the final value is logically equal to the entry value. Round-to-nearest-even gives
//@ mechanism: `-0.0 + 0.0 == +0.0`, a different value from `-0.0`.
//@ accept-means: `add_zero(&mut -0.0)` leaves `+0.0`; an accept claims the final value is the entry value `-0.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`add_zero verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn add_zero(x: &mut f64) {
    *x = *x + 0.0;
}
