//@ expect: reject
//@ mechanism: an `f64` written inside a loop body and compared with itself after the loop is read
//@ mechanism: through the loop-effect lane, where it is a real number, so `y == y` holds. `y` stays
//@ mechanism: NaN when the input is NaN (`NaN + 0.0` is NaN) and IEEE-754 `NaN == NaN` is false.
//@ mechanism: The loop-carried spelling of f64_eq_reflexive_despite_nan.rs.
//@ accept-means: `loop_self_eq(f64::NAN)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`loop_self_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn loop_self_eq(x: f64) -> bool {
    let mut y = x;
    let mut i = 0;
    #[invariant(i <= 1)]
    while i < 1 {
        y = y + 0.0;
        i += 1;
    }
    y == y
}
