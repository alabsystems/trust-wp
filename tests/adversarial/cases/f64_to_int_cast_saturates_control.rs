//@ expect: verify
//@ mechanism: `as` from a float to an integer truncates toward zero, saturates at the target's bounds and
//@ mechanism: maps NaN to 0. Over constants the model decides each by Rust's own conversion.
//@ accept-means: n/a (control) — `300.0 as u8` is 255, `-1.5 as u8` is 0, `NaN as i32` is 0 and
//@ accept-means: `-2.7 as i32` is -2 in every execution.
//@ fixed-by: n/a (control)
//@ teeth: unknown on the commit before D-215 (the real-number lowering reads NaN as no value and its
//@ teeth: floor is not certified); verified after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 255)]
pub fn saturates_high() -> u8 {
    let big = 300.0f64;
    big as u8
}

#[ensures(result == 0)]
pub fn saturates_low() -> u8 {
    let neg = -1.5f64;
    neg as u8
}

#[ensures(result == 0)]
pub fn nan_is_zero() -> i32 {
    let n = f64::NAN;
    n as i32
}

#[ensures(result == -2)]
pub fn truncates_toward_zero() -> i32 {
    let x = -2.7f32;
    x as i32
}
