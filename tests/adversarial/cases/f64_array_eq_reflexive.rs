//@ expect: reject
//@ mechanism: an `[f64; N]` compares its elements with f64's IEEE-754 `eq`; the array comparison is
//@ mechanism: read as logical equality of the two values.
//@ accept-means: `array_eq([f64::NAN, 0.0])` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`array_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn array_eq(x: [f64; 2]) -> bool {
    x == x
}
