//@ expect: reject
//@ mechanism: the `else` arm of `x == x` is reached only by NaN, and the reals have none, so the arm is
//@ mechanism: read as dead and nothing it computes is examined. Under IEEE-754 it runs, and `NaN as i32`
//@ mechanism: is `0`, so the arm returns `2`.
//@ accept-means: `one(f64::NAN)` returns `2`; an accept claims it returns `1`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`one verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 1)]
pub fn one(x: f64) -> i32 {
    if x == x { 1 } else { x as i32 + 2 }
}
