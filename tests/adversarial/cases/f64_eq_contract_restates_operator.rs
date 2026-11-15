//@ expect: reject
//@ mechanism: a contract `==` is logical equality and the program's `==` is IEEE-754 equality; over
//@ mechanism: the reals they coincide, so a contract restating the operator verifies. They differ in
//@ mechanism: both directions: `NaN == NaN` is false in the program and true logically, and
//@ mechanism: `0.0 == -0.0` is true in the program and false logically.
//@ accept-means: `restated_eq(f64::NAN, f64::NAN)` returns `false` and `restated_eq(0.0, -0.0)` returns
//@ accept-means: `true`; an accept claims each returns the logical equality of its arguments.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`restated_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == (x == y))]
pub fn restated_eq(x: f64, y: f64) -> bool {
    x == y
}
