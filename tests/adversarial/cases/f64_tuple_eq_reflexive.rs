//@ expect: reject
//@ mechanism: a tuple with an f64 component compares that component with f64's IEEE-754 `eq`; the
//@ mechanism: generic builtin `PartialEq::eq` contract reads the whole comparison as logical equality.
//@ accept-means: `tuple_eq((f64::NAN, 0))` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`tuple_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn tuple_eq(x: (f64, i32)) -> bool {
    x == x
}
