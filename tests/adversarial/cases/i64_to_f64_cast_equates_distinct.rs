//@ expect: reject
//@ ay-not-unsat: same_float
//@ mechanism: `as` from `i64` to `f64` rounds to nearest-even, so distinct integers above 2^53 convert to
//@ mechanism: one float. A model that reads the cast as the identity concludes the integers are equal
//@ mechanism: whenever their conversions are.
//@ accept-means: `same_float(9007199254740992, 9007199254740993)` returns `true` (both convert to
//@ accept-means: 2^53), and the two integers differ; an accept claims the result implies they are equal.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`same_float verified`) on the campaign tip before D-215, which read the cast as the
//@ teeth: identity; rejected after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result ==> x == y)]
pub fn same_float(x: i64, y: i64) -> bool {
    x as f64 == y as f64
}
