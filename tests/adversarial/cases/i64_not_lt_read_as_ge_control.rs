//@ expect: verify
//@ mechanism: the control for f64_not_lt_read_as_ge.rs: the same body over `i64`, where `!(x < y)` is
//@ mechanism: `x >= y` for every pair, so the only difference between the two files is the float.
//@ accept-means: n/a (control) — both functions return `true` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: verified on the campaign tip before D-215 and after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn lt_complement_is_ge(x: i64, y: i64) -> bool {
    !(x < y) == (x >= y)
}

#[ensures(result)]
pub fn le_complement_is_gt(x: i64, y: i64) -> bool {
    !(x <= y) == (x > y)
}
