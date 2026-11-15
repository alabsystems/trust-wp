//@ expect: verify
//@ mechanism: the integer twin of f64_branch_not_ge_read_as_lt.rs: over `i64` and `i32`, `!(x >= 10)`
//@ mechanism: IS `x < 10`, so the arm's claim is the path condition it was taken on.
//@ accept-means: n/a (control) — for every integer, `!(x >= 10)` implies `x < 10`.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (each function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn branch_not_ge(x: i64) -> bool {
    if !(x >= 10) { x < 10 } else { true }
}

#[ensures(result)]
pub fn branch_not_lt_i32(x: i32) -> bool {
    if !(x < 1) { x >= 1 } else { true }
}
