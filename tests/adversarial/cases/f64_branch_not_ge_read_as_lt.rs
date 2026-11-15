//@ expect: reject
//@ mechanism: a branch taken on a negated float comparison (`if !(x >= 10.0)`) carries that negation as
//@ mechanism: its path condition, and the arm then claims the complementary comparison (`x < 10.0`).
//@ mechanism: Over integers and reals the two are one fact; over IEEE-754 floats they are not, because
//@ mechanism: every ordered comparison with NaN is false: at NaN the arm is taken and `x < 10.0` is
//@ mechanism: false. The path-condition twin of f64_not_lt_read_as_ge.rs, whose complement is a value,
//@ mechanism: not a branch. f64_branch_not_ge_restated_control.rs restates the path condition itself and
//@ mechanism: i64_branch_not_ge_control.rs is the same body over `i64`.
//@ accept-means: `branch_not_ge(f64::NAN)` and `branch_not_lt_f32(f32::NAN)` return `false`; an accept
//@ accept-means: claims each returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED on the campaign tip before D-215 (`branch_not_ge verified`, `branch_not_lt_f32 verified`:
//@ teeth: the reals read the path condition as its complement); each FAILED (postcondition) under D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn branch_not_ge(x: f64) -> bool {
    if !(x >= 10.0) { x < 10.0 } else { true }
}

#[ensures(result)]
pub fn branch_not_lt_f32(x: f32) -> bool {
    if !(x < 1.0) { x >= 1.0 } else { true }
}
