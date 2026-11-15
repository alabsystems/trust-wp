//@ expect: verify
//@ mechanism: the isolating twin of f64_branch_not_ge_read_as_lt.rs: the same branches, each arm claiming
//@ mechanism: its own path condition as written (`!(x >= 10.0)`, `!(x < 1.0)`) rather than the
//@ mechanism: complementary comparison. Only the claim's spelling differs, and the two spellings differ
//@ mechanism: only at NaN.
//@ accept-means: n/a (control) — an arm taken on `!(x >= 10.0)` has `!(x >= 10.0)`.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (each function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn branch_not_ge(x: f64) -> bool {
    if !(x >= 10.0) { !(x >= 10.0) } else { true }
}

#[ensures(result)]
pub fn branch_not_lt_f32(x: f32) -> bool {
    if !(x < 1.0) { !(x < 1.0) } else { true }
}
