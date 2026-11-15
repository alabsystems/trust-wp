//@ expect: verify
//@ mechanism: the integer twin of f64_ghost_block_comparison_read_over_reals.rs: over `i64`, `x == x`,
//@ mechanism: `x + 0 == x` and `x <= y || x > y` hold, so each ghost value asserted is true.
//@ accept-means: n/a (control) — each assertion holds for every integer.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (each `proof_assert` and function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn ghost_self_eq(x: i64) {
    let g: Ghost<bool> = ghost!(x == x);
    proof_assert!(*g);
}

#[ensures(true)]
pub fn ghost_add_zero(x: i64) {
    let g: Ghost<i64> = ghost!(x + 0);
    proof_assert!(*g == x);
}

#[ensures(true)]
pub fn ghost_total(x: i64, y: i64) {
    let g: Ghost<bool> = ghost!(x <= y || x > y);
    proof_assert!(*g);
}
