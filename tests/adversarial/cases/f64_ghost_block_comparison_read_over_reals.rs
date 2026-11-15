//@ expect: reject
//@ mechanism: a float comparison or sum computed inside `ghost!` and asserted through the ghost value.
//@ mechanism: Ghost code is program code: `ghost!(x == x)` runs the IEEE comparison (false at NaN) and
//@ mechanism: `ghost!(x + 0.0)` the IEEE sum (`+0.0` at `x == -0.0`), unlike a snapshot, whose body is a
//@ mechanism: logical term. Over the reals each `proof_assert!` holds. The ghost lane's twin of the
//@ mechanism: postcondition cases D-215 lists; i64_ghost_block_comparison_control.rs is the same bodies
//@ mechanism: over `i64`.
//@ accept-means: `ghost_self_eq(f64::NAN)` and `ghost_total(f64::NAN, 0.0)` hold a ghost `false`, and
//@ accept-means: `ghost_add_zero(-0.0)` holds a ghost `+0.0`, logically unequal to `x`; an accept claims
//@ accept-means: each assertion true.
//@ fixed-by: D-215
//@ teeth: ACCEPTED at the merged campaign tip before D-215 (each `proof_assert` and function verified);
//@ teeth: under D-215 `ghost_self_eq` and `ghost_add_zero` are FAILED (proof_assert) and `ghost_total`
//@ teeth: is `unknown`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn ghost_self_eq(x: f64) {
    let g: Ghost<bool> = ghost!(x == x);
    proof_assert!(*g);
}

#[ensures(true)]
pub fn ghost_add_zero(x: f64) {
    let g: Ghost<f64> = ghost!(x + 0.0);
    proof_assert!(*g == x);
}

#[ensures(true)]
pub fn ghost_total(x: f64, y: f64) {
    let g: Ghost<bool> = ghost!(x <= y || x > y);
    proof_assert!(*g);
}
