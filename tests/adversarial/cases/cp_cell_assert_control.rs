//@ expect: verify
//@ mechanism: interior-mutable write rule in the proof_assert substitution lane —
//@ mechanism: over-refusal control for cp_cell_conflate_assert.rs. A call through a
//@ mechanism: `&Cell` may not havoc facts about values that are NOT interior-mutable:
//@ mechanism: `n: u8` keeps its precondition across `c.set(n)`.
//@ fixed-by: s63 (wp-s63) — control, nothing to fix
//@ accept-means: n/a (control) — claims nothing about the cell contents.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

#[requires(n < 10u8)]
#[ensures(true)]
pub fn cell_assert_ok(c: &Cell<u8>, n: u8) {
    c.set(n);
    proof_assert!(n < 10u8);
}
