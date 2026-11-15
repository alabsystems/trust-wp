//@ expect: reject
//@ verdict: failed
//@ fn-failed: hop
//@ mechanism: the false half of the isolating pair for the contract-free bounds rule (D-95): the
//@ mechanism: clause-free host of contract_free_index_bounds_clausefree_control with its guard
//@ mechanism: weakened from `i < v.len()` to `i <= v.len()`, so `i == v.len()` reaches the index.
//@ mechanism: A discovery predicate blind to `Assert(BoundsCheck)` makes this body a target of
//@ mechanism: nothing; a cap that credited any walked bounds site without the lane's own
//@ mechanism: obligation would verify it. Only the charged and REFUTED goal `i < len` rejects it.
//@ accept-means: an index one past the end of a slice, on a path the guard admits, was examined by
//@ accept-means: nobody (or credited without its goal) and the crate reported a clean run
//@ fixed-by: D-95
//@ teeth: ACCEPTED (exit 0, `hop` named in no verdict line) before D-95; `hop(&[], 0)` panics
//@ teeth: with "index out of bounds" when compiled and run as a plain program.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub fn hop(v: &[u32], i: usize) -> u32 {
    if i <= v.len() { v[i] } else { 0 }
}
