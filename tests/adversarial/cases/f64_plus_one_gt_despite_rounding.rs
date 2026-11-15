//@ expect: reject
//@ mechanism: an `f64` reaches the solver as a real number, so `x + 1.0 > x` reads as a tautology.
//@ mechanism: Rust adds floats by IEEE-754 and rounds: `1e16 + 1.0 == 1e16`. NaN is excluded by the
//@ mechanism: first disjunct (`!(NaN >= 0.0)` is true), so this is the rounding twin of the NaN
//@ mechanism: cases f64_eq_reflexive_despite_nan.rs and f64_le_or_gt_total_despite_nan.rs, which the
//@ mechanism: corpus held alone.
//@ fixed-by: D-215 — `+` over an `f64` is `fp.add` rounded to nearest-even.
//@ accept-means: `plus_one_gt(1e16)` returns `false`; an accept claims it returns `true`.
//@ teeth: ACCEPTED (`plus_one_gt verified`), with and without D-142. Rejected under D-215: FAILED
//@ teeth: (postcondition), or between runs of one binary `unknown` (a refutation withheld for missing
//@ teeth: solver provenance). The twin f64_plus_one_ge_despite_rounding_control.rs differs in `>=` and is
//@ teeth: true.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn plus_one_gt(x: f64) -> bool {
    !(x >= 0.0) || x + 1.0 > x
}
