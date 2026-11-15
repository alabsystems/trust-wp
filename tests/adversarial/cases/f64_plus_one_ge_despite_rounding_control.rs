//@ expect: verify
//@ xfail: ay's floating-point path does not decide a query that needs a float variable's value, and
//@ xfail: answers `timeout`; D-215 names this price. The reals proved it before D-215.
//@ xfail-verdict: unknown
//@ mechanism: twin of f64_plus_one_gt_despite_rounding.rs: rounding to nearest is monotone, so
//@ mechanism: `x + 1.0 >= x` holds for every `f64` with `x >= 0.0`, and NaN meets the first disjunct.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn plus_one_ge(x: f64) -> bool {
    !(x >= 0.0) || x + 1.0 >= x
}
