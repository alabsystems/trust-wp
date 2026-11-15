//@ expect: verify
//@ mechanism: the control for f64_double_then_halve_overflows.rs: at `f64::MAX` the doubling overflows to
//@ mechanism: infinity, so the round trip does not return `f64::MAX`. Rust's own arithmetic decides it.
//@ accept-means: n/a (control) — the function returns `false` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: failed on the campaign tip before D-215 (a counterexample from exact real arithmetic);
//@ teeth: verified after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!result)]
pub fn max_round_trips() -> bool {
    let big = f64::MAX;
    big * 2.0 / 2.0 == big
}
