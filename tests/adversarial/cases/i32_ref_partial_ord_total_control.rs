//@ expect: verify
//@ mechanism: the isolating twin of f64_ref_partial_ord_total_despite_nan.rs: over `&i32` the reference
//@ mechanism: impl's builtin contract is a total order and is admitted; only a float-carrying type loses it.
//@ accept-means: n/a (control) — `x <= y || x > y` holds for every pair of integers.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn ref_le_or_gt(x: &i32, y: &i32) -> bool {
    x <= y || x > y
}
