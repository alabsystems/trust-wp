//@ expect: reject
//@ mechanism: `<f64 as PartialOrd>::lt` and `::ge` resolve to the generic builtin contracts
//@ mechanism: `result == (self@ < rhs@)` and `result == (self@ >= rhs@)`, read as a total order. Both are
//@ mechanism: false when either operand is NaN. The method-call spelling of f64_le_or_gt_total_despite_nan.rs.
//@ accept-means: `lt_or_ge(f64::NAN, 0.0)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`lt_or_ge verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn lt_or_ge(x: f64, y: f64) -> bool {
    x.lt(&y) || x.ge(&y)
}
