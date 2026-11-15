//@ expect: reject
//@ mechanism: `<=` and `>` between two `&f64` call the library's reference impl
//@ mechanism: `<&f64 as PartialOrd>::le` / `::gt`, which resolve to the generic builtin contracts
//@ mechanism: `result == (self@ <= rhs@)` / `result == (self@ > rhs@)`, a total order. Both comparisons
//@ mechanism: are false when either pointee is NaN. The reference-operand twin of
//@ mechanism: f64_partial_ord_methods_total.rs, whose receiver is the `f64` itself.
//@ accept-means: `ref_le_or_gt(&f64::NAN, &0.0)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`ref_le_or_gt verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn ref_le_or_gt(x: &f64, y: &f64) -> bool {
    x <= y || x > y
}
