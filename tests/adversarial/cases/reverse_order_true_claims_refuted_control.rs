//@ expect: verify
//@ xfail: the true claims about `Reverse` are refuted, because its comparisons are read as the inner
//@ xfail: values' order (reverse_order_read_as_inner_order.rs, whose false claims verify). An XPASS with
//@ xfail: that case rejecting is the signal that `Reverse` is ordered as Rust orders it.
//@ mechanism: control: with `x < y`, `Reverse(x) > Reverse(y)` holds and `Reverse(x) < Reverse(y)` does not.
//@ accept-means: n/a (control)
//@ fixed-by: OPEN (see reverse_order_read_as_inner_order.rs)
//@ teeth: n/a (over-refusal control; MEASURED as `rev_gt FAILED ✗ (postcondition)` and
//@ teeth: `rev_lt_never_panics FAILED ✗ (postcondition)`, when committed and on the campaign tip)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cmp::Reverse;

#[requires(x@ < y@)]
#[ensures(result)]
pub fn rev_gt(x: i32, y: i32) -> bool {
    Reverse(x) > Reverse(y)
}

#[requires(x@ < y@)]
pub fn rev_lt_never_panics(x: i64, y: i64) {
    if Reverse(x) < Reverse(y) {
        panic!();
    }
}
