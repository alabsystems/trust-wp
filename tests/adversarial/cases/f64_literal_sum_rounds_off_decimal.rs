//@ expect: reject
//@ mechanism: an operator over two float literals is folded on the host, and the fold must be Rust's
//@ mechanism: IEEE-754 arithmetic: `0.1 + 0.2` rounds to `0.30000000000000004`, which is not the `f64`
//@ mechanism: nearest `0.3`. Decimal arithmetic on the literals as written makes the sum `0.3`.
//@ accept-means: `sum()` returns `0.30000000000000004`; an accept claims it returns `0.3`.
//@ fixed-by: D-215
//@ teeth: rejected on the campaign tip before D-215 as well: the exact real sum of the two literals'
//@ teeth: binary values is neither `0.3` nor its rounding. It pins the fold, beside its control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0.3)]
pub fn sum() -> f64 {
    0.1 + 0.2
}
