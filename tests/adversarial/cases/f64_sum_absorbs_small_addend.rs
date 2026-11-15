//@ expect: reject
//@ mechanism: the rounding twin of f64_add_one_exceeds_despite_rounding.rs with every operand finite and
//@ mechanism: constant: over the reals `1e16 + 1.0` differs from `1e16`, while round-to-nearest-even
//@ mechanism: absorbs the addend. No NaN or infinity is involved.
//@ accept-means: `absorbs()` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`absorbs verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn absorbs() -> bool {
    let big = 1.0e16f64;
    let sum = big + 1.0;
    sum != big
}
