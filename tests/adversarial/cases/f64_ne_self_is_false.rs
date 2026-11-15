//@ expect: reject
//@ mechanism: `x != x` over an f64 is read as the negation of real equality, which is never true.
//@ mechanism: Under IEEE-754 `NaN != NaN` is true. The `!=` twin of f64_eq_reflexive_despite_nan.rs.
//@ accept-means: `ne_self(f64::NAN)` returns `true`; an accept claims it returns `false`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`ne_self verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!result)]
pub fn ne_self(x: f64) -> bool {
    x != x
}
