//@ expect: reject
//@ mechanism: `x + 0.0` is read as the identity over the reals, so the result is logically equal to
//@ mechanism: the parameter. Round-to-nearest-even gives `-0.0 + 0.0 == +0.0`, a different value
//@ mechanism: from `-0.0` under the contract's logical equality. The returned-value twin of
//@ mechanism: f64_mut_ref_add_zero_identity.rs, which stores the sum through a `&mut`.
//@ accept-means: `add_zero(-0.0)` returns `+0.0`; an accept claims it returns its argument `-0.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`add_zero verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn add_zero(x: f64) -> f64 {
    x + 0.0
}
