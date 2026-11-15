//@ expect: verify
//@ mechanism: the control for f64_ne_self_is_false.rs: `NaN != NaN` over the NaN constant has one IEEE-754
//@ mechanism: answer, `true`, and the IEEE model decides it by Rust's own comparison of the two constants.
//@ accept-means: n/a (control) — `n != n` is `true` for `n = f64::NAN`.
//@ fixed-by: n/a (control)
//@ teeth: verified beside its RED twin; an IEEE model that read a NaN constant as a number would not.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn nan_ne_nan() -> bool {
    let n = f64::NAN;
    n != n
}
