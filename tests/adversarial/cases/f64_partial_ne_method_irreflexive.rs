//@ expect: reject
//@ mechanism: `<f64 as PartialEq>::ne` resolves to the generic builtin `PartialEq::ne` contract, the
//@ mechanism: negation of logical equality. f64's `ne` is true at NaN.
//@ accept-means: `ne_method(f64::NAN)` returns `true`; an accept claims it returns `false`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`ne_method verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!result)]
pub fn ne_method(x: f64) -> bool {
    x.ne(&x)
}
