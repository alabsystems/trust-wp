//@ expect: reject
//@ mechanism: `Option<f64> == Option<f64>` is described by the generic builtin `PartialEq::eq`
//@ mechanism: contract as logical equality, but `Option`'s `eq` compares the payloads with f64's IEEE-754
//@ mechanism: `eq`, so `Some(NaN) == Some(NaN)` is false.
//@ accept-means: `option_eq(Some(f64::NAN))` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`option_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn option_eq(x: Option<f64>) -> bool {
    x == x
}
