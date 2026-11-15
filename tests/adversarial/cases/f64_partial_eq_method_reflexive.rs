//@ expect: reject
//@ mechanism: `<f64 as PartialEq>::eq` resolves to the generic builtin `PartialEq::eq` contract
//@ mechanism: `result == (self@ == rhs@)`, which states logical equality. f64's `eq` is IEEE-754 equality,
//@ mechanism: false at NaN. The method-call spelling of f64_eq_reflexive_despite_nan.rs.
//@ accept-means: `eq_method(f64::NAN)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`eq_method verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn eq_method(x: f64) -> bool {
    x.eq(&x)
}
