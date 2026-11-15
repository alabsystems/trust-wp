//@ expect: reject
//@ mechanism: a primitive `==` over an f64 FIELD of a local struct (no `PartialEq` impl involved,
//@ mechanism: unlike sp22_derived_float_field.rs) is read as reflexive. The field can be NaN.
//@ accept-means: `field_eq(P { a: f64::NAN })` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`field_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct P {
    pub a: f64,
}

#[ensures(result)]
pub fn field_eq(p: P) -> bool {
    p.a == p.a
}
