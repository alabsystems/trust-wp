//@ expect: reject
//@ mechanism: an element read out of a `Vec<f64>` and compared with itself: the comparison is read
//@ mechanism: over the reals (or as logical equality), so it is reflexive. The element can be NaN.
//@ accept-means: `vec_elem_eq(vec![f64::NAN])` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`vec_elem_eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn vec_elem_eq(v: Vec<f64>) -> bool {
    if v.len() > 0 { v[0] == v[0] } else { true }
}
