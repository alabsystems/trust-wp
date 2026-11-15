//@ expect: reject
//@ mechanism: the f32 twin of f64_eq_reflexive_despite_nan.rs: an `f32` reaches the solver as a real
//@ mechanism: number too, so `x == x` reads as reflexive although `NaN == NaN` is false.
//@ accept-means: `eq_self(f32::NAN)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`eq_self verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn eq_self(x: f32) -> bool {
    x == x
}
