//@ expect: reject
//@ mechanism: an `f64` reaches the solver as a real number, and the reals have no NaN, so `x == x`
//@ mechanism: reads as reflexive. Rust compares floats by IEEE-754, under which `NaN == NaN` is
//@ mechanism: false; Creusot reads the same comparison through Why3's IEEE floats and does not prove
//@ mechanism: it. sp22_derived_float_field.rs guards the derived-`PartialEq` spelling of this; the
//@ mechanism: primitive operator was never excluded.
//@ accept-means: `eq_self(f64::NAN)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`eq_self verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn eq_self(x: f64) -> bool {
    x == x
}
