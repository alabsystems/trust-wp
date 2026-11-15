//@ expect: reject
//@ mechanism: floats reach the solver as real numbers, and a narrowing `f64 as f32` is read as the
//@ mechanism: identity, so `(x as f32) as f64 == x` reads as a tautology. In IEEE-754 the cast rounds
//@ mechanism: to the nearest `f32`: `0.1f64 as f32 as f64` is `0.10000000149011612`. The cast
//@ mechanism: spelling of f64_eq_reflexive_despite_nan.rs and f64_plus_one_gt_despite_rounding.rs.
//@ fixed-by: D-215 — `as` between the two formats is `fp.to_fp` rounded to nearest-even.
//@ accept-means: `roundtrip(0.1)` returns `false`; an accept claims it returns `true`.
//@ WHY THE CONTRACT IS FALSE: `roundtrip(0.1) == false`.
//@ teeth: ACCEPTED (`roundtrip verified`), with and without D-142 (a contracted body
//@ teeth: is never capped); FAILED (postcondition) under D-215. The twin f64_to_f32_cast_exact_control.rs
//@ teeth: casts a value `f32` holds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x == 0.1)]
#[ensures(result)]
pub fn roundtrip(x: f64) -> bool {
    (x as f32) as f64 == x
}
