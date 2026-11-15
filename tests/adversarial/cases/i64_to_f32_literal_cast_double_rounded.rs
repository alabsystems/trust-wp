//@ expect: reject
//@ mechanism: `as` from an integer to `f32` rounds the integer once, to nearest-even. Rounding it to
//@ mechanism: `f64` first and then to `f32` lands 2^60 + 2^36 + 1 on the tie 2^60 + 2^36 and then on
//@ mechanism: 2^60, where the single rounding gives 2^60 + 2^37. Pins the host fold of a literal cast.
//@ accept-means: `double_rounded()` returns 2^60 + 2^37; an accept claims it returns 2^60.
//@ fixed-by: D-215
//@ teeth: rejected on the campaign tip before D-215 too (its identity reading of the cast claims
//@ teeth: the integer itself); rejected after, by the fold.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 1152921504606846976.0f32)]
pub fn double_rounded() -> f32 {
    let v: i64 = 1152921573326323713;
    v as f32
}
