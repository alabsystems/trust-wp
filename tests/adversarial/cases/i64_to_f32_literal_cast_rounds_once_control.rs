//@ expect: verify
//@ mechanism: the control for i64_to_f32_literal_cast_double_rounded.rs: 2^60 + 2^36 + 1 as `f32` is
//@ mechanism: 2^60 + 2^37, the nearest `f32` to the integer itself.
//@ accept-means: n/a (control) — the function returns 2^60 + 2^37 in every execution.
//@ fixed-by: n/a (control)
//@ teeth: failed on the campaign tip before D-215 (the identity reading keeps the integer);
//@ teeth: verified after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 1152921642045800448.0f32)]
pub fn rounded_once() -> f32 {
    let v: i64 = 1152921573326323713;
    v as f32
}
