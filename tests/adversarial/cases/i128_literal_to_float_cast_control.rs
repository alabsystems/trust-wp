//@ expect: verify
//@ mechanism: an `i128` literal cast to a float is folded on the host like any narrower one. The range
//@ mechanism: check of the fold computed `-(1 << 127)`, which overflows, so the debug driver panicked on
//@ mechanism: the function and verified nothing.
//@ accept-means: n/a (control) — `5i128 as f64` is `5.0` and `-7i128 as f32` equals `-7.0f32` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: measured on `5i128 as f64 == 5.0` and `7i128 as f32 == 7.0f32` as postconditions: verified on
//@ teeth: the campaign tip before D-215; under D-215's fold without its 128-bit arm the debug driver
//@ teeth: panicked (`attempt to negate with overflow`) on each; with the arm this file verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 5.0)]
pub fn i128_to_f64() -> f64 {
    let v: i128 = 5;
    v as f64
}

#[ensures(result)]
pub fn i128_to_f32() -> bool {
    let v: i128 = -7;
    v as f32 == -7.0f32
}
