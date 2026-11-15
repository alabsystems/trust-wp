//@ expect: verify
//@ mechanism: control for the division-by-zero obligation family: a divisor with an explicit
//@ mechanism: `#[requires]` excluding 0 (and MIN/-1) must still verify.
//@ WHY THE PROGRAM IS RIGHT: under `d@ != 0 && d@ != -1` neither the DivisionByZero assert nor
//@ WHY THE PROGRAM IS RIGHT: the signed MIN/-1 overflow assert can fire.
//@ teeth: verifies at campaign 03a35447 (wp-s58 probe p4, 2026-09-14) — an over-refusal here is
//@ teeth: a regression in the arithmetic-obligation lane.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(d@ != 0)]
#[requires(d@ != -1)]
#[ensures(true)]
pub fn f(n: i32, d: i32) -> i32 {
    n / d
}
