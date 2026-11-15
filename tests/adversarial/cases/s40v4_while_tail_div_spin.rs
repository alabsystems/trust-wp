//@ expect: reject
//@ mechanism: loop-exit diverging tail (division) checked under the assumed loop condition
//@ accept-means: f(1, 0, 0) divides by zero after the loop. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: verified (false accept) on 5becf6c8, the merged wp-campaign + v3 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: u32, d: u32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = x / d; spin() }
