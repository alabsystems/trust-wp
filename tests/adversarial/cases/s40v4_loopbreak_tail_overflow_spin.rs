//@ expect: reject
//@ mechanism: body-break loop: the break arm's diverging tail was checked under the assumed continuation condition `!(i >= n)` (vacuous)
//@ accept-means: f(i32::MIN, 0) overflows `x - 1` after the break. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: verified (false accept) on 5becf6c8, the merged wp-campaign + v3 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] loop { if i >= n { break; } i += 1; } let _y = x - 1; spin() }
