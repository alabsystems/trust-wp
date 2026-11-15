//@ expect: reject
//@ mechanism: sequential loops: the second loop's user invariant `x > 0` (established by `x = 5`) was pooled into loop 0's exit-tail check `x - 1` on the earlier `x`
//@ accept-means: f(i32::MIN, 0) computes `i32::MIN - 1`, which overflows. FALSE.
//@ fixed-by: wp-s40 loop-invariant-pooling-v5
//@ teeth: verified (false accept) on 232542f7, the merged wp-campaign + v4 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(y: i32, n: u32) { let mut x: i32 = y; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _w = x - 1; x = 5; #[invariant(x > 0i32)] loop { } }
