//@ expect: reject
//@ mechanism: outer loop-exit diverging tail after nested loops checked under the assumed outer condition
//@ accept-means: f(i32::MIN, 0) overflows `x - 1` after both loops. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: verified (false accept) on 5becf6c8, the merged wp-campaign + v3 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut j: u32 = 0; #[invariant(j <= n)] while j < n { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } j += 1; } let _y = x - 1; spin() }
