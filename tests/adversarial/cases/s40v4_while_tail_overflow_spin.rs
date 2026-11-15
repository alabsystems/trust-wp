//@ expect: reject
//@ mechanism: the loop lane walked a loop-exit tail that must diverge but checked it under the ASSUMED loop condition, so `!cond ==> check` was vacuous; the post-loop slice skipped it as the loop lane's (no switch after the loop)
//@ accept-means: f(i32::MIN, 0) overflows `x - 1` after the loop, before spin(). FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: verified (false accept) on 5becf6c8, the merged wp-campaign + v3 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = x - 1; spin() }
