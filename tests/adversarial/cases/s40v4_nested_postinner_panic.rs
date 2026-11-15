//@ expect: reject
//@ mechanism: nested loops: false stable invariant `j == 0` discharged a post-inner-loop panic arm
//@ accept-means: f(3) panics with j == 2. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: verified (false accept) on 5becf6c8, the merged wp-campaign + v3 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) { let mut j: u32 = 0; #[invariant(j <= n)] while j < n { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } if j == 2 { panic!() } j += 1; } }
