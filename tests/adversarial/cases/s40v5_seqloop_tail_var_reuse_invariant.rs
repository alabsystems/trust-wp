//@ expect: reject
//@ mechanism: sequential loops: the second loop's TRUE-at-its-header invariant `i == 0` (after `i = 0`) was pooled into loop 0's exit-tail check about the pre-reset `i`
//@ accept-means: f(100) overflows `10u32 - i` before `i = 0`. FALSE.
//@ fixed-by: wp-s40 loop-invariant-pooling-v5
//@ teeth: verified (false accept) on 232542f7, the merged wp-campaign + v4 pre-change build (A/B 2026-09-13)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = 10u32 - i; i = 0; #[invariant(i == 0u32)] loop { } }
