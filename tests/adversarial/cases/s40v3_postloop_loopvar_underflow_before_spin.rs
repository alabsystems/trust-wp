//@ expect: reject
//@ mechanism: a check on the path to a trusted inert spin in a function with a loop was dropped by the block-slice walker (post-loop slice, loop variable)
//@ accept-means: f(0) leaves the loop with i == 0 and computes `0u32 - 1` before spin(). FALSE.
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: new in v3 (post-loop slice)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } if i == 0 { let _y = i - 1; spin() } }
