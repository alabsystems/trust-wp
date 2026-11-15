//@ expect: reject
//@ mechanism: a check on the path to a trusted inert spin in a function with a loop was dropped by the block-slice walker (post-loop slice)
//@ accept-means: f(i32::MIN, 0) overflows `x - 1` after the loop, before spin(). FALSE.
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: verified on d8875165 (s40 v3 probe r31/r36)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } if x < 0 { let _y = x - 1; spin() } }
