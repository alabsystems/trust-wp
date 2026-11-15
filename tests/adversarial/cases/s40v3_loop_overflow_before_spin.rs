//@ expect: reject
//@ mechanism: a check on the path to a trusted inert spin was dropped with the arm (block_reaches_panic_call never follows the assert-failure edge) (loop lane)
//@ accept-means: f(1) enters the loop with i == 0 and computes `0u32 - 1`. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: verified on 51d9d0b1 (s40 v2 review probes r18/r21/r22/r26-r29)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { if i == 0 { let _z = i - 1; spin() } i += 1; } }
