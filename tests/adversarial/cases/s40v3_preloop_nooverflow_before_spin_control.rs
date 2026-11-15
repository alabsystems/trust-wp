//@ expect: verify
//@ mechanism: control: a check on the path to a trusted inert spin in a function with a loop was dropped by the block-slice walker (pre-loop slice)
//@ accept-means: n/a (control) — `x + 1` with x < 0 cannot overflow; TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { if x < 0 { let _y = x + 1; spin() } let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } }
