//@ expect: verify
//@ mechanism: control: loop-exit diverging tail checked condition-free
//@ accept-means: n/a (control) — requires x > 0 makes `x - 1` safe; TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[requires(x > 0i32)]
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = x - 1; spin() }
