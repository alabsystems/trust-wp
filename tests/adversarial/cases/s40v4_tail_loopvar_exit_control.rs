//@ expect: verify
//@ mechanism: control: loop-exit diverging tail checked condition-free but under the exit guard
//@ accept-means: n/a (control) — at exit i == n, so `n - i` cannot underflow; TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = n - i; spin() }
