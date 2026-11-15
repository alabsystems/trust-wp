//@ expect: verify
//@ mechanism: control: body-break exit tail checked condition-free under the break guard
//@ accept-means: n/a (control) — at the break i >= n and i <= n, so `n - i` cannot underflow; TRUE contract
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] loop { if i >= n { break; } i += 1; } let _y = n - i; spin() }
