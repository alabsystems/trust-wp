//@ expect: verify
//@ mechanism: control: the check before the trusted spin cannot fail under the arm guard
//@ accept-means: n/a (control) — `x + 1` with x < 0 cannot overflow; TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(result == x)]
pub fn f(x: i32) -> i32 { if x < 0 { let _y = x + 1; spin() } x }
