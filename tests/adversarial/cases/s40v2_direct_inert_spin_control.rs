//@ expect: verify
//@ mechanism: a local inert -> ! spin called directly under a caller precondition; continuation unreachable
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[requires(x >= 0i32)]
#[ensures(result == x)]
pub fn f(x: i32) -> i32 { if x < 0 { spin() } x }
