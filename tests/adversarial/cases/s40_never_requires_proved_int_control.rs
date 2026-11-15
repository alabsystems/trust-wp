//@ expect: verify
//@ mechanism: int form of the contracted -> ! callee control; returning-path fact premises only the postcondition
//@ accept-means: n/a (control) — TRUE contracts, must keep verifying
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
pub fn die(x: i32) -> ! { loop {} }
#[ensures(x@ <= 0)]
pub fn f(x: i32) { if x > 0 { die(x) } }
