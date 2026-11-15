//@ expect: reject
//@ mechanism: an extern "C" -> ! function with no contract got the user -> ! surviving-path treatment
//@ accept-means: a reachable contract-free extern abort was assumed unreachable. FALSE: f(0) aborts.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

unsafe extern "C" { fn abort() -> !; }
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { unsafe { abort() } } }
