//@ expect: reject
//@ mechanism: a contract-free local -> ! fn whose body can fail an assert got the surviving-path treatment
//@ accept-means: die(x) panics for x <= 0 and f(0) calls it. FALSE.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn die(x: i32) -> ! { assert!(x > 0); loop {} }
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { die(x) } }
