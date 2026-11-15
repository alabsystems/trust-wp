//@ expect: reject
//@ mechanism: a -> ! call with target None bailed extraction before its precondition was emitted
//@ accept-means: f(0) calls die(0) although die requires x > 0. FALSE.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
//@ also-verified: die
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
pub fn die(x: i32) -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32) -> i32 { die(x) }
