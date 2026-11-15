//@ expect: reject
//@ mechanism: a diverging call through a fn pointer had no DefId, so the arm got the surviving-path treatment
//@ accept-means: die() panics and f(0) reaches it through d. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: verified on 8147c10d (s40 review probe p07)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn die() -> ! { panic!() }
#[ensures(true)]
pub fn f(x: i32) { let d: fn() -> ! = die; if x <= 0 { d() } }
