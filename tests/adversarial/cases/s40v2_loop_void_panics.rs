//@ expect: reject
//@ mechanism: an uninhabited-return panicking call inside a loop body was assumed away
//@ accept-means: die() panics and f(1, 0) reaches it. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: verified on 8147c10d (s40 review probe q21)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Void {}
pub fn die() -> Void { panic!() }
#[ensures(true)]
pub fn f(n: u32, x: i32) { let mut i = 0u32; #[invariant(i <= n)] while i < n { if x <= 0 { die(); } i += 1; } }
