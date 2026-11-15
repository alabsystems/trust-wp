//@ expect: reject
//@ mechanism: loop-exit tail `x - 1; panic!()` checked under the assumed loop condition
//@ accept-means: f(0, 0) panics after the loop. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: regression guard — already rejected on 5becf6c8 (the in-loop return / panic tail is refused there on another path); review probe a13 (without the in-loop return) verified on 785efec6
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = x - 1; panic!() }
