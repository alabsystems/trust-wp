//@ expect: reject
//@ mechanism: a loop-exit arm of the condition switch that reaches panic!() was a panic-arm obligation checked under the assumed loop condition (vacuous); no check and no switch after the loop
//@ accept-means: f(0) panics after the loop. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: regression guard — already rejected on 5becf6c8 (the in-loop return / panic tail is refused there on another path); review probe a13 (no check, no switch after the loop) verified on 785efec6
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } panic!() }
