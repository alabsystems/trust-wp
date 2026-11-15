//@ expect: reject
//@ mechanism: loop-exit diverging tail checked under the assumed loop condition (vacuous), with an in-loop return
//@ accept-means: f(i32::MIN, 0) overflows `x - 1` after the loop. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: regression guard — already rejected on 5becf6c8 (the in-loop return / panic tail is refused there on another path); review probe a01 verified on 785efec6
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { if i == 7 { return; } i += 1; } let _y = x - 1; spin() }
