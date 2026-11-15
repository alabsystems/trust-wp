//@ expect: reject
//@ mechanism: nested loops with an inner return: post-inner-loop diverging arm
//@ accept-means: f(i32::MIN, 3): i never reaches 3 (n == 3 exits first), so j == 2 reaches `x - 1`. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: regression guard — already rejected on 5becf6c8 (the in-loop return / panic tail is refused there on another path); review probe a09 verified on 785efec6
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32, n: u32) { let mut j: u32 = 0; #[invariant(j <= n)] while j < n { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { if i == 3 { return; } i += 1; } if j == 2 { let _y = x - 1; spin() } j += 1; } }
