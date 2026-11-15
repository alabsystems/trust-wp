//@ expect: reject
//@ mechanism: call through a fn pointer owes its target's precondition
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `f(x)` with `f = pos` (requires x > 0) verified without any fact on x.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
//@ also-verified: pos
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ > 0)]
#[ensures(result == x)]
pub fn pos(x: u8) -> u8 {
    x
}

#[ensures(true)]
pub fn via_ptr(x: u8) -> u8 {
    let f: fn(u8) -> u8 = pos;
    f(x)
}
