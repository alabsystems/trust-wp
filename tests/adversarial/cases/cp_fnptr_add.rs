//@ expect: reject
//@ mechanism: operator call through a fn pointer resolved to a precondition-free fallback
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `f(x, 1)` with `f = <u8 as Add>::add` verified; it panics for x = 255.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn fnptr(x: u8) -> u8 {
    let f: fn(u8, u8) -> u8 = <u8 as core::ops::Add>::add;
    f(x, 1)
}
