//@ expect: reject
//@ mechanism: drop glue running a panicking user Drop::drop was not a panic site
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: a function holding a local whose Drop impl panics verified; it always panics on return.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

struct D;

impl Drop for D {
    fn drop(&mut self) {
        panic!("boom")
    }
}

#[ensures(result@ == x@)]
pub fn dropper(x: u8) -> u8 {
    let _d = D;
    x
}
