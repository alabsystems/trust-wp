//@ expect: reject
//@ mechanism: drop glue of a generic struct instantiated with a panicking Drop type
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: a local `W { t: D }` whose field's Drop panics verified.
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

struct W<T> {
    t: T,
}

#[ensures(result@ == x@)]
pub fn dg(x: u8) -> u8 {
    let _w = W { t: D };
    x
}
