//@ expect: reject
//@ mechanism: otherwise-arm LetAssume circularity, unit-returning function
//@ accept-means: a wildcard panic!() arm was assumed unreachable. FALSE: f(1) panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r5)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: u8) {
    match x {
        0 => {}
        _ => panic!(),
    }
}
