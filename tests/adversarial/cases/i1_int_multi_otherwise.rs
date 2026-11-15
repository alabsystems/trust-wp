//@ expect: reject
//@ mechanism: otherwise-arm LetAssume circularity with two surviving valued arms
//@ accept-means: a wildcard unreachable!() was assumed unreachable. FALSE: f(2) panics although 2 < 5.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe p10b)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 5)]
#[ensures(result@ >= 1)]
pub fn f(x: u8) -> u8 {
    match x {
        0 => 1,
        1 => 2,
        _ => unreachable!(),
    }
}
