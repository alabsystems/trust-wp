//@ expect: reject
//@ mechanism: otherwise-arm LetAssume circularity on a 3-variant user enum
//@ accept-means: a wildcard panic!() arm was assumed unreachable. FALSE: f(E::C) panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r3)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E {
    A,
    B,
    C,
}

#[ensures(result@ >= 1)]
pub fn f(e: E) -> u8 {
    match e {
        E::A => 1,
        E::B => 2,
        _ => panic!(),
    }
}
