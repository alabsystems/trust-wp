//@ expect: reject
//@ mechanism: otherwise arm (v=None) with a panic obligation was dropped from the surviving-arm LetAssume disjunction; the hoisted {x==0} discharged !(x!=0) circularly
//@ accept-means: an otherwise-arm unreachable!() was assumed unreachable. FALSE: f(1) panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r1)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 5)]
#[ensures(true)]
pub fn f(x: u8) -> u8 {
    match x {
        0 => 1,
        _ => unreachable!(),
    }
}
