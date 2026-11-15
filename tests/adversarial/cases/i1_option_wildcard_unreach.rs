//@ expect: reject
//@ mechanism: otherwise-arm LetAssume circularity on an enum discriminant switch
//@ accept-means: a wildcard unreachable!() on Option was assumed unreachable. FALSE: f(None) panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r2)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(o: Option<i32>) -> i32 {
    match o {
        Some(v) => v,
        _ => unreachable!(),
    }
}
