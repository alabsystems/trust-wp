//@ expect: reject
//@ mechanism: std::process::abort was not a panic entry point; the arm was assumed unreachable
//@ accept-means: a reachable abort was assumed unreachable. FALSE: f(0) aborts.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r8)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: i32) {
    if x <= 0 {
        std::process::abort()
    }
}
