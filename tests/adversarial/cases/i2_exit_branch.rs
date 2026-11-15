//@ expect: reject
//@ mechanism: std::process::exit was not a panic entry point; the arm was assumed unreachable
//@ accept-means: a reachable exit was assumed unreachable. FALSE: f(0) exits without returning.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: not measured before fix (same mechanism as i2_abort_branch)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: i32) {
    if x <= 0 {
        std::process::exit(1)
    }
}
