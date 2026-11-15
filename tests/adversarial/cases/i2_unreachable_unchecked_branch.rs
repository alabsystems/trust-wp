//@ expect: reject
//@ mechanism: core::hint::unreachable_unchecked (creusot-std: requires(false)) was not an obligation
//@ accept-means: a reachable unreachable_unchecked (UB) was assumed unreachable. FALSE: f(0) is UB.
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
        unsafe { std::hint::unreachable_unchecked() }
    }
}
