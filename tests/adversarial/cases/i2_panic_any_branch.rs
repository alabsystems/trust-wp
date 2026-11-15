//@ expect: reject
//@ mechanism: is_panic_entry_point matched only panicking::* and rt::begin_panic, so std::panic::panic_any was a non-panic divergence (assumed unreachable)
//@ accept-means: a reachable panic_any was assumed unreachable. FALSE: f(0) panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe p04)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: i32) {
    if x <= 0 {
        std::panic::panic_any(0u32);
    }
}
