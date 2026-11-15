//@ expect: verify
//@ mechanism: panic_any made unreachable by the precondition
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
#[ensures(true)]
pub fn f(x: i32) {
    if x <= 0 {
        std::panic::panic_any(0u32);
    }
}
