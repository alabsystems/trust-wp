//@ expect: verify
//@ mechanism: a -> ! panicking fn with requires(false), called only where the precondition rules the call out
//@ accept-means: n/a (control) — TRUE contracts, must keep verifying
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
#[ensures(true)]
pub fn die() -> ! {
    panic!()
}

#[requires(x@ > 0)]
#[ensures(true)]
pub fn f(x: i32) {
    if x <= 0 {
        die()
    }
}
