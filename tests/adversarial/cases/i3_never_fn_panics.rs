//@ expect: reject
//@ mechanism: a -> ! body that unconditionally panics has no switch, so no panic obligation was emitted; ensures(true) was proved vacuously
//@ accept-means: die() with requires(true) was accepted although its body panics. FALSE: die() panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r6)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn die() -> ! {
    panic!()
}

#[ensures(true)]
pub fn f(x: i32) {
    if x <= 0 {
        die()
    }
}
