//@ expect: verify
//@ mechanism: Control for the annotated_loop_* family: the same annotated loop with NO write
//@ mechanism: anywhere. `^r == *r` is TRUE here, so the fix for the family must not be a
//@ mechanism: blanket refusal of functions that contain an annotated loop.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        i += 1;
    }
}
