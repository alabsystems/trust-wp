//@ expect: verify
//@ mechanism: the per-parameter keying control for the credit rule: the call takes `x`,
//@ mechanism: and the write afterwards lands on a DIFFERENT parameter. `x`'s credit must
//@ mechanism: survive. A disqualification keyed on "this body writes through some `&mut`
//@ mechanism: after a call" instead of on the written parameter would refuse this.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32, y: &mut i32) {
    set(x);
    *y = 3i32;
}
