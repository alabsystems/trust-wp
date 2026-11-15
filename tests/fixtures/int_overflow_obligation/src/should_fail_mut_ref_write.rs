// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (write through `&mut`): `v` is overwritten through a mutable borrow
//! with 255 before `v + 1`; the obligation must not use the initial `0`.

use trust_wp::ensures;

#[ensures(true)]
pub fn through_ref(y: u8) -> u8 {
    let mut v: u8 = 0;
    let r = &mut v;
    *r = y;
    v + 1
}

fn main() {}
