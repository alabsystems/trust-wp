// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: every arithmetic operation below is guarded by a precondition
//! that implies Creusot's overflow goal, or has no overflow goal at all.

use trust_wp::{ensures, requires};

#[requires(x@ < 255)]
#[ensures(result@ == x@ + 1)]
pub fn add_guarded(x: u8) -> u8 {
    x + 1
}

#[requires(x@ > -128)]
#[ensures(result@ == x@ - 1)]
pub fn sub_guarded(x: i8) -> i8 {
    x - 1
}

#[requires(x@ <= 127)]
#[ensures(result@ == x@ * 2)]
pub fn mul_guarded(x: u8) -> u8 {
    x * 2
}

#[requires(x@ != -128)]
#[ensures(result@ == -x@)]
pub fn neg_guarded(x: i8) -> i8 {
    -x
}

#[requires(b@ != 0)]
#[requires(!(a@ == -128 && b@ == -1))]
#[ensures(true)]
pub fn div_guarded(a: i8, b: i8) -> i8 {
    a / b
}

#[requires(x@ < 255)]
#[ensures(true)]
pub fn add_in_branch(x: u8, c: bool) -> u8 {
    if c {
        x + 1
    } else {
        x
    }
}

#[ensures(true)]
pub fn add_path_guarded(x: u8) -> u8 {
    if x < 255 {
        x + 1
    } else {
        0
    }
}

#[ensures(true)]
pub fn wrapping(x: u8) -> u8 {
    x.wrapping_add(1)
}

#[ensures(true)]
pub fn unsigned_div(a: u8, b: u8) -> u8 {
    if b == 0 {
        0
    } else {
        a / b
    }
}

fn main() {}
