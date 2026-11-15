// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twins of the second overflow-obligation fixtures.

use trust_wp::{ensures, requires};

/// `b` reads only the stable `a`: `a - b == 0` stays exact past the loop.
#[requires(input@ == 0)]
#[ensures(true)]
pub fn stable_chain(input: u8) -> u8 {
    let mut x: u8 = input;
    let a = x;
    let b = a;
    x = 255;
    let mut i: u8 = 0;
    while i < 1 {
        i += 1;
    }
    let _ = x;
    a - b
}

/// Twin of conflate_post: `a / 2 + b / 2 <= 254` for any two `u8`.
#[requires(input@ == 0)]
#[ensures(true)]
pub fn conflate_ranges(input: u8) -> u8 {
    let mut x: u8 = input;
    let a = x;
    x = 255;
    let b = x;
    let mut i: u8 = 0;
    let mut r: u8 = 0;
    while i < 1 {
        r = a / 2 + b / 2;
        i += 1;
    }
    let _ = x;
    r
}

/// Twin of conflate_contractless (no panic site but arithmetic).
pub fn conflate_contractless_ok(input: u8) -> u8 {
    let mut x: u8 = input;
    let a = x;
    x = x.wrapping_add(128);
    let b = x;
    let mut i: u8 = 0;
    while i < 1 {
        i += 1;
    }
    let _ = x;
    a / 2 + b / 2
}

/// Twin of assert_contractless: the contract makes the assert unreachable.
#[requires(x@ < 3)]
#[ensures(true)]
pub fn assert_contracted_ok(x: u8) -> u8 {
    assert!(x < 3);
    x + 1
}

#[requires(x@ < 255)]
#[ensures(true)]
pub fn ref_add_ok(x: &u8) -> u8 {
    x + 1
}

#[requires(a@ >= b@)]
#[ensures(true)]
pub fn ref_sub_ok(a: &u8, b: &u8) -> u8 {
    a - b
}

fn main() {}
