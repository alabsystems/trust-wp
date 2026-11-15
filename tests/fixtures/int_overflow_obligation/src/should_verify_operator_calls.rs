// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twins of the operator-call RED fixtures: each call is guarded.

use std::ops::Add;
use trust_wp::{ensures, requires};

#[requires(x@ < 255)]
#[ensures(true)]
pub fn explicit_add_ok(x: u8) -> u8 {
    std::ops::Add::add(x, 1)
}

#[requires(x@ < 255)]
#[ensures(true)]
pub fn method_add_ok(x: u8) -> u8 {
    x.add(1)
}

#[requires(s@ < 8)]
#[ensures(true)]
pub fn shl_ref_ok(x: &u8, s: &u32) -> u8 {
    x << s
}

fn main() {}
