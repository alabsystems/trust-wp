// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `&u8 << &u32` forwards to the checked shift; panics for `*s >= 8`.

use trust_wp::ensures;

#[ensures(true)]
pub fn shl_ref(x: &u8, s: &u32) -> u8 {
    x << s
}

fn main() {}
