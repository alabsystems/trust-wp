// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `&u8 - &u8` calls `<&u8 as Sub>::sub`: panics for `*a < *b`.

use trust_wp::{ensures, requires};

#[requires(true)]
#[ensures(true)]
pub fn ref_sub(a: &u8, b: &u8) -> u8 {
    a - b
}

fn main() {}
