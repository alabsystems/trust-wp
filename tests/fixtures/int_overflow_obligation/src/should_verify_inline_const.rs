// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: an inline const body whose arithmetic provably stays in range.

use trust_wp::ensures;

#[ensures(true)]
pub fn half_const<const N: u32>(x: u32) -> u32 {
    let _ = const { N / 2 + 1 };
    x
}

fn main() {}
