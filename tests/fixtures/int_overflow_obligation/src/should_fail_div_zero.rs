// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `a / b` with no precondition divides by zero when b = 0.
//! Creusot: `UInt32.div` precondition `t'int b <> 0`.

use trust_wp::ensures;

#[ensures(true)]
pub fn quot0(a: u32, b: u32) -> u32 {
    a / b
}

fn main() {}
