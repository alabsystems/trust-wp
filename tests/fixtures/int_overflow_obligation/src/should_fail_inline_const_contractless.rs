// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: the exact Creusot `should_fail/ignore_overflow.rs` shape — a
//! contract-free generic fn whose inline const body can overflow.

pub fn f<const N: u32>(_x: u32, _y: u32) {
    const { N + 1 };
}

fn main() {}
