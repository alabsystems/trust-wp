// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Iterator::sum` into `u8` is an overflow-checked fold: `[255, 1]` panics.

pub fn sum(v: &[u8]) -> u8 {
    v.iter().sum::<u8>() / 1
}

fn main() {}
