// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A local whose `Drop` impl panics: drop glue runs after `x / 1`. A
//! contract-free body is never verified over it.

struct D;

impl Drop for D {
    fn drop(&mut self) {
        panic!("boom")
    }
}

pub fn dropper(x: u8) -> u8 {
    let _d = D;
    x / 1
}

fn main() {}
