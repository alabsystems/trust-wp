// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `v.remove(0)` panics on an empty vector inside the callee. No lane checks
//! the std body, so a contract-free caller is never verified.

pub fn vr(mut v: Vec<u8>) -> u8 {
    v.remove(0) / 1
}

fn main() {}
