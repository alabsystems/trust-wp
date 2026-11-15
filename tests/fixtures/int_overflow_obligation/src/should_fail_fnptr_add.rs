// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `<u8 as Add>::add` called through a fn pointer panics exactly as `x + 1`
//! does: `fnptr(255)` overflows.

pub fn fnptr(x: u8) -> u8 {
    let f: fn(u8, u8) -> u8 = <u8 as core::ops::Add>::add;
    f(x, 1) / 1
}

fn main() {}
