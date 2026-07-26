// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[ensures(result ...)]` remains valid on value-returning items.

use trust_wp_macros::ensures;

#[ensures(result == 0)]
fn returns_zero() -> i32 {
    0
}

fn main() {
    let _ = returns_zero();
}
