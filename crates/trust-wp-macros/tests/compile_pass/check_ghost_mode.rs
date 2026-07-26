// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[check(ghost)]` should be accepted on functions.
//! Regression test for #1313.

use trust_wp_macros::check;

#[check(ghost)]
fn ghost_function(x: i32) -> i32 {
    x + 1
}

fn main() {
    let _ = ghost_function(1);
}
