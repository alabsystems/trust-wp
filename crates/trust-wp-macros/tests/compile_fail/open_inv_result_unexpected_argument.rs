// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `#[open_inv_result(arg)]` rejects unexpected arguments
//!
//! The `#[open_inv_result]` attribute takes no arguments.
//!
//! Issue: #2564 (self-audit parity with other zero-argument marker attrs)

use trust_wp_macros::open_inv_result;

// ERROR: #[open_inv_result] takes no arguments
#[open_inv_result(something)]
fn bad_open_inv_result(x: u64) -> u64 {
    x
}

fn main() {}
