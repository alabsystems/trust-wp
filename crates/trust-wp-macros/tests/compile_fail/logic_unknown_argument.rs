// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `#[logic(typo)]` rejects unknown attribute arguments
//!
//! The `#[logic]` attribute accepts: `open`, `open(self)`, `open(crate)`, `prophetic`, `law`.
//! Any other argument is a compile-time error.
//!
//! Issue: #473 (logic attribute argument silently ignored)

use trust_wp_macros::logic;

// ERROR: unknown attribute argument
#[logic(typo)]
fn bad_logic(x: i32) -> i32 {
    x
}

fn main() {}
