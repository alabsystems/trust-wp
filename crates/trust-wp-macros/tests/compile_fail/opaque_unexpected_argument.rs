// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `#[opaque(arg)]` rejects unexpected arguments
//!
//! The `#[opaque]` attribute takes no arguments.
//!
//! Issue: #473 (related self-audit — attribute arguments silently ignored)

use trust_wp_macros::opaque;

// ERROR: #[opaque] takes no arguments
#[opaque(something)]
fn bad_opaque(x: i32) -> i32 {
    x
}

fn main() {}
