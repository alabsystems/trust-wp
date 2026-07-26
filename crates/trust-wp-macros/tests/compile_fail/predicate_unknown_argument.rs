// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `#[predicate(typo)]` rejects unknown attribute arguments
//!
//! The `#[predicate]` attribute accepts: `open`, `open(self)`, `open(crate)`, `prophetic`, `law`.
//! Any other argument is a compile-time error.
//!
//! Issue: #473 (logic attribute argument silently ignored)

use trust_wp_macros::predicate;

// ERROR: unknown attribute argument
#[predicate(typo)]
fn bad_predicate(x: i32) -> bool {
    x > 0
}

fn main() {}
