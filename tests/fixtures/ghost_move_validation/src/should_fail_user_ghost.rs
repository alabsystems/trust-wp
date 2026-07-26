// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression fixture for #1130.
//!
//! A user-defined type named `Ghost` must not be treated as trust-wp's
//! specification-only `Ghost<T>` type by move validation.

use trust_wp_std::ghost;

#[allow(dead_code)]
pub struct Ghost(Vec<i32>);

#[allow(dead_code)]
pub fn move_user_defined_ghost_in_ghost(g: Ghost) {
    let _ = ghost! {
        {
            // Must be rejected: this is a user-defined non-Copy type, not
            // trust-wp's `trust_wp_std::ghost::Ghost<T>`.
            let _moved = g; // ERROR: cannot move non-ghost value in ghost block
        }
    };
}

fn main() {}
