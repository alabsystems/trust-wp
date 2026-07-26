// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `result` cannot be used in pearlite!
//!
//! The `result` keyword refers to the function's return value and is only
//! valid in postconditions (#[ensures]), not in pearlite! expressions.

use trust_wp_macros::pearlite;

fn main() {
    // result is not valid in pearlite - only in ensures
    let _ = pearlite!(result > 0);
}
