// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: free `result` in `#[ensures]` requires a non-unit return.

use trust_wp_macros::ensures;

// ERROR: `result` requires the annotated item to return a value
#[ensures(result == 0)]
fn no_return() {}

fn main() {}
