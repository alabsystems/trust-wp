// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: explicit `-> ()` still counts as unit return for `result`.

use trust_wp_macros::ensures;

// ERROR: `result` requires the annotated item to return a value
#[ensures(result == 0)]
fn explicit_unit() -> () {}

fn main() {}
