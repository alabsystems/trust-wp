// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fixture that intentionally triggers a contract parse error.
//!
//! String literals like `"a"` are valid Rust syntax and accepted by the
//! proc macro, but trust-wp's contract parser does not support string literal
//! tokens in pure expressions.

use trust_wp::ensures;

#[ensures(result == "a")]
pub fn return_char() -> char {
    'a'
}
