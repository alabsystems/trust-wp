// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile-fail tests for contract macros.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests verify that invalid contracts produce compile errors.

#[test]
fn compile_fail_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile_fail/*.rs");
}
