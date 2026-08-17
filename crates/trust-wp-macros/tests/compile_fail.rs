// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail tests for trust-wp-macros
//!
//! These tests verify that invalid contracts produce compile-time errors
//! rather than silently passing.

#[test]
fn compile_fail() {
    if !trust_wp_test_utils::enter_explicit_unverified_trybuild_test("compile_fail") {
        return;
    }
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile_fail/*.rs");
}
