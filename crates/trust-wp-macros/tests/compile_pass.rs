// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass tests for trust-wp-macros.

#[test]
fn compile_pass() {
    if !trust_wp_test_utils::enter_explicit_unverified_trybuild_test("compile_pass") {
        return;
    }
    let t = trybuild::TestCases::new();
    t.pass("tests/compile_pass/*.rs");
}
