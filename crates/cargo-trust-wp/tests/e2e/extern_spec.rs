// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! extern_spec! User-Defined Contract Tests.
//!
//! These tests verify that user-defined extern_spec! macros are discovered
//! and used during verification (Part of #160, #371).

use ntest::timeout;

use super::support::{assert_function_status, run_cargo_trust_wp, stderr_string};

/// Tests that user-defined `extern_spec!` for `Option::unwrap` is discovered and used.
///
/// The `get_value` function relies on the `extern_spec!` contract to verify.
/// If the `extern_spec!` is not discovered, verification would fail because
/// the driver wouldn't know the contract for `Option::unwrap`.
#[test]
#[timeout(180_000)]
fn test_extern_spec_user_defined_option_unwrap() {
    let output = run_cargo_trust_wp("extern_spec_project", "get_value");
    let stderr = stderr_string(&output);
    // Check function-specific output, not exit code: extern_spec verification
    // may fail for reasons unrelated to contract discovery.
    assert_function_status(&stderr, "get_value", "verified");
}

/// Tests a simpler case: `get_known_value` should verify with hardcoded `Some(42)`.
#[test]
#[timeout(180_000)]
fn test_extern_spec_get_known_value() {
    let output = run_cargo_trust_wp("extern_spec_project", "get_known_value");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "get_known_value", "verified");
}

/// An `extern_spec!` method body is proved against the spec's own ensures
/// (Creusot goal `vc_extern_spec_<..>_body`).
#[test]
#[timeout(180_000)]
fn test_extern_spec_body_is_verified() {
    let output = run_cargo_trust_wp("extern_spec_project", "is_one_body");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("is_one_body verified ✓"),
        "extern_spec body must be verified:\n{stderr}"
    );
}

/// A body that violates the extern spec's ensures is rejected.
#[test]
#[timeout(180_000)]
fn test_extern_spec_wrong_body_fails() {
    let output = run_cargo_trust_wp("extern_spec_project", "is_one_wrong_body");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("is_one_wrong_body FAILED ✗"),
        "wrong extern_spec body must fail:\n{stderr}"
    );
}
