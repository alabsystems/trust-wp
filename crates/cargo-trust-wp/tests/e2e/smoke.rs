// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Smoke / sanity tests for the cargo-trust-wp command surface.

use ntest::timeout;

use super::support::{
    assert_function_status, assert_trusted_non_proof, run_cargo_trust_wp, status_code,
    stderr_string,
};

#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_simple_project_verifies() {
    let output = run_cargo_trust_wp("simple_project", "increment");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    assert_function_status(&stderr, "increment", "verified");
}

#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_failing_project_reports_failure() {
    let output = run_cargo_trust_wp("failing_project", "buggy_increment");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    assert_function_status(&stderr, "buggy_increment", "FAILED");
}

/// Tests that `buggy_abs` (postcondition `result > 0` when `x == 0`) fails verification.
///
/// This tests a different failure mode from `buggy_increment`: zero-value edge case
/// where `abs(0) == 0` violates postcondition `result > 0`.
#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_failing_project_buggy_abs() {
    let output = run_cargo_trust_wp("failing_project", "buggy_abs");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    assert_function_status(&stderr, "buggy_abs", "FAILED");
}

#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_logic_project_verifies() {
    let output = run_cargo_trust_wp("logic_project", "add_one_runtime");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    assert_function_status(&stderr, "add_one_runtime", "verified");
}

/// Regression test for ay#1975 soundness fix (trust-wp#307).
///
/// The function `add_one_buggy` has an impossible postcondition (`result > add_one(x)`
/// where body is `x + 1` and `add_one(x) = x + 1`), which should FAIL verification.
///
/// Fixed in ay#1975 (commit 443907a1): LIA correctly handles UF Int terms.
#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_logic_project_reports_failure() {
    let output = run_cargo_trust_wp("logic_project", "add_one_buggy");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    assert_function_status(&stderr, "add_one_buggy", "FAILED");
}

/// Bare `#[logic]` (Default mode) must be opaque from a different module (#540).
///
/// `cross_module::cross_module_default_opaque` uses `super::add_one(x)` in its
/// postcondition from a child module. If Default-mode logic were incorrectly
/// open cross-module, this would verify; correct behavior is verification failure.
#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_logic_project_cross_module_default_is_opaque() {
    let output = run_cargo_trust_wp("logic_project", "cross_module_default_opaque");
    let code = status_code(&output);
    assert!(
        code == 1 || code == 2,
        "expected verification-failure (1) or unknown/incomplete (2) for cross-module opaque logic, got {code}: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    let failed_marker = "trust-wp: cross_module::cross_module_default_opaque FAILED";
    let unknown_marker = "trust-wp: cross_module::cross_module_default_opaque unknown";
    assert!(
        stderr.contains(failed_marker) || stderr.contains(unknown_marker),
        "expected cross-module function to be non-verified (FAILED/unknown): {stderr}"
    );
    assert!(
        !stderr.contains("trust-wp: cross_module::cross_module_default_opaque verified"),
        "cross-module Default logic unexpectedly verified: {stderr}"
    );
}

/// `#[law]` functions are equivalent to `#[logic(open)]` — their defining axiom
/// is emitted so the solver can use them. `triple_runtime` uses `triple(x)` in
/// its postcondition; the law axiom makes this provable. (#716)
#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_logic_project_law_function_verifies() {
    let output = run_cargo_trust_wp("logic_project", "triple_runtime");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    assert_function_status(&stderr, "triple_runtime", "verified");
}

#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_parse_error_projects_exit_code_3() {
    let output = run_cargo_trust_wp("parse_error_project", "return_char");
    assert_eq!(
        status_code(&output),
        3,
        "expected parse-error exit code 3: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("failed to parse ensures"),
        "missing parse error diagnostic: {stderr}"
    );
}

/// Tests that #[trusted] functions have postconditions assumed without body verification
/// but still do not count as clean proofs.
///
/// The `trusted_external` function has an intentionally wrong postcondition
/// (claims result > 100 but returns 42). Because it's marked #[trusted],
/// the body should NOT be verified and should show "trusted (skipped)".
///
/// The `--filter trusted_external` restricts verification to only the trusted function,
/// ensuring this test focuses specifically on trusted function handling.
#[test]
#[timeout(180_000)]
fn test_cargo_trust_wp_trusted_project() {
    let output = run_cargo_trust_wp("trusted_project", "trusted_external");
    let stderr = stderr_string(&output);
    assert_trusted_non_proof(&output, "trusted_external");
    assert!(
        stderr.contains("trust-wp:"),
        "missing trust-wp output: {stderr}"
    );
    // The key assertion: trusted_external should be marked as skipped, not failed
    assert!(
        stderr.contains("trusted_external trusted (skipped)"),
        "trusted function should be skipped, not verified: {stderr}"
    );
    // The trusted function specifically should NOT show FAILED
    assert!(
        !stderr.contains("trusted_external FAILED"),
        "trusted function should never fail verification: {stderr}"
    );
}
