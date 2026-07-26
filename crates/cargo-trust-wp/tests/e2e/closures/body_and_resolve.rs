// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure body verification and resolve predicate support — Phase 3-4 (#358).

use ntest::timeout;

use crate::support::{
    assert_function_status, assert_trusted_non_proof, run_cargo_trust_wp, stderr_string,
};

// ============================================================================
// Phase 3: Annotated closure body verification (#358)
// ============================================================================

#[test]
#[timeout(180_000)]
fn test_closure_phase3_annotated_body_positive() {
    let output = run_cargo_trust_wp("closure_project", "phase3_annotated_closure_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase3_annotated_closure_positive", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase3_annotated_body_negative_fails() {
    let output = run_cargo_trust_wp("closure_project", "phase3_annotated_closure_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "phase3_annotated_closure_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "phase3_annotated_closure_negative", "FAILED");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase3_capture_substitution_positive() {
    let output = run_cargo_trust_wp("closure_project", "phase3_capture_substitution_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase3_capture_substitution_positive", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase3_capture_substitution_negative_fails() {
    let output = run_cargo_trust_wp("closure_project", "phase3_capture_substitution_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "phase3_capture_substitution_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "phase3_capture_substitution_negative", "FAILED");
}

// Phase 3 AC#4: Creusot 01_basic.rs-inspired patterns

#[test]
#[timeout(180_000)]
fn test_closure_phase3_basic_capture_return() {
    let output = run_cargo_trust_wp("closure_project", "phase3_basic_capture_return");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase3_basic_capture_return", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase3_basic_multi_arg_positive() {
    let output = run_cargo_trust_wp("closure_project", "phase3_basic_multi_arg_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase3_basic_multi_arg_positive", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase3_basic_multi_arg_fails() {
    let output = run_cargo_trust_wp("closure_project", "phase3_basic_multi_arg_fails");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "phase3_basic_multi_arg_fails should fail: {output:?}"
    );
    assert_function_status(&stderr, "phase3_basic_multi_arg_fails", "FAILED");
}

// Phase 3 AC#2 & AC#5: FnMut closure body with mutable capture

#[test]
#[timeout(180_000)]
fn test_closure_phase3_fnmut_capture_increment() {
    let output = run_cargo_trust_wp("closure_project", "phase3_fnmut_capture_increment_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(
        &stderr,
        "phase3_fnmut_capture_increment_positive",
        "verified",
    );
}

#[test]
#[timeout(180_000)]
fn test_closure_phase3_fnmut_capture_increment_fails() {
    let output = run_cargo_trust_wp("closure_project", "phase3_fnmut_capture_increment_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "phase3_fnmut_capture_increment_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "phase3_fnmut_capture_increment_negative", "FAILED");
}

// ── Phase 4: resolve predicate and FnOnce support ──────────────────────

#[test]
#[timeout(180_000)]
fn test_closure_phase4_resolve_simple_positive() {
    let output = run_cargo_trust_wp("closure_project", "phase4_resolve_simple_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase4_resolve_simple_positive", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_once_trusted() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_once_trusted");
    assert_trusted_non_proof(&output, "call_fn_once_trusted");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_once_verified() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_once_verified");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "call_fn_once_verified", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_once_negative() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_once_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "call_fn_once_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "call_fn_once_negative", "FAILED");
}

// ── Phase 4: FnMut -> FnOnce weakening (non-trusted) ──────────────────

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_mut_as_fn_once_verified() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_as_fn_once_verified");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "call_fn_mut_as_fn_once_verified", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_mut_as_fn_once_negative() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_as_fn_once_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "call_fn_mut_as_fn_once_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "call_fn_mut_as_fn_once_negative", "FAILED");
}

// ── Phase 4b: Fn closure laws — Fn -> FnMut -> FnOnce weakening chain ──

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_trusted() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_trusted");
    assert_trusted_non_proof(&output, "call_fn_trusted");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_as_fn_once_trusted() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_as_fn_once_trusted");
    assert_trusted_non_proof(&output, "call_fn_as_fn_once_trusted");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_weaken_fn_to_fn_once() {
    let output = run_cargo_trust_wp("closure_project", "weaken_fn_to_fn_once");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "weaken_fn_to_fn_once", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4_fn_negative() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "call_fn_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "call_fn_negative", "FAILED");
}

// ── Phase 4c: Creusot 06_fn_specs.rs patterns — weakening at each trait level ──

#[test]
#[timeout(180_000)]
fn test_closure_phase4c_weaken_fn_mut_to_fn_once() {
    let output = run_cargo_trust_wp("closure_project", "weaken_fn_mut_to_fn_once");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "weaken_fn_mut_to_fn_once", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4c_weaken_fn_both_postconditions() {
    let output = run_cargo_trust_wp("closure_project", "weaken_fn_both_postconditions");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "weaken_fn_both_postconditions", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4c_fn_once_user() {
    let output = run_cargo_trust_wp("closure_project", "fn_once_user");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "fn_once_user", "verified");
}

// ── Phase 4c: Simplified 09_fnonce_resolve.rs patterns ─────────────────

#[test]
#[timeout(180_000)]
fn test_closure_phase4c_apply_fn_once_to_val() {
    let output = run_cargo_trust_wp("closure_project", "apply_fn_once_to_val");
    assert_trusted_non_proof(&output, "apply_fn_once_to_val");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase4c_fnonce_resolve_negative() {
    let output = run_cargo_trust_wp("closure_project", "fnonce_resolve_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "fnonce_resolve_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "fnonce_resolve_negative", "FAILED");
}
