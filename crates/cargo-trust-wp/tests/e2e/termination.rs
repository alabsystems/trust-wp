// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive Termination E2E Tests (#208).

use ntest::timeout;

use super::support::{assert_function_status, run_cargo_trust_wp, status_code, stderr_string};

/// Direct recursion with #[check(terminates)] and a decreasing variant should verify.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_variant_decreases() {
    let output = run_cargo_trust_wp("termination_project", "recursive_countdown");
    let stderr = stderr_string(&output);
    assert!(
        output.status.success(),
        "recursive_countdown should verify: {output:?}"
    );
    assert_function_status(&stderr, "recursive_countdown", "verified");
}

/// Direct recursion with #[check(terminates)] but no #[variant] should error.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_missing_variant_errors() {
    let output = run_cargo_trust_wp("termination_project", "recursive_missing_variant");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "missing recursive variant should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic: {stderr}"
    );
    assert!(
        stderr.contains("requires #[variant(...)]"),
        "expected missing-variant guidance: {stderr}"
    );
}

/// Direct recursion with a non-decreasing variant should fail verification.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_non_decreasing_variant_fails() {
    let output = run_cargo_trust_wp("termination_project", "recursive_non_decreasing");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        1,
        "non-decreasing recursive variant should fail verification: {output:?}"
    );
    assert_function_status(&stderr, "recursive_non_decreasing", "FAILED");
}

/// Conditional recursion with divergent assignment should verify (#807).
///
/// The non-recursive branch has a different computation in the same MIR local,
/// but CFG-aware extraction ensures the recursive call uses the correct args.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_conditional_recursion_verifies() {
    let output = run_cargo_trust_wp("termination_project", "conditional_recursion");
    let stderr = stderr_string(&output);
    assert!(
        output.status.success(),
        "conditional_recursion should verify (variant n decreases by 1): {stderr}"
    );
    assert_function_status(&stderr, "conditional_recursion", "verified");
}

/// Guarded recursion where variant decrease requires call-site path assumptions (#813).
#[test]
#[timeout(180_000)]
fn test_recursive_termination_guarded_path_sensitive_variant_verifies() {
    let output = run_cargo_trust_wp(
        "termination_project",
        "guarded_recursion_requires_path_condition",
    );
    let stderr = stderr_string(&output);
    assert!(
        output.status.success(),
        "guarded_recursion_requires_path_condition should verify under n > 0 path guard: {stderr}"
    );
    assert_function_status(
        &stderr,
        "guarded_recursion_requires_path_condition",
        "verified",
    );
}

/// Guarded recursion with a non-decreasing variant should still fail.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_guarded_non_decreasing_variant_fails() {
    let output = run_cargo_trust_wp("termination_project", "guarded_recursion_non_decreasing");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        1,
        "guarded_recursion_non_decreasing should fail verification: {output:?}"
    );
    assert_function_status(&stderr, "guarded_recursion_non_decreasing", "FAILED");
}

/// Mutual recursion with `#[check(terminates)]` still requires variants on cycle members.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_mutual_missing_variant_errors() {
    let output = run_cargo_trust_wp("termination_project", "mutual_missing_variant");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "mutual recursion missing variants should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic: {stderr}"
    );
    assert!(
        stderr.contains("requires #[variant(...)]"),
        "expected missing-variant guidance for mutual recursion: {stderr}"
    );
}

/// Recursion through an unannotated helper is detected as mutual recursion and rejected.
///
/// `helper_recursion_through_unannotated` calls `_helper_trampoline` (no contracts),
/// which calls back. The reachable call graph expands through the helper to discover
/// the cycle, and structural validation rejects it as mutual recursion.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_helper_indirect_recursion_rejected() {
    let output = run_cargo_trust_wp(
        "termination_project",
        "helper_recursion_through_unannotated",
    );
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "helper-indirect recursion should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("mutual recursion"),
        "expected mutual-recursion diagnostic for helper-indirect recursion: {stderr}"
    );
    assert!(
        stderr.contains("not yet supported"),
        "expected unsupported mutual-recursion guidance: {stderr}"
    );
}

/// Mutual recursion under `#[check(terminates)]` is rejected until SCC variant ordering lands.
#[test]
#[timeout(180_000)]
fn test_recursive_termination_mutual_recursion_not_supported_errors() {
    let output = run_cargo_trust_wp("termination_project", "mutual_non_decreasing");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "mutual recursion should be a termination-check error until supported: {output:?}"
    );
    assert!(
        stderr.contains("mutual recursion"),
        "expected mutual-recursion diagnostic: {stderr}"
    );
    assert!(
        stderr.contains("not yet supported"),
        "expected unsupported mutual-recursion guidance: {stderr}"
    );
}

/// A `#[check(terminates)]` function that calls a non-terminated callee should error.
#[test]
#[timeout(180_000)]
fn test_terminates_calls_nonterminate_errors() {
    let output = run_cargo_trust_wp("termination_project", "terminates_calls_nonterminate");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "terminates calling non-terminates should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic: {stderr}"
    );
    assert!(
        stderr.contains("not marked #[check(terminates)]"),
        "expected non-terminates callee guidance: {stderr}"
    );
}

/// A `#[check(terminates)]` function with a loop but no variant should error.
#[test]
#[timeout(180_000)]
fn test_terminates_loop_no_variant_errors() {
    let output = run_cargo_trust_wp("termination_project", "terminates_loop_no_variant");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "terminates with unguarded loop should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic: {stderr}"
    );
    assert!(
        stderr.contains("loop") && stderr.contains("variant"),
        "expected loop-variant requirement guidance: {stderr}"
    );
}

/// A trait impl that omits `#[check(terminates)]` declared by the trait should error.
#[test]
#[timeout(180_000)]
fn test_trait_impl_check_mode_mismatch_errors() {
    let output = run_cargo_trust_wp("termination_project", "must_terminate");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "trait-impl check mode mismatch should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic: {stderr}"
    );
    assert!(
        stderr.contains("Expected") && stderr.contains("#[check(terminates)]"),
        "expected trait-impl mismatch guidance: {stderr}"
    );
}

/// Mutual recursion through default trait method: impl_g -> Self::default_f (#2686).
///
/// An impl method that calls a default trait method from the same trait should be
/// rejected because the default method could be overridden to call back. This matches
/// Creusot's should_fail/terminates/default_function_non_logic.rs test.
#[test]
#[timeout(180_000)]
fn test_default_trait_method_mutual_recursion_rejected() {
    let output = run_cargo_trust_wp("termination_project", "impl_g");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "default-method mutual recursion should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic for default-method mutual recursion: {stderr}"
    );
}

/// Mutual recursion through generic trait dispatch: i32::dispatch_foo -> generic_bar -> I::Item::dispatch_foo (#2686).
///
/// When a #[check(terminates)] function calls through generic trait dispatch that can
/// resolve back to the same function, the callgraph conservative edges should detect
/// the cycle. This matches Creusot's should_fail/terminates/complicated_traits_recursion.rs.
#[test]
#[timeout(180_000)]
fn test_generic_trait_dispatch_mutual_recursion_rejected() {
    let output = run_cargo_trust_wp("termination_project", "dispatch_foo");
    let stderr = stderr_string(&output);
    assert_eq!(
        status_code(&output),
        2,
        "generic-dispatch mutual recursion should be a termination-check error: {output:?}"
    );
    assert!(
        stderr.contains("termination check failed"),
        "expected termination-check diagnostic for generic-dispatch mutual recursion: {stderr}"
    );
}
