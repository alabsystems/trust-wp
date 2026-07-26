// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trait Contract Tests (#357, #717, #1579, #1652).
//!
//! Covers trait contract inheritance, generic call sites, struct field access,
//! trait refinement obligations, loop-verified refinement, and invariant parity.

use ntest::timeout;

use super::support::{
    assert_exact_trust_wp_line_count, assert_function_status, run_cargo_trust_wp, status_code,
    stderr_string,
};

// ============================================================================
// Phase 1: Trait method contracts are discovered and inherited by impls.
// ============================================================================

/// Tests that trait method contracts are discovered by the driver.
///
/// The Counter trait has `#[ensures(result >= 0)]` on its `count` method.
/// `MyCounter::count` (with no explicit contracts) should inherit this contract
/// and verify successfully since it returns 42. Verification of the impl method
/// proves trait contract discovery worked (without inherited contracts, the
/// function would have no ensures clause to check).
#[test]
#[timeout(180_000)]
fn test_trait_contract_discovery() {
    let output = run_cargo_trust_wp("trait_project", "count");
    let stderr = stderr_string(&output);
    // Trait contract discovery is proven by the impl method being verified:
    // MyCounter::count has no explicit contract — only inherited trait contracts.
    assert_function_status(&stderr, "<MyCounter as Counter>::count", "verified");
}

/// Tests that an impl method inherits and verifies against its trait contract.
///
/// `MyCounter::count` returns 42, which satisfies `ensures(result >= 0)`.
#[test]
#[timeout(180_000)]
fn test_trait_contract_inherits_and_verifies() {
    let output = run_cargo_trust_wp("trait_project", "count");
    let stderr = stderr_string(&output);
    // The impl method should be verified against the inherited trait contract
    assert_function_status(&stderr, "count", "verified");
}

/// Tests the Positive trait: `AlwaysOne::get_positive` returns 1, satisfies `ensures(result > 0)`.
#[test]
#[timeout(180_000)]
fn test_trait_contract_positive_verifies() {
    let output = run_cargo_trust_wp("trait_project", "AlwaysOne");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "get_positive", "verified");
}

/// Tests that an impl violating its trait's contract is detected as a failure.
///
/// `AlwaysZero::get_positive` returns 0, which violates `ensures(result > 0)`.
#[test]
#[timeout(180_000)]
fn test_trait_contract_violation_detected() {
    let output = run_cargo_trust_wp("trait_project", "AlwaysZero");
    assert!(
        !output.status.success(),
        "expected failure exit code: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "get_positive", "FAILED");
}

// ============================================================================
// Phase 2: Generic Call Site Trait Contract Tests (#357)
//
// Tests that generic functions like `fn f<T: Foo>(x: T)` can use
// the trait's contracts at call sites.
// ============================================================================

/// Tests that a generic function calling `Counter::count` verifies.
///
/// `generic_count<T: Counter>(c: &T) -> i32` calls `c.count()` and has
/// `ensures(result >= 0)`. Since `Counter::count` has `ensures(result >= 0)`,
/// the trait's postcondition should be available at the call site and
/// verification should succeed.
#[test]
#[timeout(180_000)]
fn test_trait_generic_call_site_verifies() {
    let output = run_cargo_trust_wp("trait_project", "generic_count");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "generic_count", "verified");
}

/// Tests that a generic function calling `Positive::get_positive` verifies.
///
/// `generic_positive<T: Positive>(p: &T) -> i32` calls `p.get_positive()`
/// and has `ensures(result > 0)`. The trait guarantees `result > 0`.
#[test]
#[timeout(180_000)]
fn test_trait_generic_positive_verifies() {
    let output = run_cargo_trust_wp("trait_project", "generic_positive");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "generic_positive", "verified");
}

/// Tests that a generic function with a too-strong postcondition fails.
///
/// `generic_count_too_strong<T: Counter>(c: &T) -> i32` calls `c.count()`
/// and claims `ensures(result > 0)`, but Counter only guarantees `result >= 0`.
/// Result could be 0, so verification should fail.
#[test]
#[timeout(180_000)]
fn test_trait_generic_too_strong_fails() {
    let output = run_cargo_trust_wp("trait_project", "generic_count_too_strong");
    assert!(
        !output.status.success(),
        "expected failure exit code: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "generic_count_too_strong", "FAILED");
}

// ============================================================================
// Phase 4: Generic struct field access in specifications (#717)
// ============================================================================

/// Tests that a function accessing a generic struct field in a postcondition verifies.
///
/// `get_inner_ge(x: &Wrapper<i32>) -> i32` returns `x.inner` and has
/// `ensures(result >= x.inner)`. Since the result IS `x.inner`, this should verify.
#[test]
#[timeout(180_000)]
fn test_generic_struct_field_access_verifies() {
    let output = run_cargo_trust_wp("trait_project", "get_inner_ge");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "get_inner_ge", "verified");
}

/// Tests that a generic function accessing a field of a wrapper struct verifies.
///
/// `count_wrapper<T: Counter>(w: &Wrapper<T>) -> i32` calls `w.inner.count()`
/// and has `ensures(result >= 0)`. The trait guarantees `result >= 0`.
#[test]
#[timeout(180_000)]
fn test_generic_struct_trait_field_call_verifies() {
    let output = run_cargo_trust_wp("trait_project", "count_wrapper");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "count_wrapper", "verified");
}

// ============================================================================
// Phase 3: Trait refinement obligations (#357)
// ============================================================================

/// Tests that an impl with a stronger postcondition passes trait refinement.
#[test]
#[timeout(180_000)]
fn test_trait_refinement_stronger_postcondition_verifies() {
    let output = run_cargo_trust_wp("trait_project", "StrongerPost");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("refinement verified"),
        "StrongerPost should pass trait refinement with stronger postcondition: {stderr}"
    );
}

/// Tests that strengthening the precondition fails refinement.
#[test]
#[timeout(180_000)]
fn test_trait_refinement_stronger_precondition_fails() {
    let output = run_cargo_trust_wp("trait_project", "StrongerPre");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trait refinement FAILED"),
        "StrongerPre should fail trait refinement: {stderr}"
    );
    assert!(
        stderr.contains("trait precondition implies impl precondition"),
        "missing precondition refinement failure check label: {stderr}"
    );
}

/// Tests that weakening the postcondition fails refinement.
#[test]
#[timeout(180_000)]
fn test_trait_refinement_weaker_postcondition_fails() {
    let output = run_cargo_trust_wp("trait_project", "WeakerPost");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trait refinement FAILED"),
        "WeakerPost should fail trait refinement: {stderr}"
    );
    assert!(
        stderr.contains("impl postcondition implies trait postcondition"),
        "missing postcondition refinement failure check label: {stderr}"
    );
    // Precondition direction must NOT fail — both sides use `x >= 0` (#2363).
    assert!(
        !stderr.contains("check: trait precondition implies impl precondition"),
        "WeakerPost precondition direction should NOT fail (same requires on both sides): {stderr}"
    );
}

/// Tests that trait refinement succeeds when impl and trait parameter names differ.
#[test]
#[timeout(180_000)]
fn test_trait_refinement_param_rename_verifies() {
    let output = run_cargo_trust_wp("trait_project", "RenamedParamImpl");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("refinement verified"),
        "RenamedParamImpl should verify refinement with parameter normalization: {stderr}"
    );
}

// ============================================================================
// Phase 5: Trait refinement for loop-verified functions (#1652)
// ============================================================================

/// Regression test for #1652: loop-verified trait impl with weaker postcondition
/// must fail trait refinement.
///
/// Before #1652, the loop verification path ended with `continue`, skipping the
/// trait refinement check entirely. This test confirms the fix catches the
/// violation: `result >= 0` does not imply trait's `result == n`.
#[test]
#[timeout(180_000)]
fn test_loop_trait_refinement_weaker_postcondition_fails() {
    let output = run_cargo_trust_wp("trait_project", "WeakerLoopPost");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1 for weaker loop postcondition: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert_exact_trust_wp_line_count(
        &stderr,
        "trust-wp: <WeakerLoopPost as LoopRefinedCounter>::sum_n verified ✓",
        1,
    );
    assert_exact_trust_wp_line_count(
        &stderr,
        "trust-wp: <WeakerLoopPost as LoopRefinedCounter>::sum_n trait refinement FAILED ✗",
        1,
    );
    assert!(
        stderr.contains("impl postcondition implies trait postcondition"),
        "missing postcondition refinement failure label (loop path): {stderr}"
    );
    assert!(
        stderr.contains("post-loop verification") || stderr.contains("postcondition deferred"),
        "expected compositional path diagnostic before refinement: {stderr}"
    );
    // A single trait-refinement pass can legitimately emit separate failures for
    // the precondition and postcondition directions. Count the specific
    // postcondition check instead of the generic failure banner to detect
    // duplicate ContinueWithAssumptions refinement runs (#2361).
    let refinement_count = stderr
        .matches("check: impl postcondition implies trait postcondition")
        .count();
    assert_eq!(
        refinement_count, 1,
        "postcondition refinement should be reported exactly once, got {refinement_count}: \
         {stderr}"
    );
    // Precondition direction must NOT fail — both sides use `n >= 0` (#2363).
    assert!(
        !stderr.contains("check: trait precondition implies impl precondition"),
        "WeakerLoopPost precondition direction should NOT fail (same requires on both sides): \
         {stderr}"
    );
}

/// Tests that a loop-verified impl with the same postcondition verifies and
/// still reports trait refinement on the compositional path.
#[test]
#[timeout(180_000)]
fn test_loop_trait_refinement_matching_postcondition_verifies() {
    let output = run_cargo_trust_wp("trait_project", "StrongerLoopPost");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_exact_trust_wp_line_count(
        &stderr,
        "trust-wp: <StrongerLoopPost as LoopRefinedCounter>::sum_n verified ✓",
        1,
    );
    assert_exact_trust_wp_line_count(
        &stderr,
        "trust-wp: <StrongerLoopPost as LoopRefinedCounter>::sum_n refinement verified ✓",
        1,
    );
    assert!(
        stderr.contains("post-loop verification") || stderr.contains("postcondition deferred"),
        "expected compositional path diagnostic before successful refinement: {stderr}"
    );
    assert!(
        !stderr.contains("<StrongerLoopPost as LoopRefinedCounter>::sum_n trait refinement FAILED"),
        "StrongerLoopPost should not emit a trait refinement failure: {stderr}"
    );
}

// ============================================================================
// Phase 6: Type-invariant clause parity in trait refinement (#1579)
// ============================================================================

/// Tests that invariant-backed refinement verifies when the type invariant
/// makes the impl precondition provable from the trait precondition.
///
/// InvariantRefinementOk adds `x.invariant()` as an impl precondition. Since
/// the type invariant on PositiveU32 is assumed for all well-typed arguments,
/// `true => x.invariant()` holds after invariant augmentation and refinement
/// should verify.
#[test]
#[timeout(180_000)]
fn test_trait_refinement_invariant_positive_verifies() {
    let output = run_cargo_trust_wp("trait_project", "InvariantRefinementOk");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("refinement verified"),
        "InvariantRefinementOk should pass trait refinement with invariant augmentation: {stderr}"
    );
}

/// Tests that refinement still fails when the impl precondition is strictly
/// stronger than what the type invariant provides.
///
/// InvariantRefinementTooStrong requires `x.0@ > 1`, but the invariant only
/// provides `x.0@ > 0`. The precondition refinement `true => (x.0@ > 1)` does
/// not hold even after augmentation, so refinement must fail.
#[test]
#[timeout(180_000)]
fn test_trait_refinement_invariant_negative_fails() {
    let output = run_cargo_trust_wp("trait_project", "InvariantRefinementTooStrong");
    assert_eq!(
        status_code(&output),
        1,
        "expected verification exit code 1: {output:?}"
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("trait refinement FAILED"),
        "InvariantRefinementTooStrong should fail trait refinement: {stderr}"
    );
    assert!(
        stderr.contains("trait precondition implies impl precondition"),
        "missing precondition refinement failure check label: {stderr}"
    );
}
