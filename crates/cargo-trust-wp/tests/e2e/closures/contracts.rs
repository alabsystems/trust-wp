// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure contract support — Phase 1 (Fn) and Phase 2 (FnMut) (#358).

use ntest::timeout;

use crate::support::{
    assert_function_status, assert_trusted_non_proof, run_cargo_trust_wp, stderr_string,
};

// ============================================================================
// Phase 1: Closure contract support (#358)
// ============================================================================

/// Tests that a trusted function with closure-spec methods is not a clean proof.
///
/// The key test: `#[requires(f.precondition(x))]` and `#[ensures(f.postcondition(x, result))]`
/// use `MethodCall` syntax with closure-spec method names. The ay encoder must encode
/// these as uninterpreted Bool functions without errors.
#[test]
#[timeout(180_000)]
fn test_closure_trusted_apply_fn_non_proof() {
    let output = run_cargo_trust_wp("closure_project", "apply_fn");
    assert_trusted_non_proof(&output, "apply_fn");
}

/// Tests that the `closure_project` baseline verifies correctly.
#[test]
#[timeout(180_000)]
fn test_closure_simple_positive_verifies() {
    let output = run_cargo_trust_wp("closure_project", "simple_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "simple_positive", "verified");
}

/// Tests that a non-trusted function with closure-spec contracts verifies.
///
/// This is the key Phase 1.5 test: `verified_closure_call` is NOT #[trusted], so
/// the driver must verify the body. The body calls f(x) which desugars to
/// `Fn::call`. The `Fn::call` spec's predicate postcondition is injected as a
/// call-site assumption, which should make the ensures clause provable.
#[test]
#[timeout(180_000)]
fn test_closure_verified_closure_call_non_trusted() {
    let output = run_cargo_trust_wp("closure_project", "verified_closure_call");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "verified_closure_call", "verified");
}

/// Tests singleton tuple contract syntax `(x,)` in closure-spec method calls.
#[test]
#[timeout(180_000)]
fn test_closure_verified_closure_call_tuple_contract() {
    let output = run_cargo_trust_wp("closure_project", "verified_closure_call_tuple_contract");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "verified_closure_call_tuple_contract", "verified");
}

/// Tests multi-item tuple contract syntax `(x, y)` in closure-spec method calls.
#[test]
#[timeout(180_000)]
fn test_closure_verified_closure_call_tuple_pair_contract() {
    let output = run_cargo_trust_wp(
        "closure_project",
        "verified_closure_call_tuple_pair_contract",
    );
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(
        &stderr,
        "verified_closure_call_tuple_pair_contract",
        "verified",
    );
}

/// Regression test for #478: missing callee precondition must fail.
///
/// `missing_call_precondition` calls `f(x)` and claims a postcondition but does
/// not establish `f.precondition(x)`. This was previously accepted unsoundly.
#[test]
#[timeout(180_000)]
fn test_closure_missing_call_precondition_fails() {
    let output = run_cargo_trust_wp("closure_project", "missing_call_precondition");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "missing_call_precondition should fail: {output:?}"
    );
    assert_function_status(&stderr, "missing_call_precondition", "FAILED");
}

/// Tests that the `closure_project` negative case fails.
#[test]
#[timeout(180_000)]
fn test_closure_simple_negative_fails() {
    let output = run_cargo_trust_wp("closure_project", "simple_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "simple_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "simple_negative", "FAILED");
}

// ============================================================================
// Phase 2: FnMut closure contract support (#358)
// ============================================================================

/// Tests that a trusted `FnMut` function with `postcondition_mut` is not a clean proof.
///
/// The key test: `#[ensures((*f).postcondition_mut(x, ^f, result))]` uses a
/// four-place predicate with `^f` (prophecy/final value). The ay encoder must
/// handle the `postcondition_mut` method name and `Final` expression.
#[test]
#[timeout(180_000)]
fn test_closure_fn_mut_trusted_non_proof() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_trusted");
    assert_trusted_non_proof(&output, "call_fn_mut_trusted");
}

/// Tests that a non-trusted `FnMut` function verifies via call-site assumptions.
///
/// This is the key Phase 2 test: `call_fn_mut_verified` is NOT #[trusted], so the
/// driver must verify the body. The body calls f(x) which desugars to
/// `FnMut::call_mut`. The spec's `postcondition_mut` predicate (with ^self for the
/// closure's post-state) is injected as a call-site assumption.
#[test]
#[timeout(180_000)]
fn test_closure_fn_mut_verified_non_trusted() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_verified");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "call_fn_mut_verified", "verified");
}

/// Tests that a wrong `FnMut` postcondition fails verification.
///
/// The function claims `result > x` but only has `postcondition_mut(x, ^f, result)`
/// available as an assumption — not enough to prove `result > x`.
#[test]
#[timeout(180_000)]
fn test_closure_fn_mut_negative_fails() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "call_fn_mut_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "call_fn_mut_negative", "FAILED");
}

/// Tests that a trusted chained `FnMut` call (two calls in one body) is not a clean proof.
///
/// Phase 2 AC#3: Chained `FnMut` calls track state correctly through prophecy
/// variables. This trusted variant verifies the contract parsing/encoding works
/// for the chained case without requiring the solver to reason about intermediate
/// prophecy states.
#[test]
#[timeout(180_000)]
fn test_closure_fn_mut_twice_trusted_non_proof() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_twice_trusted");
    assert_trusted_non_proof(&output, "call_fn_mut_twice_trusted");
}
