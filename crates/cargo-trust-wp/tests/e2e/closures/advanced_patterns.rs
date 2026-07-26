// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Advanced closure patterns — Phase 5-6 (#358).
//!
//! Fn→FnMut weakening, move closures, nested closures, repeated Fn calls,
//! and generic Fn bound with unit return.

use ntest::timeout;

use crate::support::{
    assert_function_status, assert_trusted_non_proof, run_cargo_trust_wp, status_code,
    stderr_string,
};

// ============================================================================
// Phase 5: Fn→FnMut weakening and advanced patterns (#358)
// ============================================================================

/// Tests Fn → `FnMut` weakening via the `fn_mut` law (#520).
///
/// `weaken_fn_to_fn_mut` takes `&mut F` where `F: Fn`, ensuring `postcondition_mut`.
/// The `fn_mut` law connects Fn's `postcondition` to `FnMut`'s `postcondition_mut`:
///   `postcondition_mut(self, args, res_state, result)` =
///     (`postcondition(self, args, result)` && self == `res_state`)
///
/// The driver synthesizes identity final values (`f_final = f`) when it detects
/// `^f` in ensures but only `Fn::call` assumptions (not `FnMut`). This constrains
/// the prophecy variable so the `fn_mut` law's `self == res_state` is provable.
#[test]
#[timeout(180_000)]
fn test_closure_phase5_weaken_fn_to_fn_mut() {
    let output = run_cargo_trust_wp("closure_project", "weaken_fn_to_fn_mut");
    let stderr = stderr_string(&output);
    // Substring filter matches both weaken_fn_to_fn_mut (should verify) and
    // weaken_fn_to_fn_mut_negative (should fail), so exit code is 1.
    // Check that the positive case verifies.
    assert_function_status(&stderr, "weaken_fn_to_fn_mut", "verified");
}

/// Negative test: Fn → `FnMut` weakening with wrong postcondition.
#[test]
#[timeout(180_000)]
fn test_closure_phase5_weaken_fn_to_fn_mut_negative() {
    let output = run_cargo_trust_wp("closure_project", "weaken_fn_to_fn_mut_negative");
    let stderr = stderr_string(&output);
    let code = status_code(&output);
    assert_eq!(
        code, 1,
        "wrong postcondition should exit with code 1: {stderr}"
    );
    assert_function_status(&stderr, "weaken_fn_to_fn_mut_negative", "FAILED");
}

/// Tests non-trusted double `FnMut` call — expected to FAIL.
///
/// `call_fn_mut_twice_verified` calls `f(x)` twice without #[trusted].
/// The contract `postcondition_mut(*f, x, ^f, result)` claims a single-call
/// relationship between the initial state `*f` and final state `^f`, but
/// the body performs TWO mutations: the actual final state is `Final(Final(f))`,
/// not `Final(f)`. The second call's precondition `precondition(f_final, x)`
/// is also unprovable without precondition-preservation assumptions.
///
/// Previously passed due to a bug where pass-1 substitution extraction
/// leaked wrong assumptions (with un-advanced receiver state) into
/// CALL_ASSUMPTIONS, which accidentally matched the postcondition goal.
/// Fixed in #1310 by gating CALL_ASSUMPTIONS recording in pass 1.
#[test]
#[timeout(180_000)]
fn test_closure_phase5_fn_mut_twice_verified() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_mut_twice_verified");
    let stderr = stderr_string(&output);
    // Contract is unsound for double FnMut call — verification should fail (#1310)
    assert_function_status(&stderr, "call_fn_mut_twice_verified", "FAILED");
}

// ============================================================================
// Phase 6: Structural closure patterns — nested, move, multiple Fn calls
// Adapted from Creusot 01_basic, 02_nested, 03_generic_bound, 08_multiple_calls
// ============================================================================

// ── Move closures (Creusot 01_basic.rs move pattern) ─────────────────────

#[test]
#[timeout(180_000)]
fn test_closure_phase6_move_closure_positive() {
    let output = run_cargo_trust_wp("closure_project", "phase6_move_closure_positive");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase6_move_closure_positive", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase6_move_closure_negative() {
    let output = run_cargo_trust_wp("closure_project", "phase6_move_closure_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "phase6_move_closure_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "phase6_move_closure_negative", "FAILED");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase6_move_closure_two_captures() {
    let output = run_cargo_trust_wp("closure_project", "phase6_move_closure_two_captures");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase6_move_closure_two_captures", "verified");
}

// ── Nested closures (Creusot 02_nested.rs pattern) ───────────────────────

#[test]
#[timeout(180_000)]
fn test_closure_phase6_nested_closure_define() {
    let output = run_cargo_trust_wp("closure_project", "phase6_nested_closure_define");
    // Filter substring matches both phase6_nested_closure_define and
    // phase6_nested_closure_define_negative. Don't check exit code —
    // the negative variant intentionally fails. Check for "verified" marker.
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "phase6_nested_closure_define", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase6_nested_closure_define_negative() {
    let output = run_cargo_trust_wp("closure_project", "phase6_nested_closure_define_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "phase6_nested_closure_define_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "phase6_nested_closure_define_negative", "FAILED");
}

// ── Multiple Fn calls (Creusot 08_multiple_calls.rs pattern) ─────────────

#[test]
#[timeout(180_000)]
fn test_closure_phase6_call_fn_twice_trusted() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_twice_trusted");
    assert_trusted_non_proof(&output, "call_fn_twice_trusted");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase6_call_fn_twice_verified() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_twice_verified");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "call_fn_twice_verified", "verified");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase6_call_fn_twice_negative() {
    let output = run_cargo_trust_wp("closure_project", "call_fn_twice_negative");
    let stderr = stderr_string(&output);
    assert!(
        !output.status.success(),
        "call_fn_twice_negative should fail: {output:?}"
    );
    assert_function_status(&stderr, "call_fn_twice_negative", "FAILED");
}

// ── Generic Fn bound with unit return (Creusot 03_generic_bound.rs) ──────

#[test]
#[timeout(180_000)]
fn test_closure_phase6_apply_fn_unit_trusted() {
    let output = run_cargo_trust_wp("closure_project", "apply_fn_unit_trusted");
    assert_trusted_non_proof(&output, "apply_fn_unit_trusted");
}

#[test]
#[timeout(180_000)]
fn test_closure_phase6_apply_fn_unit_verified() {
    let output = run_cargo_trust_wp("closure_project", "apply_fn_unit_verified");
    assert!(output.status.success(), "cargo-trust-wp failed: {output:?}");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "apply_fn_unit_verified", "verified");
}
