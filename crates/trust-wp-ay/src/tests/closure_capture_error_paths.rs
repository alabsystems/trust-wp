// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error-path coverage for closure capture registration.
//!
//! Also covers partial capture binding scenarios where only some captured
//! variables have `_final` forms in scope (#1543 soundness audit).
//!
//! ## `assert_closure_capture_projections` unit tests
//!
//! Direct unit tests for the shared `assert_closure_capture_projections`
//! function in verify/mod.rs, covering auto-creation of post-state variables,
//! param_name skip guard, capture _final filtering, and sort-conflict
//! propagation. (#1489, #1543, #1623, #2625)

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::{Sort, Term};
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::super::*;
use crate::{
    encoder::AYEncoder,
    verify::{
        assert_captured_param_type_invariants, assert_closure_capture_projections,
        ClosureCaptureInfo, MutBorrowRequest, VerificationResult,
    },
    EncodingError,
};

/// Conflicting closure capture signatures for a single def_id must return an
/// encoding error through the mut-borrow request path. (#1485)
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_request_rejects_conflicting_closure_capture_signatures() {
    let captures = vec![
        crate::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![crate::CaptureField::new(
                "x",
                crate::ExprSort::Int,
                crate::CaptureKind::ByRef,
            )],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
        crate::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![crate::CaptureField::new(
                "x",
                crate::ExprSort::Bool,
                crate::CaptureKind::ByRef,
            )],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
    ];
    let final_values = HashMap::new();
    let request = MutBorrowRequest::new(&[], &[], &final_values).closure_captures(Some(&captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_err(),
        "conflicting closure capture signatures should return Err in mut-borrow path, got: {result:?}"
    );

    let msg = format!(
        "{}",
        result.expect_err("expected capture signature mismatch error")
    );
    assert!(
        msg.contains("changed capture signature"),
        "mut-borrow error should mention changed capture signature, got: {msg}"
    );
}

/// When a closure captures two variables but only one has a `_final` form in
/// the caller's scope, the auto-creation guard passes (because at least one
/// capture has `_final`), and only the available capture gets a projection
/// assertion. The unconstrained accessor is a known limitation (#1543 audit).
#[test]
#[timeout(30000)]
fn test_partial_capture_binding_succeeds_for_bound_capture_postcondition() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::partial_closure#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let ensures = vec![gt(var("x_final"), int(0))];
    let requires = vec![gt(deref(var("x")), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "partial capture binding should not error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "postcondition referencing only the bound capture (x) should verify, got: {verification:?}"
    );
}

/// When NO captured variable has a `_final` form in the caller's scope, the
/// auto-creation guard skips projection entirely. A non-tautological
/// postcondition that depends on the precondition should still verify,
/// proving the guard doesn't break the standard requires/ensures path.
/// (#1543 soundness audit, guard negative path)
#[test]
#[timeout(30000)]
fn test_no_capture_final_skips_projection_entirely() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::no_final_closure#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    // No final values at all — the guard condition `has_any_capture_final` is false.
    let final_values = HashMap::new();

    // Non-tautological postcondition: only provable given the precondition.
    // If the requires were dropped or broken, ensures(*x > 0) would fail.
    let requires = vec![gt(deref(var("x")), int(5))];
    let ensures = vec![gt(deref(var("x")), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "no-capture-final guard should skip projection without error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "precondition-dependent postcondition should verify when capture projection is skipped, got: {verification:?}"
    );
}

/// Guard negative path must fail on a non-tautological postcondition that
/// depends on an unbound capture-derived final variable.
#[test]
#[timeout(30000)]
fn test_no_capture_final_does_not_verify_unbound_capture_postcondition() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::no_final_unbound_post#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let final_values = HashMap::new();
    let requires = vec![];
    // Depends on capture-derived final state, but no capture `_final` exists in scope.
    let ensures = vec![gt(var("x_final"), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "no-capture-final path should not encoding-error on unbound postcondition: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Failed(_)),
        "unbound capture postcondition should fail when projection is skipped, got: {verification:?}"
    );
}

/// With partial bindings, postconditions that depend on an unbound capture
/// should fail even when another capture is bound.
#[test]
#[timeout(30000)]
fn test_partial_capture_binding_does_not_verify_unbound_capture_postcondition() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::partial_unbound_post#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let requires = vec![gt(deref(var("x")), int(0))];
    // y_final is unbound because only x has a `_final` binding.
    let ensures = vec![gt(var("y_final"), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "partial-binding path should not encoding-error on unbound capture postcondition: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Failed(_)),
        "unbound capture postcondition should fail under partial bindings, got: {verification:?}"
    );
}

/// Compute FNV-1a hash suffix used by closure symbol naming.
fn closure_suffix(def_id: &str) -> String {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for byte in def_id.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{hash:016x}")
}

/// Set up an encoder with a 2-capture closure sort and partial projection
/// binding (only capture 0 is bound). Returns (encoder, sort, suffix).
fn setup_partial_projection() -> (AYEncoder, Sort, String) {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let def_id = "test::partial_proj";
    let captures = vec![
        crate::CaptureField::new("x", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        crate::CaptureField::new("y", crate::ExprSort::Int, crate::CaptureKind::ByRef),
    ];
    let sort = encoder
        .register_closure_struct_sort(def_id, &captures)
        .unwrap();

    encoder.get_or_declare_var("c_final", sort.clone()).unwrap();

    let partial_bindings = vec![(0_usize, "x_final".to_string())];
    encoder
        .assert_capture_projection(def_id, "c_final", &partial_bindings)
        .expect("partial projection should succeed");

    (encoder, sort, closure_suffix(def_id))
}

/// Bound capture (index 0) is constrained by the projection assertion.
/// Asserting `capture_0(c_final) != x_final` should be UNSAT.
#[test]
#[timeout(30000)]
fn test_partial_capture_bound_accessor_is_constrained() {
    let (mut encoder, sort, suffix) = setup_partial_projection();

    let x_final = encoder.get_or_declare_var("x_final", Sort::Int).unwrap();
    let c_final_term = encoder.get_or_declare_var("c_final", sort).unwrap();
    // With native datatypes (#2151), use try_datatype_selector instead of UF accessor.
    let selector_name = format!("closure_capture_{suffix}_0");
    let projected_0 = encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, c_final_term, Sort::Int)
        .expect("selector 0 should exist");
    let eq_0 = encoder.solver.eq(projected_0, x_final);
    let neq_0 = encoder.solver.not(eq_0);

    encoder.solver.push();
    encoder.solver.assert_term(neq_0);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_)),
        "capture_0(c_final) should be constrained to equal x_final"
    );
    encoder.solver.pop();
}

/// Unbound capture (index 1) has no projection assertion, so asserting it equals
/// an arbitrary value is satisfiable: the accessor is underconstrained. This
/// documents the #1543 audit gap without accepting an arbitrary non-Unsat result.
#[test]
#[timeout(30000)]
fn test_partial_capture_unbound_accessor_is_not_fully_constrained() {
    let (mut encoder, sort, suffix) = setup_partial_projection();

    let c_final_term = encoder.get_or_declare_var("c_final", sort).unwrap();
    // With native datatypes (#2151), use try_datatype_selector instead of UF accessor.
    let selector_name = format!("closure_capture_{suffix}_1");
    let projected_1 = encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, c_final_term, Sort::Int)
        .expect("selector 1 should exist");
    let arbitrary_val = encoder.solver_mut().int_const(42);
    let eq_1 = encoder.solver_mut().eq(projected_1, arbitrary_val);

    encoder.solver.push();
    encoder.solver.assert_term(eq_1);
    let result = encoder.check_sat();
    // The unbound accessor is not constrained by any projection assertion, so
    // capture_1(c_final) == 42 must remain satisfiable.
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "unbound capture accessor should remain satisfiable, got: {result:?}"
    );
    encoder.solver.pop();
}

/// When `param_name` is `None` on a `ClosureCaptureInfo` entry, the projection
/// loop must skip it entirely without error. This tests the `param_name`
/// guard in `assert_closure_capture_projections`. (#1485 error path audit)
#[test]
#[timeout(30000)]
fn test_missing_param_name_skips_projection_without_error() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::missing_param_name#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            crate::CaptureKind::ByRef,
        )],
        param_name: None, // No param_name — must be skipped
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let final_values = HashMap::new();
    let requires = vec![gt(deref(var("x")), int(5))];
    let ensures = vec![gt(deref(var("x")), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "missing param_name should skip projection without error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "precondition-dependent postcondition should verify when param_name is None, got: {verification:?}"
    );
}

/// A closure with an empty captures list should be a no-op — no projection
/// assertions, no errors. Tests both the register path and the projection
/// orchestration. (#1485 error path audit)
#[test]
#[timeout(30000)]
fn test_empty_captures_list_is_noop() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::empty_captures#0".to_string(),
        captures: vec![], // No captures at all
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let final_values = HashMap::new();
    let requires = vec![gt(deref(var("x")), int(5))];
    let ensures = vec![gt(deref(var("x")), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "empty captures should not error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "empty captures should not interfere with standard verification, got: {verification:?}"
    );
}

/// Three captures, non-contiguous bindings (indices 0 and 2 bound, 1 unbound).
/// Postcondition referencing the bound captures should verify; the unbound
/// capture must remain unconstrained. (#1543 boundary audit)
#[test]
#[timeout(30000)]
fn test_non_contiguous_capture_bindings_verify_bound_captures() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::non_contiguous#0".to_string(),
        captures: vec![
            crate::CaptureField::new("a", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("b", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("c_cap", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        ],
        param_name: Some("cls".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let mut final_values = HashMap::new();
    // Only a and c_cap have _final forms; b does not.
    final_values.insert("a".to_string(), deref(var("a")));
    final_values.insert("c_cap".to_string(), deref(var("c_cap")));

    let requires = vec![gt(deref(var("a")), int(0)), gt(deref(var("c_cap")), int(0))];
    // Postcondition depends only on bound captures
    let ensures = vec![gt(var("a_final"), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "non-contiguous bindings should not error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "postcondition on bound capture (index 0) should verify with non-contiguous bindings, got: {verification:?}"
    );
}

/// ByMutRef capture kind exercises the prophecy-preserving path in
/// `axioms.rs` (`hist_inv` axiom). With a single ByMutRef capture, the
/// caller's final variable should flow through the capture projection
/// exactly as with ByRef. The CaptureKind distinction matters in
/// `hist_inv` axiom generation (ByRef constrains no-change; ByMutRef
/// allows change), but the structural projection in `verify/mod.rs`
/// is kind-agnostic. This test validates that ByMutRef does not regress
/// the projection pipeline. (#1543 soundness audit, CaptureKind gap)
#[test]
#[timeout(30000)]
fn test_by_mut_ref_capture_projection_verifies_postcondition() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::bymutref_capture#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            crate::CaptureKind::ByMutRef,
        )],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // Precondition: *x > 5. Postcondition: x_final > 0 (weaker, should verify).
    let requires = vec![gt(deref(var("x")), int(5))];
    let ensures = vec![gt(var("x_final"), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "ByMutRef capture should not error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "ByMutRef capture projection should verify weaker postcondition, got: {verification:?}"
    );
}

/// Mixed capture kinds in a single closure: one ByRef (shared, immutable)
/// and one ByMutRef (mutable, prophecy-preserving). Both should bind through
/// projection when `_final` forms exist. Tests that kind heterogeneity does
/// not break the sort registration or projection assertion pipeline.
#[test]
#[timeout(30000)]
fn test_mixed_capture_kinds_both_project_correctly() {
    use crate::tests::helpers::*;

    let closure_captures = vec![crate::closure_capture_info! {
        def_id: "test::mixed_kinds#0".to_string(),
        captures: vec![
            crate::CaptureField::new("r", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("m", crate::ExprSort::Int, crate::CaptureKind::ByMutRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(var("r")));
    final_values.insert("m".to_string(), deref(var("m")));

    // Postcondition references both captures' final forms.
    let requires = vec![gt(deref(var("r")), int(0)), gt(deref(var("m")), int(0))];
    let ensures = vec![gt(var("r_final"), int(0)), gt(var("m_final"), int(0))];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "mixed ByRef+ByMutRef should not error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "mixed capture kinds should both project and verify, got: {verification:?}"
    );
}

// ---------------------------------------------------------------------------
// assert_closure_capture_projections: direct unit tests (#1489, #1543, #1623)
// ---------------------------------------------------------------------------

/// Helper: build a single-capture ClosureCaptureInfo.
fn single_capture_info(
    def_id: &str,
    capture_name: &str,
    sort: crate::ExprSort,
    param_name: Option<&str>,
) -> ClosureCaptureInfo {
    crate::closure_capture_info! {
        def_id: def_id.to_string(),
        captures: vec![crate::CaptureField::new(capture_name, sort, crate::CaptureKind::ByRef)],
        param_name: param_name.map(str::to_string),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }
}

/// Captures with `param_name: None` must be skipped entirely.
///
/// When MIR analysis can't determine which parameter holds the closure,
/// `param_name` is None and no projection assertions should be generated.
///
/// Re: #1489 — param_name is optional
#[test]
#[timeout(30000)]
fn test_capture_projection_skip_when_param_name_is_none() {
    let mut encoder = AYEncoder::new();
    let info = single_capture_info("test::no_param#0", "x", crate::ExprSort::Int, None);

    // Pre-declare x_final to ensure skipping is due to param_name, not missing vars.
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("declare x_final");

    let result = assert_closure_capture_projections(&mut encoder, &[info], "[test] ");
    assert!(result.is_ok(), "param_name=None should succeed: {result:?}");

    // Verify no c_final variable was created.
    let var_names: std::collections::HashSet<String> = encoder.var_names().into_iter().collect();
    assert!(
        !var_names.contains("c_final"),
        "no post-state var should be created when param_name is None"
    );
}

/// When no captured variable has a `_final` form in scope, the function
/// skips the projection (no auto-creation of the closure post-state var).
///
/// Re: #1543 — partial capture binding soundness
#[test]
#[timeout(30000)]
fn test_capture_projection_skip_when_no_capture_final_vars() {
    let mut encoder = AYEncoder::new();
    let info = single_capture_info("test::no_finals#0", "x", crate::ExprSort::Int, Some("c"));

    // DON'T declare x_final — only x (non-final).
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let result = assert_closure_capture_projections(&mut encoder, &[info], "[test] ");
    assert!(
        result.is_ok(),
        "no capture _final vars should succeed: {result:?}"
    );

    // c_final should NOT be created.
    let var_names: std::collections::HashSet<String> = encoder.var_names().into_iter().collect();
    assert!(
        !var_names.contains("c_final"),
        "c_final should not be created when no capture _final vars exist"
    );
}

/// When a captured variable HAS a `_final` form in scope but the closure
/// post-state var doesn't exist yet, the function auto-creates it with
/// the registered closure struct sort.
///
/// Re: #1543 — auto-creation of closure post-state variables
#[test]
#[timeout(30000)]
fn test_capture_projection_auto_creates_post_state_var() {
    let mut encoder = AYEncoder::new();
    let info = single_capture_info("test::auto_create#0", "x", crate::ExprSort::Int, Some("c"));

    // Register the closure sort so auto-creation can retrieve it.
    let _sort = encoder
        .register_closure_struct_sort("test::auto_create#0", info.captures())
        .expect("register closure sort");

    // Declare x_final — this triggers the auto-creation path.
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("declare x_final");

    // c_final should NOT exist yet.
    let var_names_before: std::collections::HashSet<String> =
        encoder.var_names().into_iter().collect();
    assert!(
        !var_names_before.contains("c_final"),
        "precondition: c_final should not exist before call"
    );

    let result = assert_closure_capture_projections(&mut encoder, &[info], "[test] ");
    assert!(result.is_ok(), "auto-creation should succeed: {result:?}");

    // c_final should now exist (auto-created).
    let var_names_after: std::collections::HashSet<String> =
        encoder.var_names().into_iter().collect();
    assert!(
        var_names_after.contains("c_final"),
        "c_final should be auto-created when x_final exists in scope"
    );
}

/// When `{param}_final` already exists (pre-declared by MIR analysis),
/// projections are asserted directly without auto-creation.
///
/// Re: #1489 — standard projection path
#[test]
#[timeout(30000)]
fn test_capture_projection_existing_post_state_var() {
    let mut encoder = AYEncoder::new();
    let info = single_capture_info("test::pre_declared#0", "x", crate::ExprSort::Int, Some("c"));

    let closure_sort = encoder
        .register_closure_struct_sort("test::pre_declared#0", info.captures())
        .expect("register closure sort");

    encoder
        .get_or_declare_var("c_final", closure_sort)
        .expect("declare c_final");
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("declare x_final");

    let result = assert_closure_capture_projections(&mut encoder, &[info], "[test] ");
    assert!(
        result.is_ok(),
        "pre-declared post-state var should succeed: {result:?}"
    );
}

/// Multi-capture: only captures with `_final` forms in scope get projections.
/// If a closure captures (x, y) but only x_final exists, only the x
/// projection is asserted. y is unconstrained — a known limitation (#1543).
///
/// Re: #1543 — partial capture binding
#[test]
#[timeout(30000)]
fn test_capture_projection_partial_binding_only_available_finals() {
    let mut encoder = AYEncoder::new();

    let info = crate::closure_capture_info! {
        def_id: "test::partial#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, crate::CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, crate::CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    let _sort = encoder
        .register_closure_struct_sort("test::partial#0", info.captures())
        .expect("register closure sort");

    // Only declare x_final — y_final is missing.
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("declare x_final");

    let result = assert_closure_capture_projections(&mut encoder, &[info], "[test] ");
    assert!(
        result.is_ok(),
        "partial capture binding should succeed: {result:?}"
    );

    // c_final should be auto-created (x_final triggers the guard).
    let var_names: std::collections::HashSet<String> = encoder.var_names().into_iter().collect();
    assert!(
        var_names.contains("c_final"),
        "c_final should be auto-created since x_final is in scope"
    );
}

/// Empty captures list produces no assertions and no errors.
#[test]
#[timeout(30000)]
fn test_capture_projection_empty_is_noop() {
    let mut encoder = AYEncoder::new();
    let result = assert_closure_capture_projections(&mut encoder, &[], "[test] ");
    assert!(result.is_ok(), "empty captures should succeed: {result:?}");
}

/// When `{param}_final` already exists with an incompatible sort, projection
/// setup must fail closed with a structured sort conflict error.
///
/// Re: #1623, #2625 — closure post-state var declaration/projection handling
#[test]
#[timeout(30000)]
fn test_capture_projection_existing_post_state_var_sort_conflict_returns_error() {
    let mut encoder = AYEncoder::new();
    let info = single_capture_info("test::conflict#0", "x", crate::ExprSort::Int, Some("c"));

    let _closure_sort = encoder
        .register_closure_struct_sort("test::conflict#0", info.captures())
        .expect("register closure sort");

    // Pre-declare c_final as Bool; unlike Int, Bool is not eligible for the
    // existing speculative upgrade path and must surface a real sort conflict.
    encoder
        .get_or_declare_var("c_final", Sort::Bool)
        .expect("declare c_final as Bool");

    // Declare x_final to trigger the auto-creation path.
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("declare x_final");

    let result = assert_closure_capture_projections(&mut encoder, &[info], "[test] ");
    assert!(
        matches!(result, Err(EncodingError::SortConflict { .. })),
        "existing post-state sort conflict should propagate as SortConflict: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// assert_captured_param_type_invariants: direct unit tests
// ---------------------------------------------------------------------------

/// Build the `Zero` invariant body `self.0@ == 0` using positional tuple access
/// (the normalized form the driver produces): `__trust_wp_tuple_get_0(self) == 0`.
fn zero_invariant_body(zero_sort_expr: &crate::ExprSort) -> PureExpr {
    use trust_wp_core::formula::BinOp;
    PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var(
                "self".to_string(),
                Some(zero_sort_expr.clone()),
            )],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )
}

/// Register a `Zero { 0: Int, 1: Int }` ADT on `encoder` and return the interned
/// `Zero` `ExprSort` (named `type_name`) and the matching `TypeInvariantDef`
/// (`self.0@ == 0`). Mirrors the ground-pool Datatype invariant tests.
fn register_zero_adt_and_inv(
    encoder: &mut AYEncoder,
    type_name: &str,
) -> (crate::ExprSort, trust_wp_core::logic::TypeInvariantDef) {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind, TypeInvariantDef},
    };

    let zero_sort_expr = crate::ExprSort::Datatype(intern_sort_name(type_name));
    let adt_decls = std::collections::HashMap::from([(
        type_name.to_string(),
        AdtDecl::new(
            type_name.to_string(),
            type_name.to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                type_name.to_string(),
                type_name.to_string(),
                vec![
                    AdtFieldDecl::new("0".to_string(), crate::ExprSort::Int),
                    AdtFieldDecl::new("1".to_string(), crate::ExprSort::Int),
                ],
            )],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let registered_zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());
    let Sort::Datatype(_) = registered_zero_sort.clone() else {
        panic!("registered Zero sort should be a native datatype");
    };

    let body = zero_invariant_body(&zero_sort_expr);
    let inv_def = TypeInvariantDef::new(type_name.to_string(), "self".to_string(), body)
        .with_param_sort(Some(zero_sort_expr.clone()));

    (zero_sort_expr, inv_def)
}

/// Build the negated proof goal `recv.0@ != 0` over the named `Zero` var.
fn negated_field0_goal(
    encoder: &mut AYEncoder,
    var: &str,
    zero_sort_expr: &crate::ExprSort,
) -> Term {
    use trust_wp_core::formula::BinOp;
    let goal = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var(var.to_string(), Some(zero_sort_expr.clone()))],
        }),
        BinOp::Ne,
        Arc::new(PureExpr::Int(0)),
    );
    let term = encoder.encode_pure(&goal).expect("encode negated goal");
    encoder.coerce_bool_operand(term)
}

/// Build the driver-injected opaque invariant precondition `inv_<type>(recv)`
/// for the given invariant type name and receiver variable. This is the exact
/// shape `build_closure_capture_invariant_requires` produces and is the
/// soundness gate the helper requires before materializing the body.
fn capture_invariant_requires(type_name: &str, recv: &str) -> Vec<PureExpr> {
    vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(recv.to_string(), None)),
        method: trust_wp_core::logic::type_invariant_method_name(type_name),
        args: vec![],
    }]
}

/// Build a single-capture info for capture `x` of the given sort, with the
/// closure self as the receiver (`param_name == Some("self")`).
fn zero_self_capture_info(sort: crate::ExprSort) -> ClosureCaptureInfo {
    crate::closure_capture_info! {
        def_id: "creusot_test::f::{closure#0}".to_string(),
        captures: vec![crate::CaptureField::new("x", sort, crate::CaptureKind::ByValue)],
        param_name: Some("self".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }
}

/// POSITIVE: a `Zero` capture `x` in scope makes the substituted invariant body
/// (`x.0@ == 0`) a ground hypothesis, so the negated goal `x.0@ != 0` is UNSAT.
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_makes_field_constraint_unsat() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_all();
    let (zero_sort_expr, inv_def) = register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());

    // Declare the captured entry var x (Zero sort) so it participates in the VC.
    encoder
        .get_or_declare_var("x", zero_sort)
        .expect("declare x");

    let info = zero_self_capture_info(zero_sort_expr.clone());
    // The driver injected `inv_Zero(x)` — the soundness gate is satisfied, so
    // the helper materializes the body.
    let requires = capture_invariant_requires("creusot_test::Zero", "x");
    assert_captured_param_type_invariants(&mut encoder, &[info], Some(&[inv_def]), &requires)
        .expect("assert captured invariant should succeed");

    let goal = negated_field0_goal(&mut encoder, "x", &zero_sort_expr);
    encoder.assert_term(goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "with the captured invariant hypothesis, x.0@ != 0 must be UNSAT, got {result:?}"
    );
}

/// SOUNDNESS GATE: the helper IS called and the `Zero` capture `x` IS in scope,
/// but the driver did NOT inject the `inv_Zero(x)` precondition (empty
/// `requires`). The helper must NOT materialize the invariant body, because the
/// program never established it. The negated goal `x.0@ != 0` therefore stays
/// SAT (the VC correctly cannot certify safety). Without this gate the helper
/// would fabricate `x.0@ == 0` from nothing, a false-accept.
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_requires_injected_precondition() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_all();
    let (zero_sort_expr, inv_def) = register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());

    encoder
        .get_or_declare_var("x", zero_sort)
        .expect("declare x");

    let info = zero_self_capture_info(zero_sort_expr.clone());
    // No matching `inv_Zero(x)` requires was injected: the gate must fail closed.
    assert_captured_param_type_invariants(&mut encoder, &[info], Some(&[inv_def]), &[])
        .expect("helper should be a no-op without the injected precondition");

    let goal = negated_field0_goal(&mut encoder, "x", &zero_sort_expr);
    encoder.assert_term(goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "without the injected inv_Zero(x) precondition the body must NOT be \
         asserted; x.0@ != 0 must stay SAT, got {result:?}"
    );
}

/// NEGATIVE CONTROL: the SAME setup WITHOUT calling the helper leaves `x.0@`
/// unconstrained, so the negated goal `x.0@ != 0` is SAT. Proves the helper is
/// load-bearing (this is exactly the closures/10_tyinv false-SAT).
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_negative_control_is_sat_without_helper() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_all();
    let (zero_sort_expr, _inv_def) = register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());

    encoder
        .get_or_declare_var("x", zero_sort)
        .expect("declare x");

    // Intentionally DO NOT call assert_captured_param_type_invariants.

    let goal = negated_field0_goal(&mut encoder, "x", &zero_sort_expr);
    encoder.assert_term(goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "without the helper, x.0@ is unconstrained so x.0@ != 0 must be SAT, got {result:?}"
    );
}

/// GUARD (a): only the `_final` (prophecy) var is in scope — the helper must
/// assert nothing, so the negated goal over the final field stays SAT.
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_skips_final_only_scope() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_all();
    let (zero_sort_expr, inv_def) = register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());

    // Only x_final in scope; the entry var x is absent.
    encoder
        .get_or_declare_var("x_final", zero_sort)
        .expect("declare x_final");

    let info = zero_self_capture_info(zero_sort_expr.clone());
    // Even though the invariant requires for `x` was injected, only `x_final`
    // is in scope: the _final/in-scope guard must keep this a no-op.
    let requires = capture_invariant_requires("creusot_test::Zero", "x");
    assert_captured_param_type_invariants(&mut encoder, &[info], Some(&[inv_def]), &requires)
        .expect("helper should be a no-op for final-only scope");

    // x_final.0@ != 0 must remain SAT (no body was asserted for x_final).
    let goal = negated_field0_goal(&mut encoder, "x_final", &zero_sort_expr);
    encoder.assert_term(goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "helper must not assert the invariant on a _final var; x_final.0@ != 0 should be SAT, got {result:?}"
    );
}

/// GUARD (b): a trivial `Bool(true)` invariant body adds no constraint, so the
/// negated goal stays SAT.
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_skips_trivial_body() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::logic::TypeInvariantDef;

    let mut encoder = AYEncoder::new_all();
    let (zero_sort_expr, _inv_def) = register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());

    encoder
        .get_or_declare_var("x", zero_sort)
        .expect("declare x");

    // TRIVIAL invariant body for the same type.
    let trivial_inv = TypeInvariantDef::new(
        "creusot_test::Zero".to_string(),
        "self".to_string(),
        PureExpr::Bool(true),
    )
    .with_param_sort(Some(zero_sort_expr.clone()));

    let info = zero_self_capture_info(zero_sort_expr.clone());
    // The invariant requires for `x` was injected, but the body is `true`: the
    // trivial-body guard must keep this a no-op.
    let requires = capture_invariant_requires("creusot_test::Zero", "x");
    assert_captured_param_type_invariants(&mut encoder, &[info], Some(&[trivial_inv]), &requires)
        .expect("trivial body should be skipped");

    let goal = negated_field0_goal(&mut encoder, "x", &zero_sort_expr);
    encoder.assert_term(goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "trivial invariant body adds nothing; x.0@ != 0 should stay SAT, got {result:?}"
    );
}

/// GUARD (c): a capture whose type has NO matching invariant is a no-op.
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_no_matching_def_is_noop() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_all();
    // Invariant def is for "Zero", but the capture resolves to "Foo".
    let (_zero_sort_expr, inv_def) = register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let foo_sort_expr = crate::ExprSort::Datatype(intern_sort_name("creusot_test::Foo"));

    // Declare x as a plain Int so the unrelated capture sort doesn't matter.
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let info = zero_self_capture_info(foo_sort_expr);
    // No invariant matches the `Foo` capture, so there is no requires to inject
    // and the no-matching-def guard makes this a no-op.
    let result =
        assert_captured_param_type_invariants(&mut encoder, &[info], Some(&[inv_def]), &[]);
    assert!(
        result.is_ok(),
        "no matching def should be a no-op: {result:?}"
    );

    // x (an unconstrained Int) is free, so x != 0 is SAT — nothing was asserted.
    let goal = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), Some(crate::ExprSort::Int))),
        trust_wp_core::formula::BinOp::Ne,
        Arc::new(PureExpr::Int(0)),
    );
    let term = encoder.encode_pure(&goal).expect("encode goal");
    let term = encoder.coerce_bool_operand(term);
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "no matching invariant means no constraint; x != 0 should be SAT, got {result:?}"
    );
}

/// GUARD (d): suffix matching — invariant registered as crate-qualified
/// `creusot_test::Zero`, capture resolves to unqualified `Zero` → suffix
/// fallback matches and the body is asserted (negated goal becomes UNSAT).
#[test]
#[timeout(30000)]
fn test_captured_param_type_invariant_suffix_match() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_all();
    // The native ADT and invariant def use the crate-qualified name.
    let (qualified_sort_expr, inv_def) =
        register_zero_adt_and_inv(&mut encoder, "creusot_test::Zero");
    let zero_sort = encoder.sort_from_expr_sort(qualified_sort_expr);

    // The capture, however, resolves to the UNQUALIFIED name "Zero". To keep the
    // term-level field access unifying with the native datatype, declare x with
    // the registered Zero datatype sort but annotate the capture/goal with the
    // unqualified ExprSort so the suffix fallback is exercised during matching.
    let unqualified_sort_expr = crate::ExprSort::Datatype(intern_sort_name("Zero"));

    encoder
        .get_or_declare_var("x", zero_sort)
        .expect("declare x");

    let info = zero_self_capture_info(unqualified_sort_expr.clone());
    // The driver injects the requires using the invariant def's own (qualified)
    // type name — `type_invariant_method_name("creusot_test::Zero")` — which is
    // exactly the method the helper looks for. The gate is satisfied and the
    // body is materialized via the suffix fallback.
    let requires = capture_invariant_requires("creusot_test::Zero", "x");
    assert_captured_param_type_invariants(&mut encoder, &[info], Some(&[inv_def]), &requires)
        .expect("suffix match should assert the body");

    let goal = negated_field0_goal(&mut encoder, "x", &unqualified_sort_expr);
    encoder.assert_term(goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "suffix-matched invariant body should make x.0@ != 0 UNSAT, got {result:?}"
    );
}
