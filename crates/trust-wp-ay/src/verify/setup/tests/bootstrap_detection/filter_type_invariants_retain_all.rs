// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::{collections::HashSet, sync::Arc};

use ntest::timeout;
use trust_wp_core::{
    formula::{ExprSort, PureExpr},
    logic::type_invariant_method_name,
};

use super::*;
// Tests for filter_type_invariants_for_goal — retain_all path
// =============================================================================

/// When the expression references the unqualified name "invariant" and ALL
/// registered type invariants have trivially-true bodies, retain_all should fire:
/// all invariants are kept so `all_type_invariants_trivially_true()` can
/// short-circuit. (#1748)
#[test]
#[timeout(30000)]
fn filter_type_invariants_retains_all_when_invariant_name_and_all_trivial() {
    let inv_a = make_invariant("TypeA");
    let inv_b = make_invariant("TypeB");

    // Expression references the unqualified "invariant" name
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![],
    };

    let filtered = filter_type_invariants_for_goal(Some(&[inv_a, inv_b]), &[], &[expr], &[])
        .expect("should return Some");

    let names: HashSet<String> = filtered
        .into_iter()
        .map(|i| i.type_name().to_string())
        .collect();
    assert!(
        names.contains("TypeA") && names.contains("TypeB"),
        "all trivially-true invariants should be retained when 'invariant' is referenced: {names:?}"
    );
}

/// When "invariant" is referenced and at least one type invariant has a
/// non-trivial body, retain_all must still fire. Encoding can resolve the
/// unqualified AST call to a type-qualified UF using receiver sort context, so
/// dropping the definitions here leaves the resolved predicate unconstrained.
#[test]
#[timeout(30000)]
fn filter_type_invariants_retains_all_when_non_trivial_present() {
    let trivial_inv = make_invariant("Trivial");
    let non_trivial_inv = make_invariant_with_body(
        "NonTrivial",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    );

    // Expression references the unqualified "invariant" name
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![],
    };

    let filtered =
        filter_type_invariants_for_goal(Some(&[trivial_inv, non_trivial_inv]), &[], &[expr], &[])
            .expect("should return Some");

    let names: HashSet<String> = filtered
        .into_iter()
        .map(|i| i.type_name().to_string())
        .collect();
    assert!(
        names.contains("Trivial") && names.contains("NonTrivial"),
        "unqualified 'invariant' should retain all invariant definitions, got {names:?}"
    );
}

/// Verify that the transitive dependency closure works for chained element
/// invariants: Container → Middle → Elem.
#[test]
#[timeout(30000)]
fn filter_type_invariants_keeps_transitive_dependency_chain() {
    let elem = make_invariant("Elem");
    let elem_method = type_invariant_method_name("Elem");
    let middle = make_invariant("Middle").with_element_invariant_method(Some(elem_method.clone()));
    let middle_method = type_invariant_method_name("Middle");
    let container =
        make_invariant("Container").with_element_invariant_method(Some(middle_method.clone()));
    let container_method = type_invariant_method_name("Container");

    let ensure = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: container_method,
        args: vec![],
    };

    let filtered = filter_type_invariants_for_goal(
        Some(&[container.clone(), middle.clone(), elem.clone()]),
        &[],
        &[ensure],
        &[],
    )
    .expect("should return Some");

    let names: HashSet<String> = filtered
        .into_iter()
        .map(|i| i.type_name().to_string())
        .collect();
    assert!(
        names.contains("Container"),
        "directly referenced Container should be kept"
    );
    assert!(
        names.contains("Middle"),
        "transitive dep Middle should be kept"
    );
    assert!(names.contains("Elem"), "transitive dep Elem should be kept");
}

/// Verify that `None` input returns `None` (no filtering applied).
#[test]
#[timeout(30000)]
fn filter_type_invariants_none_input_returns_none() {
    let result = filter_type_invariants_for_goal(None, &[], &[], &[]);
    assert!(result.is_none(), "None input should return None");
}

// capture_field_type_name unit tests and end-to-end injection tests removed
// in #2257: invariant injection moved from ay bootstrap to driver clause
// enrichment (build_closure_capture_invariant_requires in type_invariants/clauses.rs).

/// Trivial invariant (body == true) should NOT add assertions — the result
/// should still verify because the postcondition is unconditionally true.
#[test]
#[timeout(30000)]
fn closure_capture_trivial_invariant_skipped() {
    use trust_wp_core::{
        closure::{CaptureField, CaptureKind, ClosureCaptureInfo},
        formula::intern_sort_name,
    };

    let inv = make_invariant("TrivialType");

    let trivial_id = intern_sort_name("TrivialType");
    let capture = CaptureField::new("x", ExprSort::Datatype(trivial_id), CaptureKind::ByValue);
    let capture_info =
        ClosureCaptureInfo::new("test::trivial_closure#0".to_string(), vec![capture]);

    // Postcondition: true (always provable)
    let ensures = PureExpr::Bool(true);

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], &[ensures])
            .type_invariants(Some(&[inv]))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "trivial invariant should not cause issues: {result:?}"
    );
}

/// Captures with no matching type invariant should not block verification.
#[test]
#[timeout(30000)]
fn closure_capture_no_matching_invariant() {
    use trust_wp_core::{
        closure::{CaptureField, CaptureKind, ClosureCaptureInfo},
        formula::{intern_sort_name, BinOp},
    };

    let inv = make_invariant_with_body(
        "OtherType",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    );

    let unrelated_id = intern_sort_name("UnrelatedType");
    let capture = CaptureField::new("x", ExprSort::Datatype(unrelated_id), CaptureKind::ByValue);
    let capture_info =
        ClosureCaptureInfo::new("test::no_match_closure#0".to_string(), vec![capture]);

    let ensures = PureExpr::Bool(true);

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], &[ensures])
            .type_invariants(Some(&[inv]))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "no matching invariant should not block: {result:?}"
    );
}
