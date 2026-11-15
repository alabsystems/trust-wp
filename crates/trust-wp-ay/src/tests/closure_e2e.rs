// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end closure verification tests (#758 AC3, AC4).
//!
//! These tests exercise per-capture hist_inv decomposition and structural
//! resolve through the full verification pipeline (verify_function_with_modes
//! and encoder-level axiom chains).
//!
//! Extracted from closure_layer3.rs to stay within the 500-line file limit.

use std::sync::Arc;

use ntest::timeout;

use super::{super::*, helpers::*};
use crate::encoder::closure_sorts::closure_env_sort_name;

// ============================================================================
// End-to-end FnMut mixed-capture verification (#758 AC3)
// ============================================================================

/// FnMut closure with mixed captures (ByRef + ByMutRef) via verify_function_with_modes.
///
/// Simulates a closure that captures `&x` (shared, immutable) and `&mut y` (mutable).
/// After a postcondition_mut call, the precondition provides `^y == y + 1`.
/// Postcondition asserts `^y == y + 1` (provable from precondition).
///
/// Exercises per-capture hist_inv through the full verification pipeline with
/// closure_captures registration. Re: #758 AC3.
#[test]
#[timeout(30000)]
fn test_fnmut_mixed_captures_verify_e2e() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let capture_info = crate::closure_capture_info! {
        def_id: "e2e::fnmut_mixed#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    // Precondition 1: c.postcondition_mut((), ^c, call_0)
    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(0),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    // Precondition 2: ^y == y + 1 (closure spec: mutable capture incremented)
    let y_final_eq_y_plus_1 = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: ^y == y + 1 (provable from precondition)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[postcondition_mut_assumption, y_final_eq_y_plus_1],
            &[ensures],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "FnMut mixed-capture ^y == y + 1 should verify: {result:?}"
    );
}

/// Negative test: FnMut mixed captures with wrong postcondition fails.
///
/// Same setup as above but postcondition claims `^y == y + 2` (wrong — the
/// precondition only provides `^y == y + 1`). Verifies the test above is not
/// tautological.
#[test]
#[timeout(30000)]
fn test_fnmut_mixed_captures_wrong_postcondition_fails() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let capture_info = crate::closure_capture_info! {
        def_id: "e2e::fnmut_mixed_neg#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, CaptureKind::ByRef),
            crate::CaptureField::new("y", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(0),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let y_final_eq_y_plus_1 = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Wrong postcondition: ^y == y + 2 (should fail)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        )),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[postcondition_mut_assumption, y_final_eq_y_plus_1],
            &[ensures],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        crate::tests::rejected(&result),
        "FnMut mixed-capture ^y == y + 2 should fail (precondition gives +1): {result:?}"
    );
}

// ============================================================================
// End-to-end FnOnce resolve decomposition (#758 AC4)
// ============================================================================

/// FnOnce call of FnMut closure with ByMutRef capture exercises resolve.
///
/// Setup: postcondition_once(c, arg, result) as assumption.
/// The fn_mut_once law Skolemizes to produce a witness, and resolve(witness)
/// must decompose structurally via the closure resolve axiom.
///
/// For a single ByMutRef Int capture, resolve delegates to sort-level resolve
/// for Int (trivially true). Asserting NOT(closure_resolve(env)) yields UNSAT,
/// confirming the structural decomposition axiom was emitted.
///
/// Re: #758 AC4.
#[test]
#[timeout(30000)]
fn test_fnonce_resolve_decomposition_e2e() {
    let closure_def_id = "e2e::fnonce_resolve#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "y",
                    crate::ExprSort::Int,
                    CaptureKind::ByMutRef,
                )],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("declare c");
    encoder
        .get_or_declare_var("c2", closure_sort.clone())
        .expect("declare c2");

    let once = method_call(
        var("c"),
        "postcondition_once",
        vec![var("arg"), var("result")],
    );
    let post_mut = method_call(
        var("c"),
        "postcondition_mut",
        vec![var("arg"), var("c2"), var("result")],
    );
    encoder
        .encode_pure(&once)
        .expect("encode postcondition_once");
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");

    // Assert fn_mut_once law (includes resolve axiom emission)
    encoder.assert_fn_mut_once_law();

    // Assume postcondition_once(c, arg, result)
    let once_term = encoder.encode_pure(&once).expect("re-encode once");
    encoder.assert_term(once_term);

    // Verify closure_resolve function was structurally declared
    let sort_name = closure_env_sort_name(&closure_sort).expect("expected ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&resolve_name)
        .expect("resolve function should be declared for closure sort")
        .clone();

    // For ByMutRef-Int, resolve decomposes to resolve_term_for_sort(cap_0, Int)
    // which returns true. So closure_resolve(env) <=> true.
    // Asserting NOT(resolve(env)) should be UNSAT.
    let env = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("declare env");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);

    encoder.solver_mut().push();
    encoder.assert_term(not_resolve);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "resolve(env) for ByMutRef-Int closure should be true (UNSAT when negated)"
    );
    encoder.solver_mut().pop();
}

/// Resolve for multi-capture closure with mixed kinds decomposes correctly.
///
/// Closure with (ByValue Int, ByRef Int, ByMutRef Int):
/// - ByValue: resolve returns true
/// - ByRef: resolve returns true
/// - ByMutRef: resolve delegates to sort-level (Int => true)
///
/// Total: resolve(env) <=> true && true && true <=> true.
/// Asserting NOT(resolve(env)) should be UNSAT.
#[test]
#[timeout(30000)]
fn test_resolve_multi_capture_mixed_kinds() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "e2e::resolve_multi#0".to_string(),
                captures: vec![
                    crate::CaptureField::new("a", crate::ExprSort::Int, CaptureKind::ByValue),
                    crate::CaptureField::new("b", crate::ExprSort::Int, CaptureKind::ByRef),
                    crate::CaptureField::new("c", crate::ExprSort::Int, CaptureKind::ByMutRef),
                ],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f");
    encoder
        .get_or_declare_var("f2", closure_sort.clone())
        .expect("declare f2");

    let once = method_call(
        var("f"),
        "postcondition_once",
        vec![var("arg"), var("result")],
    );
    let post_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("arg"), var("f2"), var("result")],
    );
    encoder.encode_pure(&once).expect("encode once");
    encoder.encode_pure(&post_mut).expect("encode post_mut");
    encoder.assert_fn_mut_once_law();

    let sort_name = closure_env_sort_name(&closure_sort).expect("expected ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&format!("closure_resolve_{suffix}"))
        .expect("multi-capture resolve should exist")
        .clone();

    let env = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("declare env");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);

    encoder.solver_mut().push();
    encoder.assert_term(not_resolve);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "multi-capture (ByValue+ByRef+ByMutRef) resolve should be true"
    );
    encoder.solver_mut().pop();
}
