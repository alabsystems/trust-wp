// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure body inlining integration tests for postcondition_once and
//! postcondition_mut (#2151 Phase 2).
//!
//! These tests exercise `try_inline_closure_postcondition` for FnOnce and FnMut
//! trait closures. The original postcondition (Fn trait) tests live in
//! `closure_layer2.rs`. This file was split out to stay under the 1000-line
//! file size limit.

use std::sync::Arc;

use ntest::timeout;

use crate::{shared_types::CaptureKind, CaptureField, ExprSort};

/// Integration test: `postcondition_once` body inlining works identically to
/// `postcondition` since FnOnce has the same argument layout (consumed, no
/// final state).
///
/// Models: `let c = |x| x + 1; let r = c(5); assert!(r == 6);` (FnOnce call)
///
/// Part of #2151 (Phase 2 body inlining — postcondition_once support).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_once_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure body: result == x + 1
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "inline_once_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Precondition: c.postcondition_once(5, call_0)
    // Same layout as postcondition: [args..., result]. The inliner substitutes
    // x→5, result→call_0, producing call_0 == 6.
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 6
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(6)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_once_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_once body inlining: |x| x+1 called with 5, result == 6 \
         should verify (#2151 Phase 2): {result:?}"
    );
}

/// Negative test: wrong postcondition with `postcondition_once` body inlining must fail.
///
/// Part of #2151 (Phase 2 body inlining — postcondition_once support).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_once_wrong_fails() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "inline_once_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // WRONG: result == 99 (should be 6)
    let wrong_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(99)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_once_assumption], &[wrong_ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "postcondition_once result == 99 should fail when body gives 6 \
         (#2151 Phase 2): {result:?}"
    );
}

/// Integration test: `postcondition_mut` body inlining for a simple FnMut closure.
///
/// Models a pure closure `|x| x + 1` called via FnMut. The body doesn't
/// reference Final-wrapped captures, so the extra final_state argument is
/// unused in the body but must not break the inliner.
///
/// Args layout: postcondition_mut(c, x_arg, ^c, result)
///   = [x_arg, final_state, result]
///
/// Part of #2151 (Phase 2 body inlining — postcondition_mut support).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_mut_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure body: result == x + 1 (pure body, no state mutation)
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "inline_mut_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // postcondition_mut(c, 5, ^c, call_0)
    // Args: [5, Final(c), call_0]
    // param_names = ["x"] → x maps to args[0] = 5
    // args[1] = Final(c) = final_state (skipped by inliner)
    // args[2] = call_0 = result
    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(5),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 6
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(6)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_mut_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_mut body inlining: |x| x+1 called with 5, result == 6 \
         should verify (#2151 Phase 2): {result:?}"
    );
}

/// Negative test: wrong postcondition with `postcondition_mut` body inlining must fail.
///
/// Part of #2151 (Phase 2 body inlining — postcondition_mut support).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_mut_wrong_fails() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "inline_mut_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(5),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // WRONG: result == 99
    let wrong_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(99)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_mut_assumption], &[wrong_ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "postcondition_mut result == 99 should fail when body gives 6 \
         (#2151 Phase 2): {result:?}"
    );
}

/// Integration test: `postcondition_mut` body inlining with captured variable.
///
/// Models: `let y = 10; let c = |x| x + y;` called via FnMut.
/// Proves `result == 13` when called with `3` and `y == 10`.
///
/// The `final_state` (^c) in the args is unused by the body (no mutation),
/// but must not interfere with parameter/result substitution.
///
/// Part of #2151 (Phase 2 body inlining — postcondition_mut with captures).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_mut_with_capture_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure body: result == x + y
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "inline_mut_capture_test::closure#0".to_string(),
        captures: vec![CaptureField::new("y", ExprSort::Int, CaptureKind::ByValue)],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Precondition 1: y == 10
    let y_eq_10 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    );

    // postcondition_mut(c, 3, ^c, call_0)
    // Args: [3, Final(c), call_0]
    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(3),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 13
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(13)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[y_eq_10, postcondition_mut_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_mut |x| x + y with y=10, called with 3: result == 13 \
         should verify (#2151 Phase 2): {result:?}"
    );
}

// ── #2185: Final(Var(capture)) mutation body tests ──────────────────────
//
// These tests exercise `postcondition_mut` body inlining where the closure
// body contains `Final(Var(capture))` — the distinguishing feature of
// `postcondition_mut` vs `postcondition`. Previous integration tests only
// used pure bodies that don't reference Final, making them structurally
// identical to `postcondition` tests.

/// Build a counter closure model for `postcondition_mut` tests (#2185).
///
/// Body: `result == count + x && Final(count) == count + x`
/// Returns `(capture_info, count_eq_0, postcondition_mut_call, return_expr)`.
fn build_counter_mut_closure_model(
    def_id: &str,
) -> (
    crate::ClosureCaptureInfo,
    trust_wp_core::formula::PureExpr,
    trust_wp_core::formula::PureExpr,
    trust_wp_core::formula::PureExpr,
) {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let count_plus_x = PureExpr::BinOp(
        Arc::new(PureExpr::Var("count".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    );
    let result_eq = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(count_plus_x.clone()),
    );
    let final_eq = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "count".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(count_plus_x),
    );
    let closure_body = PureExpr::BinOp(Arc::new(result_eq), BinOp::And, Arc::new(final_eq));

    let capture_info = crate::closure_capture_info! {
        def_id: def_id.to_string(),
        captures: vec![CaptureField::new(
            "count",
            ExprSort::Int,
            CaptureKind::ByMutRef,
        )],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    let count_eq_0 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("count".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );

    // postcondition_mut(c, 5, ^c, call_0)
    let postcondition_mut_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(5),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    (
        capture_info,
        count_eq_0,
        postcondition_mut_call,
        return_expr,
    )
}

/// Integration test: `postcondition_mut` body inlining with `Final(Var(capture))`
/// — exercises the full encoding pipeline for mutation contracts.
///
/// Models counter closure: `|x| { count += x; count }` with body
/// `result == count + x && Final(count) == count + x`.
/// `Final(Var("count"))` resolves to `count_final` via `resolve_nameable_expr`.
/// Verifies `result == 5` when called with `x=5` and `count=0`.
///
/// Part of #2185
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_mut_final_var_capture_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let (capture_info, count_eq_0, postcondition_mut_call, return_expr) =
        build_counter_mut_closure_model("counter_mut_test::closure#0");

    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[count_eq_0, postcondition_mut_call], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_mut with Final(Var(count)) in body: count=0, x=5, \
         result == 5 should verify (#2185): {result:?}"
    );
}

/// Negative test: `postcondition_mut` body with `Final(Var(capture))` must
/// fail when the postcondition contradicts the mutation contract.
///
/// Same counter model, but postcondition claims `result == 10` (wrong).
///
/// Part of #2185
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_mut_final_var_capture_wrong_post_fails() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let (capture_info, count_eq_0, postcondition_mut_call, return_expr) =
        build_counter_mut_closure_model("counter_mut_test::closure#1");

    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[count_eq_0, postcondition_mut_call], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "postcondition_mut with Final(Var(count)) in body: count=0, x=5, \
         result == 10 should fail (#2185): {result:?}"
    );
}
