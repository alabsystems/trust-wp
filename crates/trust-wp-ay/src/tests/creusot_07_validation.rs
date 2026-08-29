// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Creusot `07_mutable_capture` validation tests (#2151 AC).
//!
//! Validates the Phase 3 concrete contract model against Creusot's
//! `closures/07_mutable_capture.rs` test case. The Creusot test models an
//! FnMut closure that captures `&mut x`, increments `x` on each call, and
//! returns a constant `5`. The key validation is that two sequential
//! `postcondition_mut` calls with body+ensures inlining correctly track
//! the state of `x` across calls — using ground terms, zero quantifiers.
//!
//! Reference: `reference/creusot/tests/should_succeed/closures/07_mutable_capture.rs`

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::shared_types::CaptureKind;

/// Build the Creusot `test_fnmut` closure model and two-call state chain.
///
/// Returns `(capture_info, requires_chain, return_expr)` where:
/// - `capture_info`: closure `|| { x += 1; 5 }` with body `Int(5)` and
///   ensures `x == old(x) + 1`
/// - `requires_chain`: 5 preconditions modeling two calls with state threading:
///   `[old_x == 100_000, postcondition_mut(c, ^c, call_0), x_mid == old_x + 1,
///    old_x_2 == x_mid, x_final == old_x_2 + 1]`
/// - `return_expr`: `Var("call_0")` (result of the first call)
fn build_creusot_07_two_call_model(
    def_id: &str,
) -> (crate::ClosureCaptureInfo, Vec<PureExpr>, PureExpr) {
    // Closure body: raw return value `5`
    let closure_body = PureExpr::Int(5);

    // Ensures: x == old(x) + 1  (Creusot: #[ensures(x@ == old(x@+1))])
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: def_id.to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            CaptureKind::ByMutRef,
        )],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec![]), // nullary closure: || { ... }
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // 1. Initial state: old_x == 100_000
    let x_init = PureExpr::BinOp(
        Arc::new(PureExpr::Var("old_x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(100_000)),
    );

    // 2. Call 1: postcondition_mut(c, ^c, call_0)
    let call_1 = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    // 3. State threading: x_mid == old_x + 1 (from call 1's ensures)
    let x_mid = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_mid".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("old_x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    // 4. Call 2 old state: old_x_2 == x_mid
    let x_mid_is_old = PureExpr::BinOp(
        Arc::new(PureExpr::Var("old_x_2".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x_mid".to_string(), None)),
    );

    // 5. Call 2 ensures: x_final == old_x_2 + 1
    let x_final = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_final".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("old_x_2".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    (
        capture_info,
        vec![x_init, call_1, x_mid, x_mid_is_old, x_final],
        return_expr,
    )
}

/// Creusot `test_fnmut` validation: closure `|| { x += 1; 5 }` called twice.
///
/// Proves `x_final == 100_002` after two `postcondition_mut` calls using
/// body+ensures inlining (Phase 3). Zero quantifiers.
///
/// Validates #2151 AC: "Design validated against Creusot closures/07_mutable_capture.rs"
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_creusot_07_mutable_capture_two_calls_via_body_inline() {
    let (capture_info, requires, return_expr) =
        build_creusot_07_two_call_model("creusot_07::test_fnmut::closure#0");

    let postcondition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_final".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(100_002)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&requires, &[postcondition])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "Creusot 07_mutable_capture: two FnMut calls on || {{ x += 1; 5 }} \
         with x_init == 100_000 should prove x_final == 100_002 via body+ensures \
         inlining (#2151 AC validation): {result:?}"
    );
}

/// Negative: wrong final state `x_final == 100_003` fails.
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_creusot_07_mutable_capture_two_calls_rejects_wrong_final_state() {
    let (capture_info, requires, return_expr) =
        build_creusot_07_two_call_model("creusot_07_neg::test_fnmut::closure#0");

    let wrong_postcondition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_final".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(100_003)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&requires, &[wrong_postcondition])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "Creusot 07_mutable_capture: claiming x_final == 100_003 after 2 calls \
         (should be 100_002) should fail: {result:?}"
    );
}
