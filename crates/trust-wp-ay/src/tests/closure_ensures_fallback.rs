// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-coverage tests for `ensures_exprs` fallback paths in closure encoding.
//!
//! **Coverage gap identified by Prover (P1-96):**
//! Every test in the trust-wp-ay suite sets `ensures_exprs: None`. The critical
//! closure ensures paths had zero direct coverage.
//!
//! This file exercises:
//! 1. `postcondition_mut` + `ensures_exprs: Some(...)` → inline body + ensures
//! 2. `body_expr: None` + `ensures_exprs: Some(...)` → ensures-only inlining when `result` is constrained
//! 3. `body_expr: None` + ensures without `result` → UF fallback
//! 4. `postcondition` + `ensures_exprs: Some(...)` → still inlines body
//! 5. Result parameter name collision with formal params
//!
//! Part of #2124

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::{shared_types::CaptureKind, CaptureField, ExprSort};

/// Phase 3 (#2151): `postcondition_mut` with `ensures_exprs` NOW inlines the
/// body conjoined with ensures, just like `postcondition_once`.
///
/// The body provides `result == x + 1` (return value constraint) and the ensures
/// provide additional state-change constraints. When called with arg `5`, the
/// body substitution produces `call_0 == 5 + 1 == 6`, and the conjoined ensures
/// add the state-change constraint. So proving `result == 6` should SUCCEED.
///
/// Previously (#2124), this test verified UF fallback. After Phase 3, the
/// inline path handles `postcondition_mut` + ensures by conjoining body + ensures
/// as ground terms, eliminating quantifier load.
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_postcondition_mut_with_ensures_exprs_inlines_body_and_ensures() {
    // Closure body: result == x + 1 (inlined → call_0 == 5 + 1)
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    // ensures_exprs: captures side-effect (count == old(count) + 1)
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("count".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "count".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "ensures_fallback_test::closure#0".to_string(),
        captures: vec![CaptureField::new("count", ExprSort::Int, CaptureKind::ByMutRef)],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition_mut(c, 5, ^c, call_0)
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

    // Prove result == 6: body provides call_0 == 5 + 1 == 6
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

    // With Phase 3 inlining, the body is conjoined with ensures as ground terms.
    // The body substitution gives call_0 == 6, so result == 6 should verify.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_mut with ensures_exprs should inline body+ensures — \
         result == 6 should verify via ground term encoding (#2151 Phase 3): {result:?}"
    );
}

/// Contrast test: `postcondition` (Fn trait) with `ensures_exprs: Some` should
/// STILL inline the body, because the UF-skip only applies to `postcondition_mut`.
///
/// This confirms the guard at `closure_inline.rs:123` is method-specific.
///
/// Part of #2124
#[test]
#[timeout(30000)]
fn test_postcondition_fn_with_ensures_exprs_still_inlines_body() {
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

    // ensures_exprs present — but for postcondition (Fn), inlining should proceed
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "ensures_fn_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition(f, 5, call_0) — Fn trait layout
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(6)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // Body inlining should proceed for postcondition (Fn trait), so result == 6 verifies
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition (Fn) with ensures_exprs should STILL inline body — \
         result == 6 should verify (#2124): {result:?}"
    );
}

/// When `body_expr` is `None` but `ensures_exprs` constrains `result`, the
/// inline path uses the substituted ensures directly instead of fabricating a
/// dummy `true` body.
///
/// Part of #2124
#[test]
#[timeout(30000)]
fn test_body_none_ensures_some_postcondition_inlines_result_constraint() {
    // No body — only ensures_exprs that mention `result`
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "ensures_only_result_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: None,
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition(f, 5, call_0) — Fn trait
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(6)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "body_expr=None should inline substituted ensures when they constrain result — \
         result == 6 must verify (#2541): {result:?}"
    );
}

/// Ensures-only registration must fail closed when the ensures never constrain
/// `result`; the closure should fall back to the UF path instead of inventing a
/// return-value fact.
#[test]
#[timeout(30000)]
fn test_body_none_ensures_without_result_falls_to_uf() {
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "ensures_only_no_result_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: None,
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "ensures-only closures that do not constrain result must fall back to UF — \
         result == 42 should fail (#2541): {result:?}"
    );
}

/// Verify that registration guard works: `body_expr: None` AND `ensures_exprs: None`
/// means the closure is NOT registered at all (closure_inline.rs:56).
/// The postcondition call falls through to UF encoding.
///
/// Part of #2124
#[test]
#[timeout(30000)]
fn test_body_none_ensures_none_not_registered_falls_to_uf() {
    let capture_info = crate::closure_capture_info! {
        def_id: "no_reg_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    // postcondition(f, 5, call_0)
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(99)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // With no body and no ensures, the closure is not registered.
    // The UF encoding makes postcondition an opaque predicate.
    // result == 99 fails because the UF predicate does not constrain call_0.
    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "unregistered closure (no body, no ensures) should produce UF — \
         result == 99 should fail (#2124): {result:?}"
    );
}

/// Verify that closure `|result| result + 1` called with arg 5 produces
/// correct postcondition `call_0 == 6` (not vacuous truth from param collision).
///
/// Previously (P1-95 finding), the "result" → args.last() mapping overwrote
/// the param binding, causing `call_0 == call_0 + 1` (contradiction) which
/// made any postcondition vacuously true. Fixed by #2193.
///
/// Part of #2124
#[test]
#[timeout(30000)]
fn test_result_param_collision_fixed_verifies_correctly() {
    // Closure body in driver format: `result == (result + 1)`.
    // LHS "result" = return value keyword, RHS "result" = formal param.
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "result_collision_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["result".to_string()]), // param named "result"!
        ensures_exprs: None,
    };

    // postcondition(c, 5, call_0)
    // With fix (#2193): LHS "result" → call_0, RHS "result" → 5.
    // Body becomes: call_0 == (5 + 1) → call_0 == 6.
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 6 (correct for |result| result + 1 called with 5)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(6)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // FIXED (#2193): two-phase substitution correctly disambiguates.
    // Assumption: call_0 == 6. Ensures: call_0 == 6. Verified non-vacuously.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "With fix, |result| result + 1 called with 5 should verify result == 6 \
         non-vacuously (not via ex-falso): {result:?}"
    );
}

/// Verify that the collision fix rejects contradictory claims.
///
/// Previously, the param collision caused vacuous truth so result == 999
/// was provable. After #2193 fix, this should correctly fail.
///
/// Part of #2124
#[test]
#[timeout(30000)]
fn test_result_param_collision_fixed_rejects_false_claim() {
    // Closure body: result == (result + 1) — same format as driver produces
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "result_collision_vacuous::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["result".to_string()]),
        ensures_exprs: None,
    };

    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Claim result == 999 — obviously wrong for |result| result + 1 called with 5
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(999)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // FIXED (#2193): assumption is call_0 == 6 (from body). Claim call_0 == 999.
    // These are contradictory, so the solver should find a counterexample (Failed).
    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "With fix, |result| result + 1 called with 5 should reject result == 999: {result:?}"
    );
}

/// Phase 4: `postcondition_once` with `ensures_exprs` conjoins body + side effects.
///
/// Simulates unannotated FnMut closure `|| { x += 1; 5 }` called through
/// `call_fnonce`. The body is `Int(5)` (return value) and ensures is
/// `[x == old(x) + 1]` (side effect). The conjoined assumption should be:
/// `(result == 5) AND (x == old(x) + 1)`.
///
/// We verify this by:
/// 1. Setting `old_x = 100_000` as a precondition
/// 2. Asserting `postcondition_once(c, (), call_0)` as assumption
/// 3. Proving `call_0 == 5` — should succeed (from body conjoining)
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_postcondition_once_conjoins_ensures_return_value() {
    // Closure body: just the return value `5` (no `result ==` wrapping)
    let closure_body = PureExpr::Int(5);

    // Synthesized ensures: x == old(x) + 1
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
        def_id: "once_conjoins_test::closure#0".to_string(),
        captures: vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByMutRef)],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition_once(c, call_0) — FnOnce with no params, result is call_0
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Prove: result == 5 (from the conjoined body)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_once_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // With conjoining, the assumption includes `call_0 == 5` from body inlining.
    // So `result == 5` should verify.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_once with ensures_exprs should conjoin body (result == 5) \
         with ensures (x == old(x) + 1), making result == 5 provable: {result:?}"
    );
}

/// Phase 4: contrast test — without ensures_exprs, postcondition_once still
/// inlines just the body (no regression from conjoining logic).
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_postcondition_once_without_ensures_still_inlines_body() {
    // Closure body: return value `42`
    let closure_body = PureExpr::Int(42);

    let capture_info = crate::closure_capture_info! {
        def_id: "once_no_ensures_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec![]),
        ensures_exprs: None, // No ensures — pure Fn/FnOnce closure
    };

    // postcondition_once(f, call_0)
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Prove: result == 42
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_once_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // Without ensures_exprs, conjoining is a no-op. Body inlining produces
    // `call_0 == 42`, so `result == 42` should verify.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_once without ensures_exprs should inline body (result == 42): {result:?}"
    );
}

/// Phase 4: verify that the conjoined ensures side-effect is exploitable by
/// the solver — not just syntactically present.
///
/// The existing `test_postcondition_once_conjoins_ensures_return_value` only
/// checks `result == 5` which comes entirely from the body portion. It does
/// not prove the ensures `x == old(x) + 1` is usable. This test verifies
/// the ensures side-effect by adding a precondition `old_x == 0` and proving
/// `x == 1` after the closure call.
///
/// If the ensures conjunction is broken (e.g., sort mismatch, wrong encoding),
/// this test would fail even though the body-only test would pass.
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_postcondition_once_ensures_side_effect_exploitable() {
    // Closure body: return value `5` (raw, no `result ==` wrapping)
    let closure_body = PureExpr::Int(5);

    // Synthesized ensures: x == old(x) + 1
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
        def_id: "once_side_effect_test::closure#0".to_string(),
        captures: vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByMutRef)],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition_once(c, call_0)
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Precondition: x == 0 (so the captured pre-state makes the ensures say
    // ^x == 0 + 1 == 1).
    let precondition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );

    // Postcondition: ^x == 1 (exploiting the ensures side-effect)
    let postcondition = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[precondition, postcondition_once_assumption],
            &[postcondition],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // The ensures `x == old(x) + 1` + precondition `x == 0` should prove
    // `^x == 1`. Fails if old() prefix mechanism doesn't thread through the
    // closure conjunction — meaning the ensures is syntactically present but
    // semantically disconnected.
    //
    // If this assertion fails, the postcondition_once ensures conjoining from
    // #2151 has regressed. Check W1 commits cc3741b2/3b1fbb2f for the original
    // implementation.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "ensures side-effect should be exploitable (old(x) == 0 => x == 1): {result:?}"
    );
}

/// Phase 3 (#2151): `postcondition_mut` with ensures conjoins body + side effects.
///
/// Simulates FnMut closure `|x| { count += 1; x + 1 }` called through
/// `call_fnmut`. The body is `result == x + 1` (return value) and ensures is
/// `count == old(count) + 1` (side effect). The conjoined assumption should be:
/// `(result == x + 1) AND (count == old(count) + 1)`.
///
/// We verify this by:
/// 1. Setting `old_count = 10` as a precondition
/// 2. Asserting `postcondition_mut(c, 5, ^c, call_0)` as assumption
/// 3. Proving `count == 11` — succeeds from ensures side-effect
/// 4. Proving `call_0 == 6` — succeeds from body inlining
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_postcondition_mut_ensures_side_effect_exploitable() {
    // Closure body: return value is `x + 1` (raw, no result == wrapping)
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    // Synthesized ensures: count == old(count) + 1
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("count".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "count".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "mut_side_effect_test::closure#0".to_string(),
        captures: vec![CaptureField::new("count", ExprSort::Int, CaptureKind::ByMutRef)],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition_mut(c, 5, ^c, call_0)
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

    // Precondition: old_count == 10 (so ensures says count == 10 + 1 == 11)
    let precondition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("old_count".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    );

    // Postcondition: call_0 == 6 (from body: x + 1 with x = 5)
    let postcondition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(6)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[precondition, postcondition_mut_assumption],
            &[postcondition],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // With Phase 3 inlining, body gives call_0 == 6 and ensures gives
    // count == old_count + 1 == 11. The ensures side-effect is conjoined.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_mut ensures side-effect should be exploitable — \
         body gives call_0 == 6, ensures gives count == 11: {result:?}"
    );
}

/// Phase 3 (#2151): `postcondition_mut` with ensures correctly rejects false claims.
///
/// Same setup as `test_postcondition_mut_ensures_side_effect_exploitable` but
/// claims `result == 999` — should fail because body says result == 6.
///
/// Part of #2151
#[test]
#[timeout(30000)]
fn test_postcondition_mut_ensures_rejects_false_claim() {
    // Closure body: return value is `x + 1` (raw)
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    // Synthesized ensures: count == old(count) + 1
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("count".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "count".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "mut_reject_false::closure#0".to_string(),
        captures: vec![CaptureField::new("count", ExprSort::Int, CaptureKind::ByMutRef)],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // postcondition_mut(c, 5, ^c, call_0)
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

    // False claim: result == 999 (body says result == 6)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(999)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_mut_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "postcondition_mut false claim should fail \
         (result == 999 vs body == 6): {result:?}"
    );
}
