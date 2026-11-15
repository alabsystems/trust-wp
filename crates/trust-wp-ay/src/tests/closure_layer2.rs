// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure Layer-2 capture projection tests (#1489).
//!
//! These tests verify that after a closure call, capture field projections
//! connect the closure's post-state back to the caller's local variables.
//! Extracted from `verification_closure.rs` for code quality gates.

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::super::*;

const SINGLE_CAPTURE_DEF: &str = "crate::test_fnmut::closure#0";

/// Register a single-capture (Int) closure sort and set up the standard
/// pre-call state: c = mk_closure_env(x_init), postcondition says
/// capture_0(c_post) == capture_0(c) + 1.
///
/// Returns (encoder, closure_sort_suffix) for further assertions.
fn setup_single_capture_postcondition() -> (AYEncoder, String) {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: SINGLE_CAPTURE_DEF.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByValue,
                )],
            },
        )
        .unwrap();

    let c = encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("declare c");
    let c_post = encoder
        .get_or_declare_var("c_post", closure_sort.clone())
        .expect("declare c_post");
    let _x_init = encoder
        .get_or_declare_var("x_init", Sort::Int)
        .expect("declare x_init");

    let mk_c = encoder
        .build_closure_constructor(SINGLE_CAPTURE_DEF, &["x_init"])
        .expect("build constructor");
    let c_eq_mk = encoder.solver_mut().eq(c, mk_c);
    encoder.assert_term(c_eq_mk);

    let suffix = crate::encoder::closure_sorts::closure_symbol_suffix(SINGLE_CAPTURE_DEF);

    // With native datatypes (#2151), use try_datatype_selector instead of UF accessor.
    let selector_name = format!("closure_capture_{suffix}_0");
    let one = encoder.solver_mut().int_const(1);
    let capture_c = encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, c, Sort::Int)
        .expect("selector on c");
    let capture_c_post = encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, c_post, Sort::Int)
        .expect("selector on c_post");
    let capture_c_plus_1 = encoder.solver_mut().add(capture_c, one);
    let post_constraint = encoder.solver_mut().eq(capture_c_post, capture_c_plus_1);
    encoder.assert_term(post_constraint);

    encoder
        .assert_capture_projection(SINGLE_CAPTURE_DEF, "c_post", &[(0, "x_new".to_string())])
        .expect("capture projection should succeed");

    (encoder, suffix)
}

/// Layer-2: capture projection after single FnMut call.
///
/// Simulates the core pattern from `07_mutable_capture`:
/// - Closure captures `&mut x` (one Int field)
/// - `postcondition_mut` says: `capture_0(res_state) == capture_0(self) + 1`
/// - After call, `x_new == capture_0(c_post)` (Layer 2 projection)
/// - Prove: `x_new == x_init + 1`
///
/// Re: #1489 (closure Layer 2).
#[test]
#[timeout(30000)]
fn test_closure_capture_projection_single_call() {
    let (mut encoder, _suffix) = setup_single_capture_postcondition();

    let x_init = encoder
        .get_or_declare_var("x_init", Sort::Int)
        .expect("x_init already declared");
    let x_new = encoder
        .get_or_declare_var("x_new", Sort::Int)
        .expect("x_new should already exist from projection");
    let one = encoder.solver_mut().int_const(1);
    let expected = encoder.solver_mut().add(x_init, one);
    let goal = encoder.solver_mut().eq(x_new, expected);
    let neg_goal = encoder.solver_mut().not(goal);
    encoder.assert_term(neg_goal);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "single-call capture projection should verify x_new == x_init + 1"
    );
}

/// Layer-2: capture projection after two sequential FnMut calls.
///
/// Uses the "projected" postcondition style: the driver rewrites
/// `capture_0(c_post) == capture_0(c) + 1` into `x_new == x_old + 1`
/// by applying capture projections on both sides.
///
/// Re: #1489 (closure Layer 2).
#[test]
#[timeout(30000)]
fn test_closure_capture_projection_two_calls() {
    let mut encoder = AYEncoder::new_pure();

    let x_init = encoder
        .get_or_declare_var("x_init", Sort::Int)
        .expect("declare x_init");
    let one = encoder.solver_mut().int_const(1);

    // Call 1 postcondition (projected form): x_after_1 == x_init + 1
    let x_after_1 = encoder
        .get_or_declare_var("x_after_1", Sort::Int)
        .expect("declare x_after_1");
    let x_init_plus_1 = encoder.solver_mut().add(x_init, one);
    let post1 = encoder.solver_mut().eq(x_after_1, x_init_plus_1);
    encoder.assert_term(post1);

    // Call 2 postcondition (projected form): x_after_2 == x_after_1 + 1
    let x_after_2 = encoder
        .get_or_declare_var("x_after_2", Sort::Int)
        .expect("declare x_after_2");
    let x_after_1_plus_1 = encoder.solver_mut().add(x_after_1, one);
    let post2 = encoder.solver_mut().eq(x_after_2, x_after_1_plus_1);
    encoder.assert_term(post2);

    // Verify: x_after_2 == x_init + 2
    let two = encoder.solver_mut().int_const(2);
    let expected = encoder.solver_mut().add(x_init, two);
    let goal = encoder.solver_mut().eq(x_after_2, expected);
    let neg_goal = encoder.solver_mut().not(goal);
    encoder.assert_term(neg_goal);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "two-call capture projection should verify x_after_2 == x_init + 2"
    );
}

/// Layer-2 negative test: wrong projection value should be SAT (counterexample).
///
/// Same setup as single-call test, but try to prove x_new == x_init + 2
/// (should fail — only one call, so x_new == x_init + 1).
///
/// Re: #1489 (closure Layer 2).
#[test]
#[timeout(30000)]
fn test_closure_capture_projection_negative() {
    let (mut encoder, _suffix) = setup_single_capture_postcondition();

    let x_init = encoder
        .get_or_declare_var("x_init", Sort::Int)
        .expect("x_init already declared");
    let x_new = encoder
        .get_or_declare_var("x_new", Sort::Int)
        .expect("x_new exists");
    let two = encoder.solver_mut().int_const(2);
    let x_init_plus_2 = encoder.solver_mut().add(x_init, two);
    let wrong_goal = encoder.solver_mut().eq(x_new, x_init_plus_2);
    let neg_wrong = encoder.solver_mut().not(wrong_goal);
    encoder.assert_term(neg_wrong);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "single call cannot prove x_new == x_init + 2, expected Sat, got: {result:?}"
    );
}

const MULTI_CAPTURE_DEF: &str = "crate::test_multi::closure#0";

/// Register a two-capture (Int + Bool) closure, set up pre-call state and
/// postconditions: capture_0(c_post) == capture_0(c) + 1, capture_1(c_post) == true.
/// Apply Layer 2 projection for both fields.
fn setup_multi_capture_postcondition() -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: MULTI_CAPTURE_DEF.to_string(),
                captures: vec![
                    crate::CaptureField::new("x", crate::ExprSort::Int, CaptureKind::ByValue),
                    crate::CaptureField::new("flag", crate::ExprSort::Bool, CaptureKind::ByValue),
                ],
            },
        )
        .unwrap();

    let c = encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("c");
    let c_post = encoder
        .get_or_declare_var("c_post", closure_sort.clone())
        .expect("c_post");
    let _x_init = encoder
        .get_or_declare_var("x_init", Sort::Int)
        .expect("x_init");

    let mk_c = encoder
        .build_closure_constructor(MULTI_CAPTURE_DEF, &["x_init", "flag_init"])
        .expect("build constructor");
    let flag_init = encoder
        .get_or_declare_var("flag_init", Sort::Bool)
        .expect("flag_init");
    let flag_false = encoder.solver_mut().bool_const(false);
    let flag_eq = encoder.eq_or_iff(flag_init, flag_false, &Sort::Bool);
    encoder.assert_term(flag_eq);
    let c_eq = encoder.solver_mut().eq(c, mk_c);
    encoder.assert_term(c_eq);

    let suffix = crate::encoder::closure_sorts::closure_symbol_suffix(MULTI_CAPTURE_DEF);
    let sel0 = format!("closure_capture_{suffix}_0");
    let sel1 = format!("closure_capture_{suffix}_1");

    let one = encoder.solver_mut().int_const(1);
    let cap0_c = encoder
        .solver_mut()
        .try_datatype_selector(&sel0, c, Sort::Int)
        .expect("sel0 c");
    let cap0_post = encoder
        .solver_mut()
        .try_datatype_selector(&sel0, c_post, Sort::Int)
        .expect("sel0 post");
    let cap0_inc = encoder.solver_mut().add(cap0_c, one);
    let post0 = encoder.solver_mut().eq(cap0_post, cap0_inc);
    encoder.assert_term(post0);

    let cap1_post = encoder
        .solver_mut()
        .try_datatype_selector(&sel1, c_post, Sort::Bool)
        .expect("sel1 post");
    let true_val = encoder.solver_mut().bool_const(true);
    let post1 = encoder.eq_or_iff(cap1_post, true_val, &Sort::Bool);
    encoder.assert_term(post1);

    encoder
        .assert_capture_projection(
            MULTI_CAPTURE_DEF,
            "c_post",
            &[(0, "x_new".to_string()), (1, "flag_new".to_string())],
        )
        .expect("multi-field capture projection");

    encoder
}

/// Layer-2: multi-field capture projection.
///
/// Closure captures two fields: `x: Int` and `flag: Bool`.
/// Postcondition: capture_0(res) = capture_0(self) + 1, capture_1(res) = true.
/// Project both fields back and verify.
///
/// Re: #1489 (closure Layer 2).
#[test]
#[timeout(30000)]
fn test_closure_capture_projection_multi_field() {
    let mut encoder = setup_multi_capture_postcondition();

    let x_init = encoder
        .get_or_declare_var("x_init", Sort::Int)
        .expect("x_init");
    let x_new = encoder
        .get_or_declare_var("x_new", Sort::Int)
        .expect("x_new");
    let flag_new = encoder
        .get_or_declare_var("flag_new", Sort::Bool)
        .expect("flag_new");

    let one = encoder.solver_mut().int_const(1);
    let x_expected = encoder.solver_mut().add(x_init, one);
    let goal_x = encoder.solver_mut().eq(x_new, x_expected);
    let true_val = encoder.solver_mut().bool_const(true);
    let goal_flag = encoder.eq_or_iff(flag_new, true_val, &Sort::Bool);
    let goal = encoder.solver_mut().and(goal_x, goal_flag);
    let neg_goal = encoder.solver_mut().not(goal);
    encoder.assert_term(neg_goal);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "multi-field capture projection should verify both fields"
    );
}

/// Smoke test: verify_function_with_modes does not crash with closure_captures.
///
/// **WARNING:** This test has a tautological postcondition (`result == call_0`
/// with body `result = call_0`). It does NOT exercise capture projection — the
/// assertion would pass identically with `closure_captures: None`. See #1496.
///
/// For actual capture projection verification, use the encoder-level tests
/// above: `test_closure_capture_projection_single_call` (line 85) and
/// `test_closure_capture_projection_multi_field` (line 272).
///
/// Re: #1489 (closure Layer 2 integration).
#[test]
#[timeout(30000)]
fn test_verify_function_with_closure_captures_smoke() {
    use trust_wp_core::formula::PureExpr;

    let capture_info = crate::closure_capture_info! {
        def_id: "integration_test::closure#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            CaptureKind::ByValue,
        )],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    // Precondition: postcondition_mut(c, (), c_final, call_0)
    // This is the call-site assumption after calling `c()`.
    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(0),                                                // unit arg ()
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))), // c_final
            PureExpr::Var("call_0".to_string(), None), // result of closure call
        ],
    };

    // Body: result = call_0
    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // NOTE: This postcondition is tautological — result == call_0 when body
    // assigns result = call_0. This only tests the pipeline doesn't error.
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(PureExpr::Var("call_0".to_string(), None)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_mut_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "smoke test: pipeline should not error with closure_captures, got: {result:?}"
    );
}

/// Integration test: verify_function_with_modes with capture-dependent postcondition.
///
/// This test uses the full verify_function_with_modes pipeline and asserts a
/// postcondition that DEPENDS on capture projection being correct.
///
/// Setup:
/// - Preconditions: postcondition_mut(c, (), ^c, call_0) AND ^x == x + 1
///   (the second precondition simulates the closure spec's effect on `x`)
/// - Body: result = call_0
/// - Postcondition: ^x == x + 1
/// - closure_captures: ("x", Int) with param_name "c"
///
/// The postcondition's `^x` (x_final) is only populated as a variable if the
/// encoding pipeline correctly processes the Final(Var("x")) expression. The
/// capture projection then asserts capture_0(c_final) == x_final. While the
/// precondition directly asserts ^x == x + 1, this test still validates that
/// the pipeline doesn't fail when closure_captures AND final-variable
/// postconditions coexist — unlike the smoke test above which avoids both.
///
/// Re: #1489 (closure Layer 2 integration), #1496 (trivially-passing tests).
#[test]
#[timeout(30000)]
fn test_verify_function_with_closure_captures_final_var() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let capture_info = crate::closure_capture_info! {
        def_id: "integration_test::closure#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            CaptureKind::ByValue,
        )],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    // Precondition 1: postcondition_mut(c, (), ^c, call_0)
    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(0),
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    // Precondition 2: ^x == x + 1 (closure spec effect on captured variable)
    let x_final_eq_x_plus_1 = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: ^x == x + 1
    // This references x_final, which must be created by the encoding pipeline
    // from the Final(Var("x")) expressions in preconditions/postconditions.
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[postcondition_mut_assumption, x_final_eq_x_plus_1],
            &[ensures],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "^x == x + 1 should verify when precondition provides the same, got: {result:?}"
    );
}

/// Negative integration test: wrong postcondition with closure_captures fails.
///
/// Uses the same closure capture registration path as the positive test, but the
/// postcondition claims ^x == x + 2 (wrong — precondition only provides
/// ^x == x + 1). This verifies the integration pipeline actually checks
/// capture-adjacent final-state postconditions meaningfully without depending on
/// unrelated quantified `postcondition_mut` axioms.
///
/// Re: #1489, #1496.
#[test]
#[timeout(30000)]
fn test_verify_function_with_closure_captures_wrong_postcondition_fails() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    let capture_info = crate::closure_capture_info! {
        def_id: "integration_test::closure#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            CaptureKind::ByValue,
        )],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };

    // Precondition: ^x == x + 1
    let x_final_eq_x_plus_1 = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // WRONG postcondition: ^x == x + 2 (should fail)
    let wrong_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        )),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[x_final_eq_x_plus_1], &[wrong_ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        crate::tests::rejected(&result),
        "^x == x + 2 should fail when precondition only provides ^x == x + 1, got: {result:?}"
    );
}

// ── Phase 2: closure body inlining tests (#2151) ────────────────────
//
// These tests exercise the `try_inline_closure_postcondition` path where
// `body_expr` is `Some(...)`. Previous tests all use `body_expr: None`
// (UF+axiom encoding). With body inlining, the encoder substitutes
// formal parameters and "result" in the closure body expression to
// produce a ground term, eliminating quantifier load.

/// Integration test: closure body inlining via `postcondition` makes the
/// inlined body's constraint available to the solver.
///
/// Models: `let c = |x| x + 1; let r = c(5); assert!(r == 6);`
///
/// The closure `|x| x + 1` has:
/// - `body_expr`: `result == x + 1` (body as return-value equality)
/// - `param_names`: `["x"]`
///
/// The call site invokes `c.postcondition(5, call_0)`, which the inliner
/// substitutes to `call_0 == 5 + 1`. The function body returns `call_0`
/// and the postcondition `result == 6` should be provable.
///
/// Part of #2151 (Phase 2 body inlining).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_postcondition_verifies() {
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
        def_id: "inline_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Precondition: c.postcondition(5, call_0)
    // With body inlining, the encoder substitutes x→5, result→call_0
    // producing: call_0 == 5 + 1, i.e., call_0 == 6.
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    // Body: result = call_0
    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 6
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
        "closure body inlining: call_0 == 6 from |x| x+1 called with 5 \
         should verify (#2151 Phase 2): {result:?}"
    );
}

/// Negative test: wrong postcondition with body inlining must fail.
///
/// Same closure `|x| x + 1` called with 5, but postcondition claims
/// `result == 7` (wrong). Ensures the inlined body actually constrains
/// the solver rather than making the postcondition vacuously true.
///
/// Part of #2151 (Phase 2 body inlining).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_wrong_postcondition_fails() {
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
        def_id: "inline_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // WRONG: result == 7 (should be 6)
    let wrong_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_assumption], &[wrong_ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "result == 7 must fail when closure body gives call_0 == 6 \
         (#2151 Phase 2): {result:?}"
    );
}

/// Integration test: closure with captured variable uses body inlining.
///
/// Models: `let y = 10; let c = |x| x + y; let r = c(3); assert!(r == 13);`
///
/// The closure captures `y` by value. The body expression references both
/// the formal parameter `x` and the captured variable `y`. After inlining,
/// `c.postcondition(3, call_0)` becomes `call_0 == 3 + y`. Combined with
/// the capture constructor constraint (`y` initialized to 10), this proves
/// `result == 13`.
///
/// Part of #2151 (Phase 2 body inlining).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_with_capture_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure body: result == x + y
    // After substitution with x→3, result→call_0: call_0 == 3 + y
    // The capture `y` stays as-is — it resolves to the caller-side variable.
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
        def_id: "inline_capture_test::closure#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "y",
            crate::ExprSort::Int,
            CaptureKind::ByValue,
        )],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Precondition 1: y == 10 (capture initialized to 10)
    let y_eq_10 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    );

    // Precondition 2: c.postcondition(3, call_0)
    // After inlining: call_0 == 3 + y → call_0 == 3 + 10 → call_0 == 13
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(3), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 13
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(13)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[y_eq_10, postcondition_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "closure |x| x + y with y=10, called with 3: result == 13 \
         should verify (#2151 Phase 2): {result:?}"
    );
}

/// Integration test: nullary closure body inlining.
///
/// Models: `let c = || 42; let r = c(); assert!(r == 42);`
///
/// The closure has no parameters and no captures. The body expression is
/// simply `result == 42`. After inlining, `c.postcondition(call_0)` becomes
/// `call_0 == 42`.
///
/// Part of #2151 (Phase 2 body inlining).
#[test]
#[timeout(30000)]
fn test_closure_body_inline_nullary_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure body: result == 42
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "inline_nullary_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec![]),
        ensures_exprs: None,
    };

    // Precondition: c.postcondition(call_0)
    // With no params, args = [call_0]. After inlining: call_0 == 42.
    let postcondition_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 42
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
        matches!(result, crate::VerificationResult::Verified(_)),
        "nullary closure || 42: result == 42 should verify (#2151 Phase 2): {result:?}"
    );
}

/// Build a `()` expression as `__trust_wp_tuple0()`.
fn unit_expr() -> PureExpr {
    PureExpr::LogicFnCall {
        name: trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(0),
        args: vec![],
    }
}

/// Build the ensures clause: `exists<st1, st2, r> f.postcondition_mut((), st1, r)
///   && st1.postcondition_mut((), st2, result) && resolve(st2)`.
fn build_call_fnmut_ensures() -> PureExpr {
    use trust_wp_core::formula::BinOp;

    PureExpr::Exists {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Exists {
            var: "st2".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Exists {
                var: "r".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                            method: "postcondition_mut".to_string(),
                            args: vec![
                                unit_expr(),
                                PureExpr::Var("st1".to_string(), None),
                                PureExpr::Var("r".to_string(), None),
                            ],
                        }),
                        BinOp::And,
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
                            method: "postcondition_mut".to_string(),
                            args: vec![
                                unit_expr(),
                                PureExpr::Var("st2".to_string(), None),
                                PureExpr::Var("result".to_string(), None),
                            ],
                        }),
                    )),
                    BinOp::And,
                    Arc::new(PureExpr::LogicFnCall {
                        name: "resolve".to_string(),
                        args: vec![PureExpr::Var("st2".to_string(), None)],
                    }),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        }),
        triggers: vec![],
    }
}

/// Build the contract expressions for a generic `call_fnmut` function.
/// Returns `(requires, ensures, return_expr)`.
fn build_call_fnmut_contract() -> (Vec<PureExpr>, Vec<PureExpr>, PureExpr) {
    use trust_wp_core::formula::BinOp;

    let req_precondition = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![unit_expr()],
    };

    let req_forall = PureExpr::Forall {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                    method: "postcondition_mut".to_string(),
                    args: vec![
                        unit_expr(),
                        PureExpr::Var("st1".to_string(), None),
                        PureExpr::Var("r".to_string(), None),
                    ],
                }),
                BinOp::Implies,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
                    method: "precondition".to_string(),
                    args: vec![unit_expr()],
                }),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    let deref_f = PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None)));
    let final_f = PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None)));
    let deref_final_f = PureExpr::Deref(Arc::new(final_f.clone()));
    let final_final_f = PureExpr::Final(Arc::new(final_f.clone()));

    let body_postcondition_mut = PureExpr::MethodCall {
        receiver: Arc::new(deref_f.clone()),
        method: "postcondition_mut".to_string(),
        args: vec![
            unit_expr(),
            final_f.clone(),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };
    let body_postcondition_once = PureExpr::MethodCall {
        receiver: Arc::new(deref_f),
        method: "postcondition_once".to_string(),
        args: vec![unit_expr(), PureExpr::Var("call_0".to_string(), None)],
    };
    let second_body_postcondition_mut = PureExpr::MethodCall {
        receiver: Arc::new(deref_final_f),
        method: "postcondition_mut".to_string(),
        args: vec![
            unit_expr(),
            final_final_f.clone(),
            PureExpr::Var("result".to_string(), None),
        ],
    };
    let resolved_second_state = PureExpr::LogicFnCall {
        name: "resolve".to_string(),
        args: vec![final_final_f],
    };

    let return_expr = PureExpr::Var("result".to_string(), None);

    (
        vec![
            req_precondition,
            req_forall,
            body_postcondition_mut,
            body_postcondition_once,
            second_body_postcondition_mut,
            resolved_second_state,
        ],
        vec![build_call_fnmut_ensures()],
        return_expr,
    )
}

/// Generic `DerefMut` postcondition encoding: when `x: &mut T` has a
/// `MutRef(TypeParam(T))` sort annotation, `infer_expr_sort` returns a non-Int
/// `Uninterpreted("__trust_wp_mutref::...")` sort, but the RustHorn borrow model
/// decomposes the reference into an Int-sorted current-state variable. Without
/// bidirectional sort reconciliation in `encode_closure_spec_method`, the UF is
/// declared with a non-Int domain sort but receives an Int-sorted argument,
/// causing "sort mismatch in closure_spec:postcondition".
///
/// Part of #2570. Regression test for generic_deref.rs compat failure.
#[test]
#[timeout(30000)]
fn test_generic_deref_mut_postcondition_mutref_typaram_no_sort_mismatch() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Simulate x: &mut T where T is a generic type parameter
    let t_id = intern_sort_name("T");
    let mutref_typaram = ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)));
    let x = PureExpr::Var("x".to_string(), Some(mutref_typaram));

    // T::deref_mut.postcondition((x,), result) — the pattern from trust-wp-std/std/ops.rs
    let receiver = PureExpr::Var("T_deref_mut".to_string(), None);
    let result_var = PureExpr::Var("result".to_string(), None);
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition".to_string(),
        args: vec![x, result_var],
    };

    // This should not error — the bidirectional reconciliation should prefer
    // the actual Int-sorted term over the inferred MutRef sort.
    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "generic DerefMut postcondition should not produce sort mismatch error: {result:?}\n\
         encode_closure_spec_method must reconcile MutRef(TypeParam) inference \
         against actual Int-sorted borrow-model term (#2570)"
    );

    // The result should be Bool-sorted (postcondition is a predicate)
    let term = result.unwrap();
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "postcondition should produce Bool-sorted term"
    );
}

/// Generic `Clone` postcondition encoding for an immutable `&T` receiver.
///
/// The driver emits `T::clone.postcondition((t,), call_N)` assumptions for
/// generic `t.clone()` calls (#1296). This must stay well-sorted when `t` is
/// annotated as `Ref(TypeParam(T))`.
#[test]
#[timeout(30000)]
fn test_generic_clone_postcondition_ref_typaram_no_sort_mismatch() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let t_id = intern_sort_name("T");
    let ref_typaram = ExprSort::Ref(Box::new(ExprSort::TypeParam(t_id)));
    let t = PureExpr::Var("t".to_string(), Some(ref_typaram));
    let result_var = PureExpr::Var("result".to_string(), None);
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("T::clone".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![t, result_var],
    };

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "generic Clone postcondition should not produce sort mismatch error: {result:?}\n\
         encode_closure_spec_method must reconcile Ref(TypeParam) arguments for \
         driver-emitted `T::clone.postcondition` facts (#1296)"
    );

    let term = result.unwrap();
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "postcondition should produce Bool-sorted term"
    );
}

/// Integration test: generic `call_fnmut` pattern with quantified postcondition_mut
/// and unit-typed args. Reproduces the `call_fnmut` from closures/07_mutable_capture.rs.
///
/// The sort mismatch occurs when the encoding pipeline passes an Int-sorted
/// term at the Unit-sorted args position of the UF.
///
/// Part of #2151 (closure encoding sort mismatch in generic FnMut callers).
///
/// Not credited since D-127: the ensures resolves `st2`, a binder written
/// without a sort, which ranges over closure states that may hold the
/// caller's borrow, and the premise resolves `^^f`, a closure state held
/// through `f`. Both are refused rather than collapsed; what this test still
/// guards is that the refusal, not a sort mismatch, is what stops it.
#[test]
#[timeout(30000)]
fn test_generic_call_fnmut_unit_args_no_panic() {
    let (requires, ensures, return_expr) = build_call_fnmut_contract();

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    );

    match result {
        Err(crate::EncodingError::Unsupported { message, .. }) if message.contains("D-127") => {}
        Err(e) => {
            panic!(
                "call_fnmut encoding should stop only at the D-127 refusal: {e:?}\n\
                 This indicates a sort mismatch in solver.apply() that was not \
                 handled by the sort reconciliation in encode_closure_spec_method"
            );
        }
        other => panic!("call_fnmut's resolve of a closure state must not be credited: {other:?}"),
    }
}
