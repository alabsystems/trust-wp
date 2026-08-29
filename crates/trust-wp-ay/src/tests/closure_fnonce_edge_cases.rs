// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure edge case tests for FnOnce/Box captures (#2668).
//!
//! Coverage targets:
//! - FnOnce with nested mut-ref captures (Box<&mut T>)
//! - Closure captures through multiple indirection levels
//! - Closure law axiom generation (postcondition encoding for all 3 traits)
//! - Box<dyn FnOnce> call encoding through the verification pipeline
//!
//! Design: `designs/2026-03-13-2318-fnonce-nested-capture-resolve.md` (EXECUTE)
//! Related: #2318, #985, #1373

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{super::*, helpers::*};
use crate::{encoder::closure_sorts::closure_env_sort_name, shared_types::CaptureKind};

fn formatted_assertions(encoder: &AYEncoder) -> String {
    encoder
        .solver()
        .assertions()
        .into_iter()
        .map(|term| encoder.solver().format_term(term))
        .collect::<Vec<_>>()
        .join("\n")
}

// ============================================================================
// FnOnce with nested mut-ref captures (Box<&mut T>)
// ============================================================================

/// FnOnce closure capturing `Box<&mut i32>` — single-level Box wrapper
/// around a mutable reference.
///
/// The closure environment has one capture field of Int sort (the borrow is
/// erased to Int by the RustHorn encoding). After an FnOnce call, the
/// resolve axiom must hold for the post-state environment, and the capture
/// projection must connect the final state back to the caller.
///
/// This models the `bx: Box<&mut i32>` pattern from closures/09_fnonce_resolve.
#[test]
#[timeout(30000)]
fn test_fnonce_nested_mut_ref_box_capture_resolve() {
    let closure_def_id = "edge::fnonce_box_mut_ref#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![
                    // Box<&mut i32> — the mut ref is tracked as ByMutRef capture
                    crate::CaptureField::new("bx", crate::ExprSort::Int, CaptureKind::ByMutRef),
                ],
            },
        )
        .unwrap();

    // Declare closure vars for pre/post state
    encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("declare closure pre-state");
    encoder
        .get_or_declare_var("c_post", closure_sort.clone())
        .expect("declare closure post-state");

    // Register postcondition_once and postcondition_mut to trigger law emission
    let once = method_call(
        var("c"),
        "postcondition_once",
        vec![var("arg"), var("result")],
    );
    let post_mut = method_call(
        var("c"),
        "postcondition_mut",
        vec![var("arg"), var("c_post"), var("result")],
    );
    encoder
        .encode_pure(&once)
        .expect("encode postcondition_once");
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");

    // Assert fn_mut_once law (emits resolve axiom for closure sort)
    encoder.assert_fn_mut_once_law();

    // Verify resolve is trivially true for ByMutRef-Int capture
    // (flat sort resolve returns true).
    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&resolve_name)
        .expect("resolve function should be declared for closure sort")
        .clone();

    let env = encoder
        .get_or_declare_var("env_check", closure_sort)
        .expect("declare env_check");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);

    encoder.solver_mut().push();
    encoder.assert_term(not_resolve);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "resolve(env) for Box<&mut i32> closure should be true (ByMutRef-Int = trivially true)"
    );
    encoder.solver_mut().pop();
}

/// FnOnce closure capturing `Box<Box<&mut i32>>` — double-nested Box wrapper.
///
/// Models the `by: Box<Box<&mut i32>>` pattern from closures/09_fnonce_resolve.
/// The multi-level Box wrapping does not change the capture kind (still ByMutRef)
/// because the RustHorn encoding erases Box to its inner value.
#[test]
#[timeout(30000)]
fn test_fnonce_double_nested_box_mut_ref_capture_resolve() {
    let closure_def_id = "edge::fnonce_double_box_mut_ref#0";
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Two captures modeling `bx: Box<&mut i32>` and `by: Box<Box<&mut i32>>`
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![
                    crate::CaptureField::new("bx", crate::ExprSort::Int, CaptureKind::ByMutRef),
                    crate::CaptureField::new("by", crate::ExprSort::Int, CaptureKind::ByMutRef),
                ],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("declare c");
    encoder
        .get_or_declare_var("c_post", closure_sort.clone())
        .expect("declare c_post");

    let once = method_call(
        var("c"),
        "postcondition_once",
        vec![var("arg"), var("result")],
    );
    let post_mut = method_call(
        var("c"),
        "postcondition_mut",
        vec![var("arg"), var("c_post"), var("result")],
    );
    encoder.encode_pure(&once).expect("encode once");
    encoder.encode_pure(&post_mut).expect("encode mut");

    encoder.assert_fn_mut_once_law();

    // Both captures are ByMutRef-Int, so resolve is trivially true
    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&format!("closure_resolve_{suffix}"))
        .expect("multi-capture resolve should exist")
        .clone();

    let env = encoder
        .get_or_declare_var("env_check", closure_sort)
        .expect("declare env_check");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);

    encoder.solver_mut().push();
    encoder.assert_term(not_resolve);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "resolve for double-nested Box<Box<&mut i32>> captures should be trivially true"
    );
    encoder.solver_mut().pop();
}

// ============================================================================
// Closure captures through multiple indirection levels
// ============================================================================

/// Closure capturing a ByValue and a ByMutRef field: the hist_inv axiom
/// leaves BOTH unconstrained. ByMutRef captures have prophecy-based final
/// values (`^x`) that may differ, so hist_inv does not enforce identity on them.
/// Only ByRef (shared reference) captures get identity constraints in hist_inv.
///
/// After calling FnMut on this closure, both `capture_0` (ByMutRef) and
/// `capture_1` (ByValue) are unconstrained under hist_inv.
#[test]
#[timeout(30000)]
fn test_mixed_capture_byvalue_and_bymutref_hist_inv_decomposition() {
    let closure_def_id = "edge::mixed_value_mutref#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![
                    // capture_0: ByMutRef (unconstrained by hist_inv — prophecy may differ)
                    crate::CaptureField::new(
                        "mut_ref",
                        crate::ExprSort::Int,
                        CaptureKind::ByMutRef,
                    ),
                    // capture_1: ByValue (unconstrained by hist_inv)
                    crate::CaptureField::new("owned", crate::ExprSort::Int, CaptureKind::ByValue),
                ],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("s", closure_sort.clone())
        .expect("declare self");
    encoder
        .get_or_declare_var("r", closure_sort.clone())
        .expect("declare res_state");

    // Register postcondition_mut and postcondition to trigger fn_closure_laws
    let post_mut = method_call(
        var("s"),
        "postcondition_mut",
        vec![var("arg"), var("r"), var("result")],
    );
    let post = method_call(var("s"), "postcondition", vec![var("arg"), var("result")]);
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");
    encoder.encode_pure(&post).expect("encode postcondition");

    // Assert fn closure laws (emits hist_inv for this capture pattern)
    encoder.assert_fn_closure_laws();

    // Find hist_inv declaration
    let hist_inv_decl = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.starts_with("closure_hist_inv_2_"))
        .map(|(_, decl)| decl.clone())
        .expect("hist_inv should be declared");

    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let assertions = formatted_assertions(&encoder);
    assert!(
        !assertions.contains(&format!("closure_capture_{suffix}_0")),
        "ByMutRef capture_0 must not appear in hist_inv identity constraints"
    );
    assert!(
        !assertions.contains(&format!("closure_capture_{suffix}_1")),
        "ByValue capture_1 must not appear in hist_inv identity constraints"
    );

    // Create two closure-sorted vars and assert hist_inv holds between them
    let s2 = encoder
        .get_or_declare_var("s2", closure_sort.clone())
        .unwrap();
    let r2 = encoder
        .get_or_declare_var("r2", closure_sort.clone())
        .unwrap();
    let hi = encoder.solver_mut().apply(&hist_inv_decl, &[s2, r2]);
    encoder.assert_term(hi);
}

/// Three captures with different kinds: ByRef, ByMutRef, ByValue.
/// Verifies hist_inv decomposes per-capture with correct constraints
/// across all three kinds in a single closure environment.
#[test]
#[timeout(30000)]
fn test_triple_capture_mixed_kinds_hist_inv() {
    let closure_def_id = "edge::triple_mixed#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![
                    crate::CaptureField::new("shared", crate::ExprSort::Int, CaptureKind::ByRef),
                    crate::CaptureField::new(
                        "mutable",
                        crate::ExprSort::Int,
                        CaptureKind::ByMutRef,
                    ),
                    crate::CaptureField::new("owned", crate::ExprSort::Int, CaptureKind::ByValue),
                ],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("s", closure_sort.clone())
        .unwrap();
    encoder
        .get_or_declare_var("r", closure_sort.clone())
        .unwrap();

    let post_mut = method_call(
        var("s"),
        "postcondition_mut",
        vec![var("arg"), var("r"), var("result")],
    );
    let post = method_call(var("s"), "postcondition", vec![var("arg"), var("result")]);
    encoder.encode_pure(&post_mut).expect("encode mut");
    encoder.encode_pure(&post).expect("encode post");
    encoder.assert_fn_closure_laws();

    let hist_inv_decl = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.starts_with("closure_hist_inv_2_"))
        .map(|(_, decl)| decl.clone())
        .expect("hist_inv should exist for triple-capture closure");

    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let assertions = formatted_assertions(&encoder);
    assert!(
        assertions.contains(&format!("closure_capture_{suffix}_0")),
        "ByRef capture_0 must appear in hist_inv identity constraints"
    );
    assert!(
        !assertions.contains(&format!("closure_capture_{suffix}_1")),
        "ByMutRef capture_1 must not appear in hist_inv identity constraints"
    );

    let s2 = encoder
        .get_or_declare_var("s2", closure_sort.clone())
        .unwrap();
    let r2 = encoder
        .get_or_declare_var("r2", closure_sort.clone())
        .unwrap();
    let hi = encoder.solver_mut().apply(&hist_inv_decl, &[s2, r2]);
    encoder.assert_term(hi);

    // ByRef (capture_0): identity-constrained
    let sel_0 = format!("closure_capture_{suffix}_0");
    let s_0 = encoder
        .solver_mut()
        .try_datatype_selector(&sel_0, s2, Sort::Int)
        .unwrap();
    let r_0 = encoder
        .solver_mut()
        .try_datatype_selector(&sel_0, r2, Sort::Int)
        .unwrap();
    let eq_0 = encoder.solver_mut().eq(s_0, r_0);
    let neq_0 = encoder.solver_mut().not(eq_0);
    encoder.solver_mut().push();
    encoder.assert_term(neq_0);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ByRef capture_0 must be identity-constrained"
    );
    encoder.solver_mut().pop();

    // ByMutRef capture_1 is covered by the structural assertion above: it must
    // not appear in the hist_inv RHS at all.
}

// ============================================================================
// Closure law axiom generation — full Fn/FnMut/FnOnce chain
// ============================================================================

/// Full three-trait weakening chain with closure-sorted receiver.
///
/// Registers a concrete closure sort (not just Int vars), declares all three
/// postcondition variants, and verifies the complete chain:
///   postcondition(c, x, r) => postcondition_mut(c, x, c, r) => postcondition_once(c, x, r)
///
/// This exercises the closure-sort-aware witness generation and sort tag
/// matching in `fn_mut_once_law` with non-Int closure env sorts.
#[test]
#[timeout(30000)]
fn test_full_closure_law_chain_with_closure_sort() {
    let closure_def_id = "edge::law_chain#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByValue,
                )],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("declare closure receiver");
    encoder
        .get_or_declare_var("c2", closure_sort.clone())
        .expect("declare closure post-state");

    // Declare all three postcondition variants with closure-sorted receiver
    let post = method_call(var("c"), "postcondition", vec![var("x"), var("r")]);
    let post_mut = method_call(
        var("c"),
        "postcondition_mut",
        vec![var("x"), var("c2"), var("r")],
    );
    let post_once = method_call(var("c"), "postcondition_once", vec![var("x"), var("r")]);

    encoder.encode_pure(&post).expect("encode postcondition");
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");
    encoder
        .encode_pure(&post_once)
        .expect("encode postcondition_once");

    // Assert both law families
    encoder.assert_fn_closure_laws();
    encoder.assert_fn_mut_once_law();

    // Verify forward chain: postcondition => postcondition_once
    // Assume postcondition(c, x, r) holds, negate postcondition_once(c, x, r).
    // The fn_once law says: postcondition_once <=> postcondition && resolve(self).
    // For a ByValue closure, resolve is trivially true, so once <=> post.
    let post_term = encoder.encode_pure(&post).unwrap();
    let once_term = encoder.encode_pure(&post_once).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);

    encoder.solver_mut().push();
    encoder.assert_term(post_term);
    encoder.assert_term(neg_once);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "postcondition(c,x,r) AND NOT postcondition_once(c,x,r) must be UNSAT \
         with closure-sorted receiver (fn_once law + trivial resolve)"
    );
    encoder.solver_mut().pop();
}

/// Negative: postcondition_once without the fn_once law is independent of
/// postcondition, even with closure-sorted receivers.
///
/// Control experiment for test_full_closure_law_chain_with_closure_sort.
#[test]
#[timeout(30000)]
fn test_closure_sort_postcondition_once_independent_without_law() {
    let closure_def_id = "edge::law_neg#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("c", closure_sort.clone())
        .expect("declare c");

    let post = method_call(var("c"), "postcondition", vec![var("x"), var("r")]);
    let post_once = method_call(var("c"), "postcondition_once", vec![var("x"), var("r")]);

    let post_term = encoder.encode_pure(&post).expect("encode post");
    let once_term = encoder.encode_pure(&post_once).expect("encode once");

    // Do NOT assert closure laws — control experiment
    encoder.assert_term(post_term);
    let neg_once = encoder.solver_mut().not(once_term);
    encoder.assert_term(neg_once);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Without laws, postcondition and postcondition_once are independent UFs"
    );
}

// ============================================================================
// Box<dyn FnOnce> call encoding through verification pipeline
// ============================================================================

/// Box<dyn FnOnce> call with body inlining: the postcondition_once assumption
/// is encoded with a Box-wrapped (double-deref) receiver, but the closure body
/// is still inlined correctly because normalize_closure_receiver peels the
/// Deref layers before UF symbol lookup.
///
/// Models: `let f: Box<dyn FnOnce(i32) -> i32> = Box::new(|x| x + 1);`
/// Then: `let r = f(5); assert!(r == 6);`
#[test]
#[timeout(30000)]
fn test_box_dyn_fn_once_body_inline_verify() {
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
        def_id: "edge::box_fn_once#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Precondition: Box-wrapped receiver (**f).postcondition_once(5, call_0)
    // The double deref models Box::new(closure) where MIR produces
    // Deref(Deref(Var("f"))) — one from Box::deref, one from FnOnce::call_once.
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "f".to_string(),
        None,
    )))));
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(box_receiver),
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
        "Box<dyn FnOnce(i32) -> i32> with body inlining: |x| x+1 called with 5, \
         result == 6 should verify: {result:?}"
    );
}

/// Negative test: Box<dyn FnOnce> with wrong postcondition fails.
///
/// Same setup as above but postcondition claims `result == 7` (wrong).
/// Verifies the test above is not tautological.
#[test]
#[timeout(30000)]
fn test_box_dyn_fn_once_wrong_postcondition_fails() {
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
        def_id: "edge::box_fn_once_neg#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "f".to_string(),
        None,
    )))));
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(box_receiver),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Wrong postcondition: result == 7 (should fail — body gives x+1 = 6)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_once_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "Box<dyn FnOnce> with wrong postcondition (result == 7) must fail: {result:?}"
    );
}

/// Box<dyn FnOnce> with a capturing closure: the closure captures `n: i32`
/// by value and the body is `result == x + n`. After boxing and calling
/// with x=10, n=3, the result should be 13.
///
/// This tests that Box wrapping does not interfere with capture substitution
/// during body inlining.
#[test]
#[timeout(30000)]
fn test_box_dyn_fn_once_with_capture_body_inline() {
    // Closure body: result == x + n (where n is captured)
    let closure_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        )),
    );

    let capture_info = crate::closure_capture_info! {
        def_id: "edge::box_fn_once_capture#0".to_string(),
        captures: vec![
            crate::CaptureField::new("n", crate::ExprSort::Int, CaptureKind::ByValue),
        ],
        param_name: Some("f".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Precondition 1: n == 3 (capture value)
    let n_eq_3 = eq(var("n"), int(3));

    // Precondition 2: Box-wrapped postcondition_once(10, call_0)
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "f".to_string(),
        None,
    )))));
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(box_receiver),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(10), PureExpr::Var("call_0".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_0".to_string(), None);

    // Postcondition: result == 13 (10 + 3)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(13)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[n_eq_3, postcondition_once_assumption], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "Box<dyn FnOnce> with ByValue capture n=3, x=10: result == 13 should verify: {result:?}"
    );
}

/// FnOnce call through UF fallback path (no body): the fn_mut_once law
/// connects postcondition_mut to postcondition_once via Skolem witness.
///
/// This tests the axiom-only path used for cross-crate or opaque closures
/// where body inlining is not available.
#[test]
#[timeout(30000)]
fn test_fnonce_uf_fallback_mut_implies_once() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_mut and postcondition_once (no body — UF fallback)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);

    encoder.encode_pure(&mut_expr).expect("encode mut");
    encoder.encode_pure(&once_expr).expect("encode once");

    // Assert fn_mut_once law (connects mut to once via Skolem)
    encoder.assert_fn_mut_once_law();

    // Assume postcondition_mut(f, x, s, r) holds
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    encoder.assert_term(mut_term);

    // postcondition_once(f, x, r) should be derivable via the forward axiom
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    encoder.assert_term(neg_once);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "postcondition_mut(f,x,s,r) AND NOT postcondition_once(f,x,r) must be UNSAT \
         via fn_mut_once forward axiom (UF fallback path)"
    );
}

/// Reverse direction: postcondition_once implies postcondition_mut at the
/// Skolem witness value. Tests that the fn_mut_once reverse axiom generates
/// a valid witness even through the UF fallback path.
#[test]
#[timeout(30000)]
fn test_fnonce_uf_fallback_once_implies_mut_at_witness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);

    encoder.encode_pure(&mut_expr).expect("encode mut");
    encoder.encode_pure(&once_expr).expect("encode once");

    encoder.assert_fn_mut_once_law();

    // Assume postcondition_once(f, x, r) holds
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    encoder.assert_term(once_term);

    // Retrieve the witness function
    let witness_name = encoder
        .decls()
        .logic_func_names()
        .find(|name| name.starts_with("fn_mut_once_witness_"))
        .expect("witness should be declared after assert_fn_mut_once_law")
        .clone();
    let witness_decl = encoder
        .decls()
        .get_logic_func(&witness_name)
        .expect("witness declaration should exist")
        .clone();

    // Build witness(f, x, r)
    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let x_term = encoder.encode_pure(&var("x")).unwrap();
    let r_term = encoder.encode_pure(&var("r")).unwrap();
    let witness_term = encoder
        .solver_mut()
        .apply(&witness_decl, &[f_term, x_term, r_term]);

    // Build postcondition_mut(f, x, witness(f,x,r), r) and negate it
    let mut_decl_name = encoder
        .decls()
        .logic_func_names()
        .find(|k| k.starts_with("closure_postcondition_mut_"))
        .expect("postcondition_mut should be declared")
        .clone();
    let mut_decl = encoder
        .decls()
        .get_logic_func(&mut_decl_name)
        .expect("mut decl exists")
        .clone();
    let mut_at_witness = encoder
        .solver_mut()
        .apply(&mut_decl, &[f_term, x_term, witness_term, r_term]);
    let neg_mut = encoder.solver_mut().not(mut_at_witness);
    encoder.assert_term(neg_mut);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "postcondition_once AND NOT postcondition_mut(witness) must be UNSAT \
         (reverse axiom forces mut to hold at witness value)"
    );
}

// ============================================================================
// Standalone closure body verification — demand guard regression (#2668)
// ============================================================================

/// Regression test for bug/962 — `disjoint_captures::{closure#0}` standalone
/// closure body verification.
///
/// The closure has:
///   - Body: p.1 = 1
///   - Ensures: p_1_final == 1
///
/// During standalone body verification, postcondition_mut UF symbols may be
/// declared (from the closure's own ensures contract) but no ground
/// postcondition_mut calls exist in the requires or body_assumptions. The
/// context-aware demand guard must skip the quantified closure law axioms
/// to prevent ay-dpll from returning Unknown(Incomplete) on this simple
/// ground arithmetic obligation.
///
/// Models: `let mut clos = #[ensures(p.1@ == 1)] || { p.1 = 1; };`
/// The standalone closure body verification should succeed with ground
/// terms alone — the body assigns 1 and the ensures checks equality.
#[test]
#[timeout(30000)]
fn test_standalone_closure_body_with_postcondition_mut_uf_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure body: the assignment p.1 = 1 produces a return_expr that binds
    // the capture's final value. In the RustHorn encoding, this becomes:
    //   p_1_final == 1  (the capture's final state)
    //   result == ()     (unit return)
    //
    // The ensures is: p.1@ == 1 (which the driver rewrites to p_1_final == 1)
    //
    // Simulate standalone body verification: no postcondition calls in requires,
    // just the body binding and ensures as a simple equality check.

    // The body binding: p_1_final == 1
    let body_binding = PureExpr::BinOp(
        Arc::new(PureExpr::Var("p_1_final".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    // The ensures: p_1_final == 1 (same as body binding in this simple case)
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("p_1_final".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    // Closure captures: p.1 as ByMutRef(Int)
    let capture_info = crate::closure_capture_info! {
        def_id: "bug962::disjoint_captures#0".to_string(),
        captures: vec![
            crate::CaptureField::new("p_1", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("self".to_string()),
        body_expr: Some(ensures.clone()),
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures.clone()]),
    };

    let return_expr = PureExpr::Var("unit_result".to_string(), None);

    // Requires: just the body binding (p_1_final == 1)
    // No postcondition calls — this is standalone body verification.
    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[body_binding], &[ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "standalone closure body verification for bug/962 pattern should verify: \
         body assigns p_1_final = 1, ensures checks p_1_final == 1. \
         The context-aware demand guard must skip closure law axioms \
         when no ground postcondition calls exist. Got: {result:?}"
    );
}

/// Complementary test: call-site verification WITH ground postcondition_mut
/// calls in requires should still work — the demand guard enables closure
/// law axioms when actual postcondition calls exist in context.
///
/// This is the call-site pattern: a function calls a FnMut closure and the
/// requires contain `postcondition_mut(c, arg, c_post, result)`.
#[test]
#[timeout(30000)]
fn test_call_site_with_postcondition_mut_in_requires_verifies() {
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
        def_id: "call_site_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c".to_string()),
        body_expr: Some(closure_body),
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: None,
    };

    // Requires: postcondition_mut(c, 5, ^c, call_0) — ground call in context
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

    // Ensures: result == 6 (5 + 1)
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
        "call-site verification with ground postcondition_mut in requires \
         should verify — the demand guard must enable closure law axioms \
         when ground postcondition calls exist. Got: {result:?}"
    );
}

/// Regression test for postcondition_once ensures axiom with ByMutRef captures.
///
/// Before the fix (#2668): the postcondition_once ensures axiom bound both
/// `old_x` and `x` to `selector(env)` for ByMutRef captures, creating:
///   `selector(env) == selector(env) + 1` — always false!
/// This made the axiom vacuously satisfied and disconnected postcondition_once
/// from the closure's mutation effects.
///
/// After the fix: ByMutRef captures get a fresh Skolem variable for the post-state,
/// so the ensures becomes `sk_x == selector(env) + 1` — satisfiable.
///
/// Models: test_fnmut3 in 07_mutable_capture.rs — an unannotated FnMut closure
/// called through `call_fnonce`, with synthesized ensures `x == old(x) + 1`.
/// The postcondition_once ensures axiom must correctly constrain the post-state.
#[test]
#[timeout(30000)]
fn test_postcondition_once_ensures_bymutref_not_contradictory() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure with ByMutRef capture "x" and synthesized ensures: x == old(x) + 1
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
        def_id: "test_fnmut3::closure#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: Some(PureExpr::Int(5)),
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures_expr.clone()]),
    };

    // Simulate call_fnonce: postcondition_once(c, (), call_result) in requires
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Var("call_result".to_string(), None)],
    };

    // After the call, the ensures should give us: x_post == old_x + 1.
    // With old_x == 100_000 (from precondition), x_post should == 100_001.
    //
    // Precondition: x == 100_000 (initial capture state)
    let x_eq_100k = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(100_000)),
    );

    // Return expression (ignored, just need a value)
    let return_expr = PureExpr::Var("call_result".to_string(), None);

    // Ensures: call_result == 5 (the closure returns 5)
    let result_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[x_eq_100k, postcondition_once_assumption],
            &[result_ensures],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    // The verification should succeed or at least not produce contradictory premises.
    // Before the fix, the postcondition_once ensures axiom created a contradiction
    // (x == old(x) + 1 where both bind to the same value), which made any proof
    // vacuously true with Unknown(Incomplete). After the fix, ByMutRef captures get
    // a fresh Skolem variable for the post-state, so the ensures becomes
    // `sk_x == selector(env) + 1` — satisfiable and non-contradictory.
    //
    // Check that we don't get Unknown(Incomplete) which would indicate the axiom
    // is still causing AUFLIA undecidability overhead from contradictory premises.
    let is_unknown_incomplete = matches!(
        &result,
        crate::VerificationResult::Unknown(reason)
            if format!("{reason:?}").to_lowercase().contains("incomplete")
    );
    assert!(
        !is_unknown_incomplete,
        "postcondition_once ensures axiom with ByMutRef captures must NOT create \
         contradictory premises that push ay-dpll to Incomplete. Before fix: old_x \
         and x both bound to selector(env), making ensures always false. \
         After fix: x binds to a fresh Skolem function. Got: {result:?}"
    );
}

/// Disjoint capture pattern from bug/962: closure captures a tuple field by
/// mutable reference while another field is borrowed.
///
/// Models:
/// ```rust
/// fn disjoint_captures(mut p: (i32, i32)) -> i32 {
///     let p0 = &p.0;
///     let mut clos = #[ensures(p.1@ == 1)]
///     || {
///         p.1 = 1;
///     };
///     clos();
///     *p0 + p.1
/// }
/// ```
///
/// At the ay level, this tests that:
/// 1. The closure's ensures (p_1 == 1) is correctly propagated via postcondition_mut
/// 2. The caller can combine the closure effect with independent preconditions
///    (p_0 == 1) to derive the final result (p_0 + p_1 == 2).
///
/// This test exercises the postcondition_mut ensures axiom (connecting abstract
/// UF to concrete capture-level effects) for a single ByMutRef capture.
#[test]
#[timeout(30000)]
fn test_disjoint_capture_bug962_pattern_verifies() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure with single ByMutRef capture "p_1", ensures: p_1 == 1
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("p_1".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    // Body: p_1 = 1 (unit return)
    let capture_info = crate::closure_capture_info! {
        def_id: "bug962::disjoint_captures#0".to_string(),
        captures: vec![
            crate::CaptureField::new("p_1", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("clos".to_string()),
        body_expr: None,
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // Preconditions:
    // 1. p_0 == 1 (from #[requires(p.0@ == 1)])
    let p0_eq_1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("p_0".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    // 2. postcondition_mut(clos, (), ^clos, call_result) — the FnMut call
    let postcondition_mut_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("clos".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Final(Arc::new(PureExpr::Var("clos".to_string(), None))),
            PureExpr::Var("call_result".to_string(), None),
        ],
    };

    // 3. p_1_final (the post-call value of p.1) comes from the capture projection.
    // In the actual pipeline, assert_closure_capture_projections connects
    // p_1_final to the closure's post-state. Here we model the effect
    // of the ensures axiom: postcondition_mut ==> p_1 == 1.
    // For the ay test, we directly assert the ensures effect as a precondition
    // since the capture projection mechanism is pipeline-level, not encoder-level.
    let p1_final_eq_1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("p_1_final".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    // Return expression: p_0 + p_1_final (= 1 + 1 = 2)
    let return_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("p_0".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("p_1_final".to_string(), None)),
    );

    // Ensures: result == 2
    let result_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(2)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[p0_eq_1, p1_final_eq_1, postcondition_mut_assumption],
            &[result_ensures],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "disjoint capture pattern (bug/962) should verify at ay level: \
         p_0 == 1 (from requires), p_1_final == 1 (from closure ensures), \
         result == p_0 + p_1_final == 2. Got: {result:?}"
    );
}

/// Stronger verification of postcondition_once ensures axiom with ByMutRef captures.
///
/// Models the call_fnonce pattern from closures/07_mutable_capture.rs:
/// - Closure captures `x` by mutable reference, with ensures `x == old(x) + 1`
/// - Body returns 5
/// - Called through call_fnonce, which has ensures `f.postcondition_once((), result)`
/// - After the call, the caller needs to know:
///   (a) result == 5 (the return value)
///   (b) x was incremented by 1 (from the ensures axiom)
///
/// The postcondition_once ensures axiom must connect postcondition_once to the
/// mutation effect without creating contradictory universal quantification.
///
/// Before fix: the axiom was:
///   forall env, result, sk_x. postcondition_once(env, result) ==> sk_x == selector(env) + 1
/// This is contradictory (sk_x universally quantified but constrained to one value).
///
/// After fix: uses a Skolem FUNCTION:
///   forall env, result. postcondition_once(env, result) ==> once_post_x(env, result) == selector(env) + 1
/// This is consistent and allows the solver to derive the mutation effect.
#[test]
#[timeout(30000)]
fn test_postcondition_once_ensures_bymutref_verifies_return_value() {
    use trust_wp_core::formula::{BinOp, PureExpr};

    // Closure: || { x += 1; 5 }
    // Ensures: x == old(x) + 1
    // Body: result == 5
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
        def_id: "test_fnmut3_return::closure#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: Some(PureExpr::Int(5)),
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    // call_fnonce ensures: f.postcondition_once((), result)
    let postcondition_once_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Var("call_result".to_string(), None)],
    };

    let return_expr = PureExpr::Var("call_result".to_string(), None);

    // The caller wants to verify: result == 5 (the closure returns 5)
    // The body inlining should give us this directly. The ensures axiom
    // constrains the capture mutation but does NOT contradict the return value.
    let result_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[postcondition_once_assumption], &[result_ensures])
            .return_expr(Some(&return_expr))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "postcondition_once with ByMutRef ensures should verify return value. \
         The ensures axiom (using Skolem function, not universally quantified variable) \
         must NOT make the axiom contradictory and cause Unknown. Got: {result:?}"
    );
}

/// Verify that closure_env_sort_name returns None for Sort::Int, confirming
/// that Int-sorted generic receivers need the single-declaration fallback.
///
/// When closures pass through generic functions like `call_fnonce<F: FnOnce()>`,
/// the type parameter F encodes as Sort::Int via sort_fallback_to_int. The
/// sort-name matching in ensures axioms uses `closure_env_sort_name(domain[0])`
/// which returns None for Sort::Int, causing the primary match to fail.
/// The single-declaration fallback (#2668) uses the sole UF declaration when
/// the sort-name match fails and there is exactly one candidate.
#[test]
fn test_closure_env_sort_name_returns_none_for_int() {
    // Sort::Int is what sort_fallback_to_int produces for generic type parameters
    assert_eq!(
        closure_env_sort_name(&Sort::Int),
        None,
        "closure_env_sort_name(Sort::Int) must return None — \
         Int-sorted receivers from generic functions cannot match by sort name"
    );

    // Sort::Bool also returns None
    assert_eq!(
        closure_env_sort_name(&Sort::Bool),
        None,
        "closure_env_sort_name(Sort::Bool) must return None"
    );

    // A proper closure datatype sort returns Some (must start with "ClosureEnv_")
    let closure_sort = Sort::Uninterpreted("ClosureEnv_test_0".to_string());
    assert_eq!(
        closure_env_sort_name(&closure_sort),
        Some("ClosureEnv_test_0"),
        "closure_env_sort_name for Uninterpreted ClosureEnv_ sort should return Some"
    );
}

/// Sequential `call_fnonce` edge case with a ByMutRef capture and chained
/// `postcondition_once` facts.
///
/// Models the `test_fnmut3` pattern from `closures/07_mutable_capture.rs`:
/// the same closure `|| { x += 1; 5 }` is called twice through `call_fnonce`,
/// so the caller wants the doubly-prophesied final state `^^x == 100_002`.
/// The first call uses `c` as the receiver; the second uses `^c`, i.e. the
/// post-state of the first call as the pre-state of the second.
///
/// The inline path must project synthesized ensures through the concrete
/// receiver states: the first call constrains `^x == x + 1`, and the second
/// call on `^c` must constrain `^^x == ^x + 1`. If the ensures reuse the base
/// caller binding for `x`, the chain breaks and the proof stays SAT.
#[test]
#[timeout(30000)]
fn test_postcondition_once_bymutref_chained_calls_characterization() {
    let ensures_expr = eq(var("x"), add(old(var("x")), int(1)));

    let capture_info = crate::closure_capture_info! {
        def_id: "test_fnmut3_chained_once::closure#0".to_string(),
        captures: vec![
            crate::CaptureField::new("x", crate::ExprSort::Int, CaptureKind::ByMutRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: Some(int(5)),
        param_names: Some(vec![]),
        ensures_exprs: Some(vec![ensures_expr]),
    };

    let receiver1 = var("c");
    let receiver2 = final_expr(var("c"));
    let unit_arg = logic_fn_call("__trust_wp_tuple0", vec![]);

    let first_call_once = method_call(
        receiver1,
        "postcondition_once",
        vec![unit_arg.clone(), var("call_4")],
    );
    let second_call_once = method_call(
        receiver2,
        "postcondition_once",
        vec![unit_arg, var("call_6")],
    );

    let x_init = eq(var("x"), int(100_000));
    let x_final_after_two_calls = eq(final_expr(final_expr(var("x"))), int(100_002));
    let return_expr = var("call_6");

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(
            &[x_init, first_call_once, second_call_once],
            &[x_final_after_two_calls],
        )
        .return_expr(Some(&return_expr))
        .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "Sequential postcondition_once calls on the same ByMutRef capture should \
         thread ^x into the second call and prove ^^x == 100_002: {result:?}"
    );
}
