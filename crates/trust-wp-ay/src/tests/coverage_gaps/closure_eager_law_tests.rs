// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for eager ground instantiation of Fn closure laws (#2514, #2556).
//!
//! Coverage targets in `fn_laws.rs`:
//! - `assert_eager_fn_mut_ground_instantiation` (line 32)
//! - `assert_eager_fn_once_ground_instantiation` (line 86)
//!
//! Coverage targets in `fn_mut_once.rs`:
//! - `assert_eager_fn_mut_once_instantiations_for_exprs` (line 255)
//! - `assert_eager_existential_skolemizations_for_exprs` (line 677)
//! - `synthetic_ground_postcondition_mut_calls_from_once_requires` (line 387)
//! - `synthetic_ground_postcondition_mut_calls_from_once_exprs` (line 395)
//!
//! These functions bypass ay-dpll's single-round E-matching gap by asserting
//! direct ground instances of the fn_mut/fn_once laws for specific postcondition
//! expressions. They are called from the verification obligation pipeline but
//! had zero direct test coverage.

use super::*;

// ── Helper: register all three closure postcondition UFs ────────────────

/// Set up an encoder with postcondition, postcondition_mut, and postcondition_once
/// UF symbols registered (so `closure_postcondition_flags().has_fn` is true).
fn encoder_with_all_postcondition_ufs() -> (
    AYEncoder,
    PureExpr, // postcondition(f, x, r)
    PureExpr, // postcondition_mut(f, x, s, r)
    PureExpr, // postcondition_once(f, x, r)
) {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_expr)
        .expect("postcondition should encode");

    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    (encoder, post_expr, mut_expr, once_expr)
}

// ── assert_eager_fn_mut_ground_instantiation ────────────────────────────

/// Non-MethodCall expressions are a no-op (early return).
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_skips_non_method_call() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&int(42));
    assert!(
        result.is_ok(),
        "non-MethodCall should return Ok(()) silently"
    );
}

/// MethodCall with wrong method name is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_skips_wrong_method_name() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let wrong = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&wrong);
    assert!(
        result.is_ok(),
        "wrong method name should return Ok(()) silently"
    );
}

/// postcondition_mut with fewer than 2 args is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_skips_insufficient_args() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let short = method_call(var("f"), "postcondition_mut", vec![var("x")]);
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&short);
    assert!(result.is_ok(), "< 2 args should return Ok(()) silently");
}

/// When has_fn is false (no plain postcondition registered), no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_skips_without_fn_postcondition() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // Register only postcondition_mut, NOT postcondition
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    let result = encoder.assert_eager_fn_mut_ground_instantiation(&mut_expr);
    assert!(
        result.is_ok(),
        "missing has_fn should return Ok(()) silently"
    );
}

/// Successful ground instantiation: postcondition_mut(f, x, s, r) produces a
/// valid assertion without error.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_ground_instantiation_succeeds() {
    let (mut encoder, _, mut_expr, _) = encoder_with_all_postcondition_ufs();
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&mut_expr);
    assert!(
        result.is_ok(),
        "ground instantiation should succeed: {result:?}"
    );
}

/// Semantic check: eager fn_mut instantiation makes postcondition_mut consistent
/// with postcondition + self==res_state.
///
/// Without the eager instantiation, the negated goal postcondition_mut(f,x,s,r)
/// cannot be linked to postcondition(f,x,r) because the quantified law might
/// not fire (ay-dpll single-round E-matching gap). The eager ground instance
/// directly asserts the biconditional, so the solver can derive the link.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_semantic_links_post_and_mut() {
    let (mut encoder, _, mut_expr, _) = encoder_with_all_postcondition_ufs();

    // Assert the ground instantiation
    encoder
        .assert_eager_fn_mut_ground_instantiation(&mut_expr)
        .expect("ground inst should succeed");

    // Assert postcondition_mut(f, x, s, r) is true
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    encoder.assert_term(mut_term);

    // The fn_mut law says: postcondition_mut(f, x, s, r) <=>
    //   postcondition(f, x, r) && f == s
    // So postcondition(f, x, r) must be true (implied by the biconditional).
    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let not_post = encoder.solver_mut().not(post_term);
    encoder.assert_term(not_post);

    // Should be UNSAT: postcondition_mut true implies postcondition true
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "postcondition_mut(f,x,s,r) AND NOT postcondition(f,x,r) should be UNSAT \
         with eager fn_mut ground instantiation; got {result:?}"
    );
}

/// Deref wrapper on receiver is normalized (inner extraction).
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_normalizes_deref_receiver() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let deref_mut = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&deref_mut);
    assert!(
        result.is_ok(),
        "deref-wrapped receiver should normalize and succeed: {result:?}"
    );
}

// ── assert_eager_fn_once_ground_instantiation ───────────────────────────

/// Non-MethodCall expressions are a no-op (early return).
#[test]
#[timeout(30000)]
fn test_eager_fn_once_skips_non_method_call() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let result = encoder.assert_eager_fn_once_ground_instantiation(&int(42));
    assert!(
        result.is_ok(),
        "non-MethodCall should return Ok(()) silently"
    );
}

/// MethodCall with wrong method name is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_once_skips_wrong_method_name() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let wrong = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let result = encoder.assert_eager_fn_once_ground_instantiation(&wrong);
    assert!(
        result.is_ok(),
        "wrong method name should return Ok(()) silently"
    );
}

/// postcondition_once with zero args is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_once_skips_empty_args() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let empty = method_call(var("f"), "postcondition_once", vec![]);
    let result = encoder.assert_eager_fn_once_ground_instantiation(&empty);
    assert!(result.is_ok(), "empty args should return Ok(()) silently");
}

/// When has_fn is false, no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_once_skips_without_fn_postcondition() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    let result = encoder.assert_eager_fn_once_ground_instantiation(&once_expr);
    assert!(
        result.is_ok(),
        "missing has_fn should return Ok(()) silently"
    );
}

/// Successful ground instantiation.
#[test]
#[timeout(30000)]
fn test_eager_fn_once_ground_instantiation_succeeds() {
    let (mut encoder, _, _, once_expr) = encoder_with_all_postcondition_ufs();
    let result = encoder.assert_eager_fn_once_ground_instantiation(&once_expr);
    assert!(
        result.is_ok(),
        "ground instantiation should succeed: {result:?}"
    );
}

/// Semantic check: eager fn_once instantiation makes postcondition_once consistent
/// with postcondition + resolve(self).
#[test]
#[timeout(30000)]
fn test_eager_fn_once_semantic_links_post_and_once() {
    let (mut encoder, _, _, once_expr) = encoder_with_all_postcondition_ufs();

    // Assert the ground instantiation
    encoder
        .assert_eager_fn_once_ground_instantiation(&once_expr)
        .expect("ground inst should succeed");

    // Assert postcondition_once(f, x, r) is true
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    encoder.assert_term(once_term);

    // The fn_once law says: postcondition_once(f, x, r) <=>
    //   postcondition(f, x, r) && resolve(f)
    // So postcondition(f, x, r) must be true.
    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let not_post = encoder.solver_mut().not(post_term);
    encoder.assert_term(not_post);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "postcondition_once(f,x,r) AND NOT postcondition(f,x,r) should be UNSAT \
         with eager fn_once ground instantiation; got {result:?}"
    );
}

/// Deref wrapper on receiver is normalized.
#[test]
#[timeout(30000)]
fn test_eager_fn_once_normalizes_deref_receiver() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let deref_once = method_call(
        deref(var("f")),
        "postcondition_once",
        vec![var("x"), var("r")],
    );
    let result = encoder.assert_eager_fn_once_ground_instantiation(&deref_once);
    assert!(
        result.is_ok(),
        "deref-wrapped receiver should normalize and succeed: {result:?}"
    );
}

/// Regression test for #2566: the eager `fn_once` helper must skip the axiom
/// when `resolve_term_for_sort(...)` returns `None` (malformed resolve decl),
/// instead of fabricating `resolve(self) = true`.
///
/// Mirrors the quantified-law test
/// `test_fn_closure_laws_skip_malformed_resolve_decl_instead_of_defaulting_true`
/// in `closure_axiom_tests.rs`, but exercises the eager ground instantiation path.
#[test]
#[timeout(30000)]
fn test_eager_fn_once_skips_malformed_resolve_instead_of_defaulting_true() {
    use crate::encoder::{
        closure_sorts::{closure_env_sort_name, StructuredSortContext},
        unsoundness::{self, UnsoundnessCategory},
    };

    unsoundness::reset();

    let closure_def_id = "crate::closure_eager_law_tests::malformed_resolve#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(StructuredSortContext::ClosureStruct {
            def_id: closure_def_id.to_string(),
            captures: vec![],
        })
        .expect("register closure sort");

    // Declare `f` with the closure sort so `resolve_term_for_sort` engages
    // the closure-specific resolve path instead of the trivial `true` fallback.
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare closure receiver");

    // Register postcondition (Fn-trait) and postcondition_once symbols.
    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_expr)
        .expect("encode postcondition");
    encoder
        .encode_pure(&once_expr)
        .expect("encode postcondition_once");

    // Replace the resolve declaration with a malformed one (wrong domain sort).
    // `resolve_term_for_sort` will find this decl but `axiom_apply_tracked` will
    // fail because the closure-sorted term doesn't match `[Sort::Int]`.
    let sort_name = closure_env_sort_name(&closure_sort).expect("closure sort name");
    let suffix = sort_name
        .strip_prefix("ClosureEnv_")
        .expect("closure env prefix");
    let resolve_name = format!("closure_resolve_{suffix}");
    let malformed_decl =
        encoder
            .solver_mut()
            .declare_fun("bad_closure_resolve_decl", &[Sort::Int], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(resolve_name, malformed_decl);

    // Call the eager helper. Before the fix, this would fabricate
    // `resolve(self) = true` and assert postcondition_once = postcondition.
    // After the fix, it returns Ok(()) without asserting anything.
    let before = unsoundness::snapshot();
    let result = encoder.assert_eager_fn_once_ground_instantiation(&once_expr);
    let after = unsoundness::snapshot();
    assert!(result.is_ok(), "eager fn_once should not error: {result:?}");

    // The `resolve_term_for_sort` call inside the eager helper goes through
    // `axiom_apply_tracked`, which records `ClosureAxiomSkipped` on sort mismatch.
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta.contains_key(&UnsoundnessCategory::ClosureAxiomSkipped),
        "malformed resolve should be tracked as ClosureAxiomSkipped: {delta:?}"
    );

    // postcondition(f,x,r) AND NOT postcondition_once(f,x,r) must be SAT:
    // the eager law was skipped, so the two predicates remain independent.
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let premise = encoder.solver_mut().and(post_term, neg_once);
    encoder.assert_term(premise);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "malformed resolve must skip the eager fn_once law — \
         post AND NOT once should remain SAT (independent predicates)"
    );

    unsoundness::reset();
}

// ── assert_eager_fn_mut_once_instantiations_for_exprs (fn_mut_once.rs:255) ──

/// Empty expression list is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiations_empty_exprs() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let exprs: Vec<&PureExpr> = vec![];
    let result = encoder.assert_eager_fn_mut_once_instantiations_for_exprs(&exprs);
    assert!(result.is_ok(), "empty exprs should return Ok(())");
}

/// Expressions that are not postcondition_once calls produce no instantiations.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiations_no_once_calls() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let other = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let exprs: Vec<&PureExpr> = vec![&other];
    let result = encoder.assert_eager_fn_mut_once_instantiations_for_exprs(&exprs);
    assert!(
        result.is_ok(),
        "non-postcondition_once exprs should be a no-op"
    );
}

/// postcondition_once call without matching postcondition_mut entries is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiations_no_mut_match() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // Register only postcondition_once, no postcondition_mut
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    let exprs: Vec<&PureExpr> = vec![&once_expr];
    let result = encoder.assert_eager_fn_mut_once_instantiations_for_exprs(&exprs);
    assert!(
        result.is_ok(),
        "no mut match should be a safe no-op: {result:?}"
    );
}

// ── assert_eager_existential_skolemizations_for_exprs (fn_mut_once.rs:677) ──

/// Empty expression list is a no-op.
#[test]
#[timeout(30000)]
fn test_eager_existential_skolemizations_empty_exprs() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let exprs: Vec<&PureExpr> = vec![];
    let result = encoder.assert_eager_existential_skolemizations_for_exprs(&exprs);
    assert!(result.is_ok(), "empty exprs should return Ok(())");
}

/// Non-Exists expressions are skipped.
#[test]
#[timeout(30000)]
fn test_eager_existential_skolemizations_non_exists() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let plain = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let exprs: Vec<&PureExpr> = vec![&plain];
    let result = encoder.assert_eager_existential_skolemizations_for_exprs(&exprs);
    assert!(result.is_ok(), "non-Exists expr should be skipped");
}

/// Exists without postcondition_mut in body is skipped.
#[test]
#[timeout(30000)]
fn test_eager_existential_skolemizations_exists_without_mut() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let body = gt(var("y"), int(0));
    let expr = exists("y", body);
    let exprs: Vec<&PureExpr> = vec![&expr];
    let result = encoder.assert_eager_existential_skolemizations_for_exprs(&exprs);
    assert!(
        result.is_ok(),
        "exists without postcondition_mut should be skipped"
    );
}

/// Exists with postcondition_mut mentioning the bound variable triggers Skolemization.
#[test]
#[timeout(30000)]
fn test_eager_existential_skolemizations_with_postcondition_mut() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    // exists<s> postcondition_mut(f, x, s, r) — the bound var 's' appears in the call
    let body = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let expr = exists("s", body);
    let exprs: Vec<&PureExpr> = vec![&expr];
    let result = encoder.assert_eager_existential_skolemizations_for_exprs(&exprs);
    assert!(result.is_ok(), "Skolemization should succeed: {result:?}");
}

// ── synthetic_ground_postcondition_mut_calls_from_once_requires (fn_mut_once.rs:387) ──

/// Empty requires produces no synthetic calls.
#[test]
#[timeout(30000)]
fn test_synthetic_ground_mut_calls_empty_requires() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let result = encoder.synthetic_ground_postcondition_mut_calls_from_once_requires(&[]);
    assert!(result.is_empty(), "empty requires should produce no calls");
}

/// Non-postcondition_once requires produce no synthetic calls.
#[test]
#[timeout(30000)]
fn test_synthetic_ground_mut_calls_no_once_requires() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let other = gt(var("x"), int(0));
    let result = encoder.synthetic_ground_postcondition_mut_calls_from_once_requires(&[other]);
    assert!(
        result.is_empty(),
        "non-once requires should produce no calls"
    );
}

// ── synthetic_ground_postcondition_mut_calls_from_once_exprs (fn_mut_once.rs:395) ──

/// Empty expr list produces no synthetic calls.
#[test]
#[timeout(30000)]
fn test_synthetic_ground_mut_calls_empty_exprs() {
    let (mut encoder, _, _, _) = encoder_with_all_postcondition_ufs();
    let exprs: Vec<&PureExpr> = vec![];
    let result = encoder.synthetic_ground_postcondition_mut_calls_from_once_exprs(&exprs);
    assert!(result.is_empty(), "empty exprs should produce no calls");
}

/// postcondition_once expr without matching postcondition_mut produces no calls.
#[test]
#[timeout(30000)]
fn test_synthetic_ground_mut_calls_no_mut_match() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // Only postcondition_once, no postcondition_mut
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    let exprs: Vec<&PureExpr> = vec![&once_expr];
    let result = encoder.synthetic_ground_postcondition_mut_calls_from_once_exprs(&exprs);
    assert!(result.is_empty(), "no mut match should produce no calls");
}
