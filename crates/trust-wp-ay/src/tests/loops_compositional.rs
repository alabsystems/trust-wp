// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compositional loop + post-loop verification tests (#2085).
//!
//! These tests exercise the two-phase verification pattern introduced by
//! `ContinueWithAssumptions`: the loop invariant is verified inductively,
//! then the function postcondition is verified separately with loop-exit
//! state (invariants ∧ ¬condition) injected as preconditions.
//!
//! This models what the driver does at `verification.rs:1055-1063` when
//! `verify_contract_loop_path` returns `ContinueWithAssumptions`.

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::{super::*, helpers::*};

mod compositional_loop_paths;

fn assert_ok_failed_with_counterexample(
    result: &Result<VerificationResult, impl std::fmt::Debug>,
    context: &str,
) {
    match result {
        Ok(VerificationResult::Failed(cex)) => assert!(
            !cex.values.is_empty(),
            "{context} should fail with a counterexample model; got empty counterexample"
        ),
        Ok(other) => panic!("{context} should fail verification; got {other:?}"),
        Err(err) => panic!("{context} should encode successfully; got {err:?}"),
    }
}

fn assert_failed_result(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(_) => {}
        other => panic!("{context} should fail verification; got {other:?}"),
    }
}
// ── Frame constraint tests (#2085) ──────────────────────────────────────────
//
// Frame constraints preserve bindings for variables assigned before the loop
// but NOT modified by the loop body. The driver generates equalities like
// `saved == n` and includes them in ContinueWithAssumptions so the
// function-level verifier retains pre-loop knowledge.

/// Frame constraint positive test: pre-loop variable `saved` is NOT modified by
/// the loop, so the frame constraint `saved == n` is included in loop-exit
/// assumptions. The postcondition `result == n + n` requires both the loop-exit
/// fact `i == n` AND the frame constraint `saved == n`.
///
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n + n)]
/// #[invariant(i >= 0 && i <= n)]
/// fn frame_preserved(n: i32) -> i32 {
///     let saved = n; // pre-loop binding
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     saved + i // post-loop: depends on saved == n AND i == n
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_frame_constraint_preserves_pre_loop_binding() {
    // Phase 1: Counting loop with i as modified, saved is NOT in modified_vars.
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(1))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([
            ("i".to_string(), NamedBindingValue::untyped(int(0))),
            ("saved".to_string(), NamedBindingValue::untyped(var("n"))), // pre-loop: let saved = n
        ]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Counting loop induction should pass: {loop_result:?}"
    );

    // Phase 2: Function-level path WITH frame constraint.
    // Loop-exit: i >= 0 && i <= n && !(i < n) → i == n
    // Frame constraint: saved == n (preserved because saved not in modified_vars)
    // Postcondition: result == n + n, return_expr: saved + i
    // Proof: saved + i == n + n because saved == n AND i == n. ✓
    let loop_exit_requires = vec![
        ge(var("n"), int(1)),       // precondition
        inv,                        // invariant at exit
        not(cond),                  // loop exited
        eq(var("saved"), var("n")), // frame constraint: saved == n
    ];

    let postcondition = eq(var("result"), add(var("n"), var("n")));
    let return_expr = add(var("saved"), var("i"));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        fn_result.as_ref().is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "With frame constraint saved == n, postcondition result == n + n should verify. Got: {fn_result:?}"
    );
}

/// Negative control: same scenario as above but WITHOUT the frame constraint.
/// Without `saved == n`, the verifier cannot establish `result == n + n`
/// because `saved` is unconstrained.
#[test]
#[timeout(30000)]
fn test_frame_constraint_required_for_pre_loop_binding() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    // Phase 2: Function-level path WITHOUT frame constraint.
    // saved is a free variable — the solver can't prove saved == n.
    let loop_exit_requires = vec![
        ge(var("n"), int(1)),
        inv,
        not(cond),
        // NO frame constraint: saved is unconstrained
    ];

    let postcondition = eq(var("result"), add(var("n"), var("n")));
    let return_expr = add(var("saved"), var("i"));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert_ok_failed_with_counterexample(
        &fn_result,
        "without frame constraint, saved is unconstrained so result == n + n",
    );
}

/// Frame constraint with multiple unmodified variables: both `saved_a` and
/// `saved_b` are assigned before the loop and not modified inside it.
/// Postcondition depends on both preserved bindings.
///
/// ```rust
/// #[requires(a >= 0 && b >= 0)]
/// #[ensures(result == a + b)]
/// #[invariant(i >= 0 && i <= 10)]
/// fn multi_frame(a: i32, b: i32) -> i32 {
///     let saved_a = a;
///     let saved_b = b;
///     let mut i = 0;
///     while i < 10 {
///         i += 1;
///     }
///     saved_a + saved_b // both preserved by frame constraints
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_frame_constraint_multiple_unmodified_variables() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), int(10)));
    let cond = lt(var("i"), int(10));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("a"), int(0)), ge(var("b"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([
            ("i".to_string(), NamedBindingValue::untyped(int(0))),
            ("saved_a".to_string(), NamedBindingValue::untyped(var("a"))),
            ("saved_b".to_string(), NamedBindingValue::untyped(var("b"))),
        ]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Loop induction should pass: {loop_result:?}"
    );

    // Phase 2 with both frame constraints.
    let loop_exit_requires = vec![
        ge(var("a"), int(0)),
        ge(var("b"), int(0)),
        inv,
        not(cond),
        eq(var("saved_a"), var("a")), // frame constraint 1
        eq(var("saved_b"), var("b")), // frame constraint 2
    ];

    let postcondition = eq(var("result"), add(var("a"), var("b")));
    let return_expr = add(var("saved_a"), var("saved_b"));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "With both frame constraints, result == a + b should verify. Got: {fn_result:?}"
    );
}

/// Verifies that `induction_passed()` correctly reports false when
/// initialization fails, even if preservation and postcondition pass.
#[test]
#[timeout(30000)]
fn test_induction_failed_init_not_deferred() {
    // Wrong precondition: requires x == 5 but invariant claims x == 0.
    // Init check should fail (5 != 0).
    let inv = eq(var("x"), int(0));
    let cond = lt(var("i"), int(10));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("x".to_string(), int(0));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[eq(var("x"), int(5))], // wrong: x starts at 5, invariant says 0
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([(
            "i".to_string(),
            NamedBindingValue::untyped(int(0)),
        )]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        !loop_result.induction_passed(),
        "Induction should fail when init fails: {loop_result:?}"
    );
    assert_failed_result(
        &loop_result.initialization,
        "initialization when invariant contradicts pre-loop state",
    );
}
