// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for proof_assert path condition propagation (#1457).
//!
//! When a `proof_assert!` appears inside a branch (if/match), the branch
//! condition should be available as an assumption for verifying the assertion.
//! The driver emits `LetAssume { assumption: branch_cond, body: ... }` in the
//! return expression. For Bool-body LetAssume, `encode_let_assume` produces
//! `assumption => body` (an implication) — when encoded for side effects only
//! (postconditions do not reference `result`), the implication is discarded
//! and the assumption is never asserted as a standalone fact.
//!
//! The fix in `result_binding.rs` explicitly asserts LetAssume assumptions
//! from the return expression after encoding it for side effects.

use ntest::timeout;

use super::{super::*, helpers::*};

// ── Branch condition (if x > 0 { proof_assert!(x > -1) }) ──────────

/// Models:
///   if x > 0 { proof_assert!(x > -1) }
///
/// return_expr: LetAssume { assumption: x > 0, body: true }
/// ensures: [x > -1]  (the assertion to prove)
/// requires: []
///
/// The branch condition `x > 0` implies `x > -1`. Without path condition
/// propagation, `x` is unconstrained and the proof fails.
#[test]
#[timeout(30000)]
fn proof_assert_in_if_branch_uses_branch_condition() {
    let body = let_assume(gt(var("x"), int(0)), bool_expr(true));
    let ensures = gt(var("x"), int(-1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "branch condition x > 0 should prove x > -1 inside the branch: {result:?}"
    );
}

/// Control test: same assertion without the branch condition should fail
/// because `x` is unconstrained.
#[test]
#[timeout(30000)]
fn proof_assert_without_branch_condition_fails() {
    let ensures = gt(var("x"), int(-1));

    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ensures])).unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "unconstrained x should not prove x > -1: {result:?}"
    );
}

// ── Let-binding fact (let x = 5; proof_assert!(x > 0)) ─────────────

/// Models:
///   let x = 5;
///   proof_assert!(x > 0)
///
/// return_expr: LetAssume { assumption: x == 5, body: true }
/// ensures: [x > 0]
/// requires: []
///
/// The let-binding fact `x == 5` should make `x > 0` provable.
#[test]
#[timeout(60000)]
fn proof_assert_after_let_binding_uses_assignment_fact() {
    let body = let_assume(eq(var("x"), int(5)), bool_expr(true));
    let ensures = gt(var("x"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "let-binding x == 5 should prove x > 0: {result:?}"
    );
}

// ── Pattern match (let Some(b) = Some(true); proof_assert!(b)) ──────

/// Models:
///   let Some(b) = Some(true);
///   proof_assert!(b)
///
/// return_expr: LetAssume { assumption: b == true, body: true }
/// ensures: [b == true]
/// requires: []
///
/// This is the simplest reproducer from issue #1457: `bug/273.rs`.
#[test]
#[timeout(30000)]
fn proof_assert_pattern_match_some_true() {
    let body = let_assume(eq(var("b"), bool_expr(true)), bool_expr(true));
    let ensures = eq(var("b"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pattern match b == true should prove proof_assert!(b): {result:?}"
    );
}

// ── Negated branch (else-branch condition) ──────────────────────────

/// Models:
///   if !(x == 0) { proof_assert!(x != 0) }
///
/// return_expr: LetAssume { assumption: !(x == 0), body: true }
/// ensures: [x != 0]
#[test]
#[timeout(30000)]
fn proof_assert_in_else_branch_uses_negated_condition() {
    let body = let_assume(not(eq(var("x"), int(0))), bool_expr(true));
    let ensures = ne(var("x"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "negated branch condition !(x == 0) should prove x != 0: {result:?}"
    );
}

// ── Nested LetAssume (multiple path conditions) ─────────────────────

/// Models:
///   let x = 5;
///   if x > 0 { proof_assert!(x > 4) }
///
/// return_expr: LetAssume { assumption: x == 5,
///                body: LetAssume { assumption: x > 0, body: true } }
/// ensures: [x > 4]
///
/// Both path conditions (x == 5 AND x > 0) should be available.
#[test]
#[timeout(30000)]
fn proof_assert_nested_let_assume_combines_conditions() {
    let body = let_assume(
        eq(var("x"), int(5)),
        let_assume(gt(var("x"), int(0)), bool_expr(true)),
    );
    let ensures = gt(var("x"), int(4));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "nested conditions x == 5 AND x > 0 should prove x > 4: {result:?}"
    );
}

// ── Soundness: contradictory path conditions report vacuous Unknown ─

/// Models:
///   // unreachable: x == 5 AND x == 3
///   proof_assert!(x > 100)
///
/// Contradictory assumptions make the base context UNSAT, so the verifier
/// reports Unknown(vacuous) instead of a proof or counterexample.
#[test]
#[timeout(30000)]
fn proof_assert_contradictory_conditions_vacuous() {
    let body = let_assume(
        eq(var("x"), int(5)),
        let_assume(eq(var("x"), int(3)), bool_expr(true)),
    );
    let ensures = gt(var("x"), int(100));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    match &result {
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous") => {}
        other => panic!("contradictory assumptions should produce Unknown(vacuous): {other:?}"),
    }
}

// ── Function precondition + branch condition combined ───────────────

/// Models:
///   #[requires(y > 0)]
///   fn f(x: i32, y: i32) {
///       if x > 0 { proof_assert!(x + y > 0) }
///   }
///
/// requires: [y > 0]
/// return_expr: LetAssume { assumption: x > 0, body: true }
/// ensures: [x + y > 0]
#[test]
#[timeout(60000)]
fn proof_assert_combines_requires_and_branch_condition() {
    let requires = gt(var("y"), int(0));
    let body = let_assume(gt(var("x"), int(0)), bool_expr(true));
    let ensures = gt(add(var("x"), var("y")), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "requires y > 0 + branch x > 0 should prove x + y > 0: {result:?}"
    );
}

// ── Constructor equality in proof_assert (#2700) ───────────────────

/// Models:
///   let none: Option<i32> = None;
///   let err = none.ok_or(true);
///   proof_assert!(err == Err(true))
///
/// After driver reduction:
///   requires: [call_3 == Err(true)]
///   ensures: [call_3 == Err(true)]
///
/// This is a trivial tautology: the assertion IS the precondition.
/// If the solver fails here, it indicates a sort mismatch in Err constructor
/// encoding between precondition and postcondition contexts.
#[test]
#[timeout(30000)]
fn proof_assert_constructor_equality_err_bool() {
    let err_true = logic_fn_call("Err", vec![bool_expr(true)]);
    let precond = eq(var("call_3"), err_true.clone());
    let assertion = eq(var("call_3"), err_true);

    let result =
        verify_function_with_modes(VerificationRequest::new(&[precond], &[assertion])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "call_3 == Err(true) as both precond and assertion should verify: {result:?}"
    );
}

/// Models:
///   let some: Option<i32> = Some(1);
///   let ok = some.ok_or(false);
///   proof_assert!(ok == Ok(1))
///
/// After driver reduction:
///   requires: [call_7 == Ok(1)]
///   ensures: [call_7 == Ok(1)]
#[test]
#[timeout(30000)]
fn proof_assert_constructor_equality_ok_int() {
    let ok_1 = logic_fn_call("Ok", vec![int(1)]);
    let precond = eq(var("call_7"), ok_1.clone());
    let assertion = eq(var("call_7"), ok_1);

    let result =
        verify_function_with_modes(VerificationRequest::new(&[precond], &[assertion])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "call_7 == Ok(1) as both precond and assertion should verify: {result:?}"
    );
}

/// Models the full option.rs ok_or scenario with ghost context and
/// multiple variables. This mirrors what the driver sends to ay:
///
///   preconditions: [err == call_3, none == None(), some == Some(1),
///                   call_3 == Err(true)]
///   ghost_context: [err == call_3, none == None(), some == Some(1)]
///   assertion: [call_3 == Err(true)]
///
/// The precondition `call_3 == Err(true)` comes from reducing
/// `None().is_none() ==> (call_3 == Err(true))` at the driver level.
#[test]
#[timeout(30000)]
fn proof_assert_option_ok_or_scenario_with_ghost_context() {
    let err_true = logic_fn_call("Err", vec![bool_expr(true)]);
    let none = logic_fn_call("None", vec![]);
    let some_1 = logic_fn_call("Some", vec![int(1)]);

    let preconditions = vec![
        eq(var("err"), var("call_3")),
        eq(var("none"), none.clone()),
        eq(var("some"), some_1.clone()),
        eq(var("call_3"), err_true.clone()),
    ];
    let ghost_context = vec![
        eq(var("err"), var("call_3")),
        eq(var("none"), none),
        eq(var("some"), some_1),
    ];
    let assertion = eq(var("call_3"), err_true);

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &[assertion]).ghost_context(Some(&ghost_context)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ok_or scenario with ghost context should verify: {result:?}"
    );
}

/// Models the full option.rs ok_or scenario with unreduced implications.
/// This tests what the solver actually sees if the constructor method
/// reduction is not aggressive enough:
///
///   preconditions: [err == call_3, none == None(), some == Some(1),
///                   None().is_some() ==> (call_3 == Ok(old(None().unwrap()))),
///                   None().is_none() ==> (call_3 == Err(true))]
///   assertion: [call_3 == Err(true)]
#[test]
#[timeout(30000)]
fn proof_assert_option_ok_or_unreduced_implications() {
    let err_true = logic_fn_call("Err", vec![bool_expr(true)]);
    let none = logic_fn_call("None", vec![]);
    let some_1 = logic_fn_call("Some", vec![int(1)]);
    let ok_unwrap_none = logic_fn_call(
        "Ok",
        vec![old(method_call(
            logic_fn_call("None", vec![]),
            "unwrap",
            vec![],
        ))],
    );

    let preconditions = vec![
        eq(var("err"), var("call_3")),
        eq(var("none"), none),
        eq(var("some"), some_1),
        implies(
            method_call(logic_fn_call("None", vec![]), "is_some", vec![]),
            eq(var("call_3"), ok_unwrap_none),
        ),
        implies(
            method_call(logic_fn_call("None", vec![]), "is_none", vec![]),
            eq(var("call_3"), err_true.clone()),
        ),
    ];
    let assertion = eq(var("call_3"), err_true);

    let result =
        verify_function_with_modes(VerificationRequest::new(&preconditions, &[assertion])).unwrap();
    // This tests whether the solver can handle unreduced implications.
    // If it fails, the driver MUST reduce these before sending to ay.
    eprintln!("unreduced implications result: {result:?}");
}

// ── Old() value tracking in proof_assert (#2700 AC3) ──────────────

/// Models the gap case where a precondition constrains `x` but the
/// assertion references `old(x)` which encodes as `old_x`. Without
/// an explicit `old_x == x` bridge (for immutable variables), the
/// solver sees `old_x` as unconstrained.
///
/// This test demonstrates that old(x) maps to old_x in the ay encoder
/// and that when preconditions are expressed in terms of old-prefixed
/// variables, the assertion can use them.
///
/// The driver is responsible for ensuring that `requires(x > 0)` +
/// `proof_assert!(old(x) > 0)` produces `old_x > 0` as a precondition
/// (for immutable params, old(x) == x). At the ay level, we verify the
/// encoding works when the preconditions already use old-prefixed vars.
#[test]
#[timeout(30000)]
fn proof_assert_old_requires_bridge_for_immutable_params() {
    // Scenario: #[requires(x > 0)] fn f(x: i32) { proof_assert!(old(x) > 0) }
    // The driver should bridge requires(x > 0) → old_x > 0 (since x is immutable)
    // Here we test that old(x) in the assertion correctly uses old_x from preconditions.
    let requires = gt(var("x"), int(0));
    // Assertion: old(x) > 0 → encodes as old_x > 0
    let assertion_expr = gt(old(var("x")), int(0));

    // Ghost context bridges: old_x == x for immutable params
    let ghost_bridge = eq(old(var("x")), var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[assertion_expr])
            .ghost_context(Some(&[ghost_bridge])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "old(x) > 0 with x > 0 and old_x == x bridge should verify: {result:?}"
    );
}

/// Models:
///   #[requires(x > 0)]
///   fn f(x: &mut i32) {
///       *x = *x + 1;
///       proof_assert!(old(*x) > 0)
///   }
///
/// requires: [old_x > 0]
/// return_expr: LetAssume { assumption: x == old_x + 1, body: true }
/// ensures: [old_x > 0]
///
/// The old(x) value is captured before mutation and available as old_x.
/// The assertion `old(*x) > 0` reduces to `old_x > 0` which follows from
/// the precondition.
#[test]
#[timeout(30000)]
fn proof_assert_old_value_from_precondition() {
    let requires = gt(var("old_x"), int(0));
    let body = let_assume(eq(var("x"), add(var("old_x"), int(1))), bool_expr(true));
    let ensures = gt(var("old_x"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "old_x > 0 from precondition should verify: {result:?}"
    );
}

/// Models:
///   fn f(x: i32) {
///       let y = x + 1;
///       proof_assert!(old(x) < y)
///   }
///
/// return_expr: LetAssume { assumption: y == x + 1, body: true }
/// ensures: [x < y]
///
/// The path condition `y == x + 1` implies `x < y`.
/// For pure (non-mutable) variables, old(x) == x.
#[test]
#[timeout(30000)]
fn proof_assert_old_value_equals_current_for_immutable() {
    let body = let_assume(eq(var("y"), add(var("x"), int(1))), bool_expr(true));
    let ensures = lt(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x < y with y == x + 1 should verify: {result:?}"
    );
}

/// Models:
///   #[requires(*x > 0)]
///   fn f(x: &mut i32) {
///       let old_val = old(*x);
///       *x = *x + 1;
///       proof_assert!(*x == old_val + 1)
///   }
///
/// requires: [old_x > 0]
/// return_expr: LetAssume { assumption: x == old_x + 1, body: true }
/// ensures: [x == old_x + 1]
///
/// The mutation tracking uses old_x for the pre-mutation value.
#[test]
#[timeout(30000)]
fn proof_assert_current_equals_old_plus_delta() {
    let requires = gt(var("old_x"), int(0));
    let body = let_assume(eq(var("x"), add(var("old_x"), int(1))), bool_expr(true));
    let ensures = eq(var("x"), add(var("old_x"), int(1)));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x == old_x + 1 with path condition should verify: {result:?}"
    );
}

/// Models:
///   #[requires(v.len() > 0)]
///   fn f(v: &mut Vec<i32>) {
///       let old_len = old(v.len());
///       v.push(42);
///       proof_assert!(v.len() == old_len + 1)
///   }
///
/// This tests the interaction between old() and collection operations.
/// requires: [old_v_len > 0]
/// return_expr: LetAssume { assumption: v_len == old_v_len + 1, body: true }
/// ensures: [v_len == old_v_len + 1]
#[test]
#[timeout(30000)]
fn proof_assert_old_collection_length() {
    let requires = gt(var("old_v_len"), int(0));
    let body = let_assume(
        eq(var("v_len"), add(var("old_v_len"), int(1))),
        bool_expr(true),
    );
    let ensures = eq(var("v_len"), add(var("old_v_len"), int(1)));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "v_len == old_v_len + 1 should verify: {result:?}"
    );
}

/// Models a proof_assert over a mutable local:
///   #[requires(x == 10)]
///   fn f(mut x: i32) { proof_assert!(^x == x + 1) }
///
/// return_expr: LetAssume { assumption: ^x == x + 1, body: true }
/// ensures: [x + 1 == 11]
///
/// The final-state carrier must remain distinct from the current-state carrier
/// for mutable locals. If `^x` collapses back to `x`, the base becomes
/// contradictory (`x == x + 1`) and the proof turns vacuous.
#[test]
#[timeout(30000)]
fn proof_assert_final_value_of_mutable_local_remains_distinct() {
    let requires = eq(var("x"), int(10));
    let body = let_assume(
        eq(final_expr(var("x")), add(var("x"), int(1))),
        bool_expr(true),
    );
    let ensures = eq(add(var("x"), int(1)), int(11));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mutable-local final value should stay distinct from current state: {result:?}"
    );
}

// ── Closure capture scoping in proof_assert (#2700 AC2) ────────────

/// Models a proof_assert inside a closure that captures a local variable.
///
///   let x = 5;
///   let c = || { proof_assert!(x > 0) };
///
/// The closure captures `x` by value. The proof_assert should see x == 5
/// from the let-binding context.
///
/// requires: [x == 5]  (from closure capture)
/// ensures: [x > 0]
#[test]
#[timeout(30000)]
fn proof_assert_closure_capture_by_value() {
    let capture_fact = eq(var("x"), int(5));
    let ensures = gt(var("x"), int(0));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[capture_fact], &[ensures])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "closure capture x == 5 should prove x > 0: {result:?}"
    );
}

/// Models a proof_assert where the closure captures multiple variables
/// and the assertion references multiple captures.
///
///   let a = 1;
///   let b = 2;
///   let c = || { proof_assert!(a + b == 3) };
///
/// requires: [a == 1, b == 2]
/// ensures: [a + b == 3]
#[test]
#[timeout(30000)]
fn proof_assert_closure_multiple_captures() {
    let preconditions = vec![eq(var("a"), int(1)), eq(var("b"), int(2))];
    let ensures = eq(add(var("a"), var("b")), int(3));

    let result =
        verify_function_with_modes(VerificationRequest::new(&preconditions, &[ensures])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "a == 1, b == 2 should prove a + b == 3: {result:?}"
    );
}

/// Models proof_assert with ghost context providing additional facts.
///
///   ghost! {
///       let g = Ghost::new(42);
///       proof_assert!(*g > 0)
///   }
///
/// ghost_context: [g == 42]
/// ensures: [g > 0]
#[test]
#[timeout(30000)]
fn proof_assert_with_ghost_context_facts() {
    let ghost_context = vec![eq(var("g"), int(42))];
    let ensures = gt(var("g"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).ghost_context(Some(&ghost_context)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost context g == 42 should prove g > 0: {result:?}"
    );
}

/// Models proof_assert with combined path conditions, preconditions, and
/// ghost context — the full pipeline a real proof_assert encounters.
///
///   #[requires(n > 0)]
///   fn f(n: i32) {
///       ghost! { let g = Ghost::new(n * 2); }
///       if n > 5 {
///           proof_assert!(*g > 10)
///       }
///   }
///
/// requires: [n > 0]
/// ghost_context: [g == n * 2]
/// return_expr: LetAssume { assumption: n > 5, body: true }
/// ensures: [g > 10]
#[test]
#[timeout(60000)]
fn proof_assert_full_pipeline_with_ghost_and_path_condition() {
    let requires = gt(var("n"), int(0));
    let ghost_context = vec![eq(var("g"), mul(var("n"), int(2)))];
    let body = let_assume(gt(var("n"), int(5)), bool_expr(true));
    let ensures = gt(var("g"), int(10));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures])
            .ghost_context(Some(&ghost_context))
            .return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "requires n > 0, ghost g == n*2, path n > 5 should prove g > 10: {result:?}"
    );
}
