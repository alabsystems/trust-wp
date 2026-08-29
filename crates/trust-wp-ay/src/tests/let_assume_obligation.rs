// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for `LetAssume` and `LetObligation` encoding (#815).
//!
//! These variants scope call-site assumptions and obligations into the
//! PureExpr tree rather than accumulating them in thread-local globals.
//!
//! ## Encoding semantics
//!
//! - `LetAssume { assumption, body }`:
//!   - Bool body: `assumption => body` (implication)
//!   - Non-Bool body: `assert(path => assumption); body`
//!
//! - `LetObligation { obligation, body }`:
//!   - Bool body: `obligation AND body` (conjunction)
//!   - Non-Bool body: `assert(path => obligation); body`
//!
//! ## Test categories
//!
//! 1. **Encoding correctness**: Low-level encode + check_sat tests
//! 2. **Scoped assumptions**: Branch-local postcondition scoping (#815 Problem A)
//! 3. **Obligation enforcement**: Precondition obligation checking (#815 Problem B)
//! 4. **End-to-end verification**: `verify_function` with LetAssume/LetObligation bodies

use std::sync::Arc;

use ntest::timeout;

use super::{super::*, helpers::*};

// ── Encoding correctness: LetAssume (Bool body) ─────────────────────

#[test]
#[timeout(30000)]
fn let_assume_bool_body_encodes_as_implication() {
    // LetAssume { assumption: x > 0, body: x > -1 }
    // Encoded as: (x > 0) => (x > -1)
    //
    // Non-vacuous check: the antecedent x > 0 must be satisfiable (sanity),
    // and forcing the antecedent while negating the consequent must be UNSAT
    // (the implication actually holds, not trivially true).

    // Sanity: x > 0 is satisfiable
    let mut sat_encoder = AYEncoder::new();
    let antecedent = gt(var("x"), int(0));
    let ant_term = sat_encoder.encode_pure(&antecedent).unwrap();
    sat_encoder.assert_term(ant_term);
    let sat_result = sat_encoder.check_sat();
    assert_eq!(
        sat_result,
        SolveResult::Sat,
        "antecedent x > 0 must be satisfiable (sanity check): {sat_result:?}"
    );

    // Non-vacuous: (x > 0 => x > -1) && x > 0 && !(x > -1) must be UNSAT
    let mut encoder = AYEncoder::new();
    let expr = let_assume(gt(var("x"), int(0)), gt(var("x"), int(-1)));
    let term = encoder.encode_pure(&expr).unwrap();
    let ant_term = encoder.encode_pure(&gt(var("x"), int(0))).unwrap();
    let neg_body = encoder.encode_pure(&not(gt(var("x"), int(-1)))).unwrap();
    encoder.assert_term(term);
    encoder.assert_term(ant_term);
    encoder.assert_term(neg_body);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "forcing antecedent and negating body must be UNSAT (non-vacuous implication)"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_bool_body_negation_unsat_when_valid() {
    // LetAssume { assumption: x > 0, body: x > -1 }
    // Negation of (x > 0 => x > -1) should be UNSAT because the implication
    // is universally valid.
    let mut encoder = AYEncoder::new();

    let expr = let_assume(gt(var("x"), int(0)), gt(var("x"), int(-1)));

    let term = encoder.encode_pure(&expr).unwrap();
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of valid implication should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_bool_body_not_vacuously_true() {
    // LetAssume { assumption: x > 0, body: x > 10 }
    // Encoded as: (x > 0) => (x > 10)
    // This is NOT universally valid (e.g., x = 1), so its negation should be SAT.
    let mut encoder = AYEncoder::new();

    let expr = let_assume(gt(var("x"), int(0)), gt(var("x"), int(10)));

    let term = encoder.encode_pure(&expr).unwrap();
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "negation of non-valid implication should be SAT (counterexample exists): {result:?}"
    );
}

// ── Encoding correctness: LetObligation (Bool body) ─────────────────

#[test]
#[timeout(30000)]
fn let_obligation_bool_body_encodes_as_conjunction() {
    // LetObligation { obligation: x > 0, body: x > -1 }
    // Encoded as: (x > 0) AND (x > -1)
    //
    // Non-vacuous: assert the conjunction, then check that negating
    // the obligation makes the formula UNSAT — proving the obligation
    // is actually present in the encoding (not silently dropped).

    // The conjunction should be SAT (x = 5 satisfies both)
    let mut encoder = AYEncoder::new();
    let expr = let_obligation(gt(var("x"), int(0)), gt(var("x"), int(-1)));
    let term = encoder.encode_pure(&expr).unwrap();
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "conjunction with satisfying assignment should be SAT: {result:?}"
    );

    // Negating the obligation makes it UNSAT (obligation is actually conjoined)
    let mut enc2 = AYEncoder::new();
    let expr2 = let_obligation(gt(var("x"), int(0)), gt(var("x"), int(-1)));
    let term2 = enc2.encode_pure(&expr2).unwrap();
    let neg_obl = enc2.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    enc2.assert_term(term2);
    enc2.assert_term(neg_obl);
    assert!(
        matches!(enc2.check_sat(), SolveResult::Unsat(_)),
        "conjunction with negated obligation must be UNSAT (obligation is enforced)"
    );
}

#[test]
#[timeout(30000)]
fn let_obligation_bool_hint_body_actual_int_returns_sort_error() {
    let mut encoder = AYEncoder::new();
    let x_name = "__let_obligation_bool_hint_x";
    let x = encoder
        .solver
        .declare_const(x_name, ay_dpll::api::Sort::Int);
    encoder.vars_mut_for_test().insert(x_name.to_string(), x);
    encoder
        .var_sorts_mut_for_test()
        .insert(x_name.to_string(), ay_dpll::api::Sort::Int);
    encoder.record_sort_hint(x_name.to_string(), ExprSort::Bool);

    let expr = let_obligation(bool_expr(true), var(x_name));
    let err = encoder
        .encode_pure(&expr)
        .expect_err("Bool-inferred LetObligation body must fail closed on Int body terms");
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("sort mismatch in LetObligation Bool body"),
        "error should report LetObligation Bool-body sort mismatch: {err_msg}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "LetObligation Bool-body mismatch should return Err before solver.and panics"
    );
}

#[test]
#[timeout(30000)]
fn let_obligation_bool_body_requires_both_conjuncts() {
    // LetObligation { obligation: x > 10, body: x < 5 }
    // Encoded as: (x > 10) AND (x < 5)
    // Unsatisfiable since no integer is both > 10 and < 5.
    let mut encoder = AYEncoder::new();

    let expr = let_obligation(gt(var("x"), int(10)), lt(var("x"), int(5)));

    let term = encoder.encode_pure(&expr).unwrap();
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "contradictory conjunction should be UNSAT"
    );
}

// ── Encoding correctness: Non-Bool body ─────────────────────────────

#[test]
#[timeout(30000)]
fn let_assume_non_bool_body_asserts_assumption() {
    // LetAssume { assumption: x > 0, body: x + 1 }
    // Non-Bool body: assert(x > 0), return x + 1.
    // Then assert result = 0 should be UNSAT since x > 0 implies x+1 >= 2.
    let mut encoder = AYEncoder::new();

    let expr = let_assume(gt(var("x"), int(0)), add(var("x"), int(1)));

    let term = encoder.encode_pure(&expr).unwrap();
    let zero = encoder.solver_mut().int_const(0);
    let eq_zero = encoder.solver_mut().eq(term, zero);
    encoder.assert_term(eq_zero);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x > 0 asserted, so x + 1 cannot equal 0"
    );
}

#[test]
#[timeout(30000)]
fn let_obligation_non_bool_body_asserts_obligation() {
    // LetObligation { obligation: x > 0, body: x + 1 }
    // Non-Bool body: assert(x > 0), return x + 1.
    //
    // Non-vacuous: SAT check proves a valid assignment exists, then
    // UNSAT complement proves the obligation actually constrains x.

    // Positive: x = 1 satisfies obligation (x > 0) and body x + 1 = 2
    let mut encoder = AYEncoder::new();
    let expr = let_obligation(gt(var("x"), int(0)), add(var("x"), int(1)));
    let term = encoder.encode_pure(&expr).unwrap();
    let two = encoder.solver_mut().int_const(2);
    let eq_two = encoder.solver_mut().eq(term, two);
    encoder.assert_term(eq_two);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "x > 0 allows x = 1, so x + 1 = 2 is SAT: {result:?}"
    );

    // Complement: x + 1 = 0 requires x = -1, which violates obligation x > 0.
    // If obligation were dropped, this would be SAT (x = -1).
    let mut enc2 = AYEncoder::new();
    let expr2 = let_obligation(gt(var("x"), int(0)), add(var("x"), int(1)));
    let term2 = enc2.encode_pure(&expr2).unwrap();
    let zero = enc2.solver_mut().int_const(0);
    let eq_zero = enc2.solver_mut().eq(term2, zero);
    enc2.assert_term(eq_zero);
    assert!(
        matches!(enc2.check_sat(), SolveResult::Unsat(_)),
        "x + 1 = 0 needs x = -1, but obligation x > 0 blocks this (obligation enforced)"
    );
}

#[test]
#[timeout(30000)]
fn let_obligation_non_bool_body_actual_int_obligation_in_branch_returns_sort_error() {
    let mut encoder = AYEncoder::new();
    let x_name = "__let_obligation_non_bool_hint_x";
    let x = encoder
        .solver
        .declare_const(x_name, ay_dpll::api::Sort::Int);
    encoder.vars_mut_for_test().insert(x_name.to_string(), x);
    encoder
        .var_sorts_mut_for_test()
        .insert(x_name.to_string(), ay_dpll::api::Sort::Int);
    encoder.record_sort_hint(x_name.to_string(), ExprSort::Bool);

    let expr = ite(
        gt(var("y"), int(0)),
        let_obligation(var(x_name), add(var("z"), int(1))),
        int(0),
    );
    let err = encoder.encode_pure(&expr).expect_err(
        "non-Bool LetObligation with Int obligation should fail before path-guard implies/assert",
    );
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("sort mismatch in LetObligation non-Bool body"),
        "error should report LetObligation non-Bool-body sort mismatch: {err_msg}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "LetObligation non-Bool-body mismatch should return Err before guard_with_active_path panics"
    );
}

// ── Non-Bool branch scoping (#823 follow-up for #815) ───────────────

#[test]
#[timeout(30000)]
fn non_bool_let_assume_in_branch_is_path_scoped() {
    // LetAssume with non-Bool body (Int) inside an ITE branch.
    //
    // Body: ITE(y > 0,
    //           LetAssume { x > 0, x + 1 },  // non-Bool body
    //           int(0))
    // Ensures: x > 0
    //
    // x > 0 is branch-local and must not leak globally.
    let body = ite(
        gt(var("y"), int(0)),
        let_assume(gt(var("x"), int(0)), add(var("x"), int(1))),
        int(0),
    );
    let ensures = gt(var("x"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "non-Bool LetAssume assumption must remain branch-scoped: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn non_bool_let_obligation_in_branch_is_path_scoped() {
    // LetObligation with non-Bool body inside an ITE branch.
    // Force the else-branch (`y <= 0`) and `x <= 0`.
    //
    // If obligation `x > 0` leaked globally, this would be UNSAT.
    // With path scoping, it is SAT because the branch carrying the obligation
    // is not taken.
    let mut encoder = AYEncoder::new();
    let expr = ite(
        gt(var("y"), int(0)),
        let_obligation(gt(var("x"), int(0)), add(var("x"), int(1))),
        int(0),
    );

    let term = encoder.encode_pure(&expr).unwrap();
    let y_non_positive = encoder.encode_pure(&not(gt(var("y"), int(0)))).unwrap();
    let x_non_positive = encoder.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    let zero = encoder.solver_mut().int_const(0);
    let eq_zero = encoder.solver_mut().eq(term, zero);
    encoder.assert_term(y_non_positive);
    encoder.assert_term(x_non_positive);
    encoder.assert_term(eq_zero);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "non-Bool LetObligation must not leak out of untaken branch: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn non_bool_let_obligation_enforced_when_branch_taken() {
    // Same shape as above, but force the branch that carries the obligation.
    // Then `x <= 0` should contradict the obligation `x > 0`.
    let mut encoder = AYEncoder::new();
    let expr = ite(
        gt(var("y"), int(0)),
        let_obligation(gt(var("x"), int(0)), add(var("x"), int(1))),
        int(0),
    );

    let _term = encoder.encode_pure(&expr).unwrap();
    let y_positive = encoder.encode_pure(&gt(var("y"), int(0))).unwrap();
    let x_non_positive = encoder.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    encoder.assert_term(y_positive);
    encoder.assert_term(x_non_positive);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "non-Bool LetObligation must be enforced when its branch is taken"
    );
}

// ── Edge cases: vacuous / contradictory ──────────────────────────────

#[test]
#[timeout(30000)]
fn let_assume_false_assumption_is_vacuously_true() {
    // LetAssume { assumption: false, body: false }
    // Encoded as: false => false, which is true (vacuous truth).
    // This documents that an unreachable call-site (where postcondition
    // is false) makes the entire continuation vacuously verified.
    {
        let mut encoder = AYEncoder::new();

        let expr = let_assume(bool_expr(false), bool_expr(false));

        let term = encoder.encode_pure(&expr).unwrap();
        encoder.assert_term(term);
        let result = encoder.check_sat();
        assert_eq!(
            result,
            SolveResult::Sat,
            "false => false is vacuously true: {result:?}"
        );
    }

    // Non-vacuous control: implication with symbolic antecedent and false body.
    // `x > 0 => false` is equivalent to `!(x > 0)`.
    {
        let mut control_sat = AYEncoder::new();
        let control_expr = let_assume(gt(var("x"), int(0)), bool_expr(false));
        let control_term = control_sat.encode_pure(&control_expr).unwrap();
        let x_non_positive = control_sat.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
        control_sat.assert_term(control_term);
        control_sat.assert_term(x_non_positive);
        let result = control_sat.check_sat();
        assert_eq!(
            result,
            SolveResult::Sat,
            "x <= 0 should satisfy (x > 0 => false): {result:?}"
        );
    }

    {
        let mut control_unsat = AYEncoder::new();
        let control_expr = let_assume(gt(var("x"), int(0)), bool_expr(false));
        let control_term = control_unsat.encode_pure(&control_expr).unwrap();
        let x_positive = control_unsat.encode_pure(&gt(var("x"), int(0))).unwrap();
        control_unsat.assert_term(control_term);
        control_unsat.assert_term(x_positive);
        assert!(
            matches!(control_unsat.check_sat(), SolveResult::Unsat(_)),
            "x > 0 should contradict (x > 0 => false)"
        );
    }
}

#[test]
#[timeout(30000)]
fn let_obligation_false_obligation_returns_encoding_error() {
    // LetObligation { obligation: false, body: true }
    // A constant-false obligation comes from opaque call `requires(false)`.
    // In the non-Bool body path, the old behavior asserted `false` as a solver
    // fact, making the context trivially UNSAT → false "Verified" (UNSOUND).
    // In the Bool body path, `and(false, body)` was accidentally correct but
    // the outcome depended on body sort — inconsistent and fragile.
    //
    // Now: encode_let_obligation detects constant-false obligations and returns
    // an encoding error, preventing any false proofs regardless of body sort.
    // The caller (verification pipeline) treats this as a verification failure. (#2663)
    {
        let mut encoder = AYEncoder::new();

        let expr = let_obligation(bool_expr(false), bool_expr(true));

        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_err(),
            "LetObligation with Bool(false) should return encoding error, got {result:?}"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("requires(false)") || err_msg.contains("opaque"),
            "error message should mention opaque/requires(false): {err_msg}"
        );
    }

    // Non-Bool body variant: same result.
    {
        let mut encoder2 = AYEncoder::new();
        let expr2 = let_obligation(bool_expr(false), int(42));
        let result2 = encoder2.encode_pure(&expr2);
        assert!(
            result2.is_err(),
            "LetObligation with Bool(false) and non-Bool body should also error: {result2:?}"
        );
    }

    // Non-vacuous control: conjunction with symbolic obligation and true body.
    // `x > 0 AND true` is equivalent to `x > 0`.
    {
        let mut control_sat = AYEncoder::new();
        let control_expr = let_obligation(gt(var("x"), int(0)), bool_expr(true));
        let control_term = control_sat.encode_pure(&control_expr).unwrap();
        let x_positive = control_sat.encode_pure(&gt(var("x"), int(0))).unwrap();
        control_sat.assert_term(control_term);
        control_sat.assert_term(x_positive);
        let result = control_sat.check_sat();
        assert_eq!(
            result,
            SolveResult::Sat,
            "x > 0 should satisfy (x > 0 AND true): {result:?}"
        );
    }

    {
        let mut control_unsat = AYEncoder::new();
        let control_expr = let_obligation(gt(var("x"), int(0)), bool_expr(true));
        let control_term = control_unsat.encode_pure(&control_expr).unwrap();
        let x_non_positive = control_unsat
            .encode_pure(&not(gt(var("x"), int(0))))
            .unwrap();
        control_unsat.assert_term(control_term);
        control_unsat.assert_term(x_non_positive);
        assert!(
            matches!(control_unsat.check_sat(), SolveResult::Unsat(_)),
            "x <= 0 should contradict (x > 0 AND true)"
        );
    }
}

// ── Branch-scoped assumption: #815 Problem A ────────────────────────
//
// Scenario: A function calls `id_pos(x)` inside an `if` branch.
// The postcondition `result > 0` from `id_pos` should only be available
// within the branch, not after it.
//
// Without scoping (bug #815): postcondition leaks globally.
// With LetAssume: postcondition is scoped to the branch via implication.

#[test]
#[timeout(30000)]
fn branch_scoped_assumption_does_not_leak_globally() {
    // The assumption `x > 0` appears inside a branch via LetAssume.
    // It must NOT leak to prove `ensures: x > 0` outside the branch.
    //
    // Body: ITE(y > 0,
    //           LetAssume { assumption: x > 0, body: true },
    //           true)
    // Ensures: x > 0
    //
    // LetAssume encoding: (x > 0) => true  =  true
    // So body = ITE(y > 0, true, true) = true, result = true.
    // VC: result = true AND NOT(x > 0) — SAT (x = -1), so FAILS.
    //
    // If assumption leaked globally (old bug #815): ASSERT(x > 0) would
    // make NOT(x > 0) contradictory → UNSAT → incorrectly Verified.
    let body = ite(
        gt(var("y"), int(0)),
        let_assume(gt(var("x"), int(0)), bool_expr(true)),
        bool_expr(true),
    );
    let ensures = gt(var("x"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "branch-scoped assumption must not leak to prove ensures: {result:?}"
    );
}

/// Control test: same setup as above, but with the assumption as a global
/// precondition instead of LetAssume. This MUST verify, proving that the
/// only difference between this and the test above is the scoping.
#[test]
#[timeout(30000)]
fn branch_scoped_assumption_control_global_precondition_verifies() {
    // Same body structure, but x > 0 is a precondition (global), not LetAssume.
    let body = ite(gt(var("y"), int(0)), bool_expr(true), bool_expr(true));
    let requires = gt(var("x"), int(0));
    let ensures = gt(var("x"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "global precondition should prove ensures: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn branch_scoped_assumption_available_within_scope() {
    // Simulates checking the assumption IS available within its scope:
    //   body = LetAssume { assumption: x > 0, body: x > -1 }
    // Ensures: result == true
    //
    // Since x > 0 => x > -1 is valid, LetAssume evaluates to true.
    let body = let_assume(gt(var("x"), int(0)), gt(var("x"), int(-1)));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "assumption should be usable within scope (not Failed/Error after #2202): {result:?}"
    );
}

// ── Obligation enforcement: #815 Problem B ──────────────────────────
//
// Scenario: A function calls `id_pos(x)` which requires `x > 0`.
// The caller must PROVE this precondition; it cannot be assumed for free.
//
// Without obligations (bug #815): precondition silently assumed.
// With LetObligation: precondition becomes a proof obligation via conjunction.

#[test]
#[timeout(30000)]
fn unsatisfied_obligation_causes_verification_failure() {
    // Simulates:
    //   id_pos(x)    // requires: x > 0
    //   proof_assert!(result > 0)
    //
    // Body: LetObligation { obligation: x > 0,
    //          body: LetAssume { assumption: call_result > 0,
    //                   body: call_result > 0 } }
    //
    // No precondition establishing x > 0, so the obligation fails.
    let body = let_obligation(
        gt(var("x"), int(0)),
        let_assume(
            gt(var("_call_result"), int(0)),
            gt(var("_call_result"), int(0)),
        ),
    );
    // ensures: result == true (the assertion should hold)
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "missing precondition for call obligation should cause failure: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn satisfied_obligation_allows_assumption_usage() {
    // Simulates:
    //   requires: x > 0
    //   id_pos(x)    // requires: x > 0, ensures: result > 0
    //   proof_assert!(call_result > 0)
    //
    // Body: LetObligation { obligation: x > 0,
    //          body: LetAssume { assumption: call_result > 0,
    //                   body: call_result > 0 } }
    //
    // With precondition x > 0, the obligation is satisfied and the
    // assumption can be used within scope.
    let requires = gt(var("x"), int(0));
    let body = let_obligation(
        gt(var("x"), int(0)),
        let_assume(
            gt(var("_call_result"), int(0)),
            gt(var("_call_result"), int(0)),
        ),
    );
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "satisfied obligation should allow assumption (not Failed/Error after #2202): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn obligation_not_discharged_by_unrelated_precondition() {
    // Simulates:
    //   requires: y > 0    // unrelated to x
    //   id_pos(x)          // requires: x > 0
    //
    // Body: LetObligation { obligation: x > 0, body: true }
    // Ensures: result == true
    //
    // y > 0 does NOT prove x > 0, so verification should FAIL.
    let requires = gt(var("y"), int(0));
    let body = let_obligation(gt(var("x"), int(0)), bool_expr(true));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "unrelated precondition should not discharge obligation: {result:?}"
    );
}

// ── Nesting: combined LetAssume + LetObligation ─────────────────────

#[test]
#[timeout(30000)]
fn nested_assume_and_obligation_compose_correctly() {
    // Two nested calls:
    //   id_pos(x)       // requires: x > 0, ensures: r1 > 0
    //   double_pos(r1)  // requires: r1 > 0 (from above ensures), ensures: r2 > 1
    //
    // Body:
    //   LetObligation { obligation: x > 0,       // id_pos precondition
    //     LetAssume { assumption: r1 > 0,         // id_pos postcondition
    //       LetObligation { obligation: r1 > 0,   // double_pos precondition
    //         LetAssume { assumption: r2 > 1,     // double_pos postcondition
    //           r2 > 1 }}}}
    //
    // With requires: x > 0, the chain should verify.
    let requires = gt(var("x"), int(0));
    let body = let_obligation(
        gt(var("x"), int(0)),
        let_assume(
            gt(var("r1"), int(0)),
            let_obligation(
                gt(var("r1"), int(0)),
                let_assume(gt(var("r2"), int(1)), gt(var("r2"), int(1))),
            ),
        ),
    );
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "chained call obligations should compose (not Failed/Error after #2202): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn nested_chain_fails_when_first_obligation_unsatisfied() {
    // Same chain as above but WITHOUT the precondition x > 0.
    // The first obligation fails, breaking the entire chain.
    let body = let_obligation(
        gt(var("x"), int(0)),
        let_assume(
            gt(var("r1"), int(0)),
            let_obligation(
                gt(var("r1"), int(0)),
                let_assume(gt(var("r2"), int(1)), gt(var("r2"), int(1))),
            ),
        ),
    );
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "unsatisfied first obligation should fail entire chain: {result:?}"
    );
}

// ── MIR Assert condition as LetAssume (#929) ────────────────────────

#[test]
#[timeout(30000)]
fn assert_condition_available_via_let_assume() {
    // Models: assert!(x > 0); proof_assert!(x > -1);
    // The MIR Assert terminator's condition (x > 0) should be wrapped as
    // LetAssume so it is available as a fact in the downstream proof.
    // This is the expression tree the driver now produces after the #929 fix.
    let body = let_assume(gt(var("x"), int(0)), gt(var("x"), int(-1)));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "assert condition should be usable (not Failed/Error after #2202): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn assert_condition_not_available_without_let_assume() {
    // Control test: without LetAssume wrapping (the pre-#929 behavior),
    // the proof body is just `x > -1` with no assumption about x.
    // The ensures `result == true` cannot be proved because x is unconstrained.
    let body = gt(var("x"), int(-1));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without assert assumption, proof should fail: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn assert_negated_condition_available_via_let_assume() {
    // Models: MIR Assert { cond: x == 0, expected: false, ... }
    // This corresponds to assert!(x != 0) which MIR encodes as
    // Assert { cond: x == 0, expected: false }. The driver wraps with
    // LetAssume { assumption: !(x == 0), body }.
    // We can prove the negated condition itself (x != 0) is available.
    let body = let_assume(not(eq(var("x"), int(0))), not(eq(var("x"), int(0))));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "negated assert condition should be usable (not Failed/Error after #2202): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn assert_negated_condition_not_available_without_let_assume() {
    // Control for the test above: without LetAssume wrapping, the negated
    // assert condition does not become a scoped fact and cannot prove result=true.
    let body = not(eq(var("x"), int(0)));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without LetAssume wrapping, negated condition should not prove ensures: {result:?}"
    );
}

// ── Soundness: encoding failure must not produce false Verified (#1029) ──

#[test]
#[timeout(30000)]
fn let_obligation_encoding_failure_must_not_verify() {
    // LetObligation { obligation: <unencodable>, body: true }
    // Ensures: result == true
    //
    // The obligation is a Float(NaN) expression, which the encoder rejects
    // via try_real_const. When the obligation fails to encode, the error
    // must propagate — a dropped obligation is unsound because the
    // precondition goes unchecked.
    //
    // Fixed in #1029: the error now propagates, producing an encoding error
    // instead of a false Verified result.
    // Updated for #985: closures now encode conservatively, so we use
    // Float(NaN) as the unencodable expression instead.
    use trust_wp_core::formula::FloatBits;

    let unencodable_obligation = PureExpr::Float(FloatBits::from_f64(f64::NAN));

    let body = let_obligation(unencodable_obligation, bool_expr(true));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    );

    // #1029 fix: obligation encoding failure must propagate as Err.
    // Dropping an obligation is unsound — the precondition would go unchecked.
    assert!(
        result.is_err(),
        "dropped obligation must propagate encoding error (soundness): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn let_obligation_encodable_obligation_verifies_when_satisfied() {
    // Positive counterpart: a normal encodable obligation on the same minimal
    // shape should verify rather than error or fail closed.
    let requires = gt(var("x"), int(0));
    let body = let_obligation(gt(var("x"), int(0)), bool_expr(true));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "encodable obligation should verify when satisfied: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_encoding_failure_is_sound() {
    // Control: LetAssume with a conservatively-encoded closure is sound.
    // The parameterized closure encodes as a fresh unconstrained Bool constant
    // (#985 conservative encoding), which does not help prove the ensures.
    // LetAssume { assumption: <closure->Bool const>, body: x > 0 }
    // Ensures: result == true
    //
    // The unconstrained Bool constant may be true or false, so x > 0 remains
    // unconstrained. result == true cannot be proved -> Failed.
    // This is correct: a weak/unconstrained assumption can only cause false negatives.
    use trust_wp_core::formula::PureExpr;

    let unencodable_assumption = PureExpr::Closure {
        params: vec![("y".to_string(), None)],
        body: Arc::new(gt(var("y"), int(0))),
    };

    let body = let_assume(unencodable_assumption, gt(var("x"), int(0)));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "dropped assumption should not help prove ensures: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_encodable_assumption_proves_same_body() {
    // Positive counterpart: with an encodable assumption on the same shape, the
    // body should become provable instead of staying unconstrained.
    let body = let_assume(gt(var("x"), int(0)), gt(var("x"), int(0)));
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "encodable assumption should prove the same body it assumes: {result:?}"
    );
}

// ── Try operator LetAssume soundness (#1266) ─────────────────────────
//
// The `?` operator on `Option<T>` and `Result<T, E>` desugars to
// `LetAssume(is_some(x), <body>)` or `LetAssume(is_ok(x), <body>)`.
// These tests verify that this encoding correctly models try semantics:
// 1. The assumption constrains the solver to the success path only
// 2. The inner value (collapsed ADT) is available in the body
// 3. The assumption does NOT leak outside the scope

#[test]
#[timeout(30000)]
fn try_operator_let_assume_is_some_constrains_success_path() {
    // Models: let inner = x?;  // x: Option<i32>
    // Extraction produces: LetAssume(is_some(x), <body using x as inner>)
    //
    // Force success path (`is_some(x)`) and negate body (`!(x > -1)`).
    //
    // If LetAssume is encoded correctly as implication, this is UNSAT:
    //   (is_some(x) => x > -1) && is_some(x) && !(x > -1)
    // We also sanity-check that `is_some(x)` itself is satisfiable so UNSAT
    // cannot come from a trivially-false tester encoding.
    let mut sat_encoder = AYEncoder::new();
    let is_some_x = method_call(var("x"), "is_some", vec![]);
    let is_some_term = sat_encoder.encode_pure(&is_some_x).unwrap();
    sat_encoder.assert_term(is_some_term);
    let sat_result = sat_encoder.check_sat();
    assert_eq!(
        sat_result,
        SolveResult::Sat,
        "is_some(x) should be satisfiable for some x (Some branch exists): {sat_result:?}"
    );

    let mut encoder = AYEncoder::new();
    let body = gt(var("x"), int(-1));
    let expr = let_assume(method_call(var("x"), "is_some", vec![]), body.clone());
    encoder.register_sort_hints(&[gt(var("x"), int(0))]);

    let term = encoder.encode_pure(&expr).unwrap();
    let is_some_term = encoder
        .encode_pure(&method_call(var("x"), "is_some", vec![]))
        .unwrap();
    let not_body_term = encoder.encode_pure(&not(body)).unwrap();
    encoder.assert_term(term);
    encoder.assert_term(is_some_term);
    encoder.assert_term(not_body_term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "forcing is_some(x) LetAssume should be UNSAT: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn try_operator_let_assume_is_ok_constrains_success_path() {
    // Result-path analogue of the Option test above, but non-vacuous:
    // force success path (`is_ok(x)`) and negate body (`!(x > -1)`).
    //
    // If LetAssume is encoded correctly as implication, this is UNSAT:
    //   (is_ok(x) => x > -1) && is_ok(x) && !(x > -1)
    // We also sanity-check that `is_ok(x)` itself is satisfiable so UNSAT
    // cannot come from a trivially-false tester encoding.
    let mut sat_encoder = AYEncoder::new();
    let is_ok_x = method_call(var("x"), "is_ok", vec![]);
    let is_ok_term = sat_encoder.encode_pure(&is_ok_x).unwrap();
    sat_encoder.assert_term(is_ok_term);
    let sat_result = sat_encoder.check_sat();
    assert_eq!(
        sat_result,
        SolveResult::Sat,
        "is_ok(x) should be satisfiable for some x (Ok branch exists): {sat_result:?}"
    );

    let mut encoder = AYEncoder::new();
    let body = gt(var("x"), int(-1));
    let expr = let_assume(method_call(var("x"), "is_ok", vec![]), body.clone());
    encoder.register_sort_hints(&[gt(var("x"), int(0))]);

    let term = encoder.encode_pure(&expr).unwrap();
    let is_ok_term = encoder
        .encode_pure(&method_call(var("x"), "is_ok", vec![]))
        .unwrap();
    let not_body_term = encoder.encode_pure(&not(body)).unwrap();
    encoder.assert_term(term);
    encoder.assert_term(is_ok_term);
    encoder.assert_term(not_body_term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "forcing is_ok(x) LetAssume should be UNSAT: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn try_operator_let_assume_does_not_assume_success_globally() {
    // The LetAssume encoding should NOT make is_some(x) a global fact.
    // After the LetAssume scope, properties that depend on is_some(x)
    // should not be provable without explicit preconditions.
    //
    // Use a non-trivial body (x > 0) to avoid the vacuous case where
    // body = true makes the implication trivially true regardless of
    // encoding correctness.
    //
    // Body: LetAssume { is_some(x), x > 0 }
    // Encoding: is_some(x) => (x > 0)
    //
    // After asserting the implication, NOT(is_some(x)) AND NOT(x > 0)
    // should be SAT — the failure path (None) is unconstrained.
    let mut failure_path_encoder = AYEncoder::new();
    let failure_path_expr = not(method_call(var("x"), "is_some", vec![]));
    let failure_path_term = failure_path_encoder
        .encode_pure(&failure_path_expr)
        .unwrap();
    failure_path_encoder.assert_term(failure_path_term);
    let fp_result = failure_path_encoder.check_sat();
    assert_eq!(
        fp_result,
        SolveResult::Sat,
        "NOT(is_some(x)) should itself be satisfiable (None path exists): {fp_result:?}"
    );

    let body_expr = gt(var("x"), int(0));
    let body = let_assume(method_call(var("x"), "is_some", vec![]), body_expr.clone());
    let mut encoder = AYEncoder::new();

    let term = encoder.encode_pure(&body).unwrap();
    encoder.assert_term(term);

    // Assert both NOT(is_some(x)) and NOT(x > 0) — should be SAT if
    // neither the assumption nor the body leak globally
    let not_is_some = not(method_call(var("x"), "is_some", vec![]));
    let neg_is_some_term = encoder.encode_pure(&not_is_some).unwrap();
    let neg_body_term = encoder.encode_pure(&not(body_expr)).unwrap();
    encoder.assert_term(neg_is_some_term);
    encoder.assert_term(neg_body_term);

    let scope_result = encoder.check_sat();
    assert_eq!(
        scope_result,
        SolveResult::Sat,
        "is_some(x) and body must not leak from LetAssume scope — \
         NOT(is_some(x)) AND NOT(x > 0) should remain satisfiable: {scope_result:?}"
    );
}

#[test]
#[timeout(30000)]
fn try_operator_let_assume_is_ok_does_not_assume_success_globally() {
    // Result-path analogue with non-trivial body:
    // LetAssume(is_ok(x), x > -1) must not force x > -1 when !is_ok(x).
    //
    // This guards against accidental global leakage of success-path facts.
    let mut failure_path_encoder = AYEncoder::new();
    failure_path_encoder.register_sort_hints(&[gt(var("x"), int(0))]);
    let failure_path_expr = not(method_call(var("x"), "is_ok", vec![]));
    let failure_path_term = failure_path_encoder
        .encode_pure(&failure_path_expr)
        .unwrap();
    failure_path_encoder.assert_term(failure_path_term);
    let fp_result = failure_path_encoder.check_sat();
    assert_eq!(
        fp_result,
        SolveResult::Sat,
        "NOT(is_ok(x)) should itself be satisfiable (Err path exists): {fp_result:?}"
    );

    let body_expr = gt(var("x"), int(-1));
    let body = let_assume(method_call(var("x"), "is_ok", vec![]), body_expr.clone());
    let mut encoder = AYEncoder::new();
    encoder.register_sort_hints(&[gt(var("x"), int(0))]);

    let term = encoder.encode_pure(&body).unwrap();
    encoder.assert_term(term);

    // If LetAssume scope leaks, this would become UNSAT.
    let not_is_ok = not(method_call(var("x"), "is_ok", vec![]));
    let neg_term = encoder.encode_pure(&not_is_ok).unwrap();
    let not_body_term = encoder.encode_pure(&not(body_expr)).unwrap();
    encoder.assert_term(neg_term);
    encoder.assert_term(not_body_term);

    let scope_result = encoder.check_sat();
    assert_eq!(
        scope_result,
        SolveResult::Sat,
        "when !is_ok(x), success-path body constraints must remain unset: {scope_result:?}"
    );
}

#[test]
#[timeout(30000)]
fn try_operator_let_assume_in_ite_branch_scoped() {
    // Models: if cond { let v = opt?; ... } else { ... }
    // The LetAssume from the try operator should be branch-scoped.
    //
    // Body: ITE(flag,
    //           LetAssume(is_some(x), x > 0),
    //           true)
    // Ensures: is_some(x) — should NOT be provable (only assumed in one branch)
    let body = ite(
        var("flag"),
        let_assume(
            method_call(var("x"), "is_some", vec![]),
            gt(var("x"), int(0)),
        ),
        bool_expr(true),
    );
    let ensures = method_call(var("x"), "is_some", vec![]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(
            result,
            VerificationResult::Failed(_)
                | VerificationResult::Unknown(UnknownReason::QuantifierEmatchingExistsIncomplete)
        ),
        "try operator assumption in ITE branch must not leak into a proof: {result:?}"
    );
}

// ── Soundness: contradictory LetAssume assumptions (#1394) ──────────

#[test]
#[timeout(30000)]
fn contradictory_let_assume_facts_must_not_vacuously_verify() {
    // Models the multiple-projected-write scenario from #1394/#1424:
    //   x.0 = 5;
    //   x.0 = 7;
    //   proof_assert!(false);
    //
    // After #1424, extraction must keep only the latest write fact for the
    // same projected path (last-write-wins):
    //   LetAssume { assumption: tuple_get_0(x) == 7, body: false }
    //
    // Expected: Failed (the absurd proof_assert condition is not provable).

    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    let latest_write = eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(7));
    let body = let_assume(latest_write, bool_expr(false));

    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "last-write-wins projected-write assumption must not vacuously verify \
         proof_assert!(false): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn latest_projected_write_fact_proves_latest_claim() {
    // Positive counterpart: the same last-write-wins fact should prove the
    // matching latest claim, rather than only participating in a failing body.
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    let latest_write = eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(7));
    let body = let_assume(
        latest_write.clone(),
        eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(7)),
    );
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "latest projected-write fact should prove the latest claim: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn single_let_assume_projected_write_fact_is_sound() {
    // Control test: a single projected-write LetAssume fact is sound.
    // Models: x.0 = 5; proof_assert!(tuple_get_0(x) == 5)
    //
    // The assumption tuple_get_0(x) == 5 should allow proving the same fact.

    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    let assumption = eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(5));
    let provable_body = eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(5));

    let body = let_assume(assumption, provable_body);
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "projected-write assumption should prove fact: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn single_let_assume_projected_write_does_not_over_constrain() {
    // The assumption tuple_get_0(x) == 5 should NOT allow proving
    // tuple_get_0(x) == 7 — that would mean the assumption over-constrains
    // in a way that produces false positives.

    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    let assumption = eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(5));
    let wrong_claim = eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(7));

    let body = let_assume(assumption, wrong_claim);
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "assumption x.0==5 must not prove x.0==7: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn stale_projected_write_fact_after_whole_reassignment_must_not_verify() {
    // Models the stale-fact scenario from projected-write extraction:
    //   pair.1 = 10;       // projected-write fact: tuple_get_1(pair) == 10
    //   pair = (7, 20);    // whole-local overwrite — should invalidate ALL facts
    //   proof_assert!(tuple_get_1(pair) == 10)  // should FAIL (pair.1 is now 20)
    //
    // If extraction does not clear projected_write_facts on whole-local
    // reassignment, the stale fact `tuple_get_1(pair) == 10` remains and could
    // allow the proof_assert to verify vacuously when the body references the
    // same symbolic variable.
    //
    // At the SMT level, this models:
    //   LetAssume { tuple_get_1(x) == 10, body: tuple_get_1(x) == 10 }
    //
    // This should verify (the assumption implies the body trivially), which is
    // UNSOUND when the stale fact should have been cleared. The ay level cannot
    // catch this — it faithfully encodes LetAssume as implication. The fix must
    // be in the extraction layer.
    //
    // This test documents that the ay layer CORRECTLY encodes the stale fact
    // as a valid implication. The soundness responsibility lies in extraction
    // clearing facts on whole-local reassignment.

    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let stale_assumption = eq(logic_fn_call(&tuple_get_1, vec![var("x")]), int(10));
    let body_claim = eq(logic_fn_call(&tuple_get_1, vec![var("x")]), int(10));

    let body = let_assume(stale_assumption, body_claim);
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();

    // The LetAssume encoding is `(=> (= (tuple_get_1 x) 10) (= (tuple_get_1 x) 10))`
    // which is trivially valid. This VERIFIES at the ay level.
    // This is the expected behavior: ay faithfully encodes the implication.
    // The soundness bug is upstream in extraction (not clearing stale facts).
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "stale LetAssume should verify (soundness in extraction, not encoding): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn nested_substruct_overwrite_stale_deep_field_fact_documents_unsoundness() {
    // Models the nested sub-struct overwrite soundness gap (#1500):
    //   x.a.b = 10;         // fact: tuple_get_b(tuple_get_a(x)) == 10
    //   x.a = new_struct;   // fact: tuple_get_a(x) == new_struct
    //                       // STALE: tuple_get_b(tuple_get_a(x)) == 10 NOT cleared
    //   proof_assert!(tuple_get_b(tuple_get_a(x)) == 10)  // should FAIL
    //
    // At the SMT level with both facts as LetAssume:
    //   LetAssume { tuple_get_b(tuple_get_a(x)) == 10,
    //     LetAssume { tuple_get_a(x) == new_val,
    //       body: tuple_get_b(tuple_get_a(x)) == 10
    //     }
    //   }
    //
    // The outer assumption directly implies the body, making this vacuously
    // Verified at the ay level. This documents the EXPECTED ay behavior —
    // the fix must be in extraction (invalidating deep-path facts on sub-struct
    // overwrite).

    let tuple_get_a =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_b =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    // Deep field: tuple_get_b(tuple_get_a(x))
    let deep_field = logic_fn_call(
        &tuple_get_b,
        vec![logic_fn_call(&tuple_get_a, vec![var("x")])],
    );
    // Shallow field: tuple_get_a(x)
    let shallow_field = logic_fn_call(&tuple_get_a, vec![var("x")]);

    // Stale assumption from x.a.b = 10
    let stale_deep_assumption = eq(deep_field.clone(), int(10));
    // New assumption from x.a = new_val (value 99 representing new_struct)
    let overwrite_assumption = eq(shallow_field, int(99));
    // Body claims the stale deep field value still holds
    let body_claim = eq(deep_field, int(10));

    // Nest: outer stale deep assumption wraps inner overwrite assumption wraps body
    let inner = let_assume(overwrite_assumption, body_claim);
    let body = let_assume(stale_deep_assumption, inner);
    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();

    // This VERIFIES because the outer LetAssume (tuple_get_b(tuple_get_a(x)) == 10)
    // directly implies the body claim. The inner overwrite to tuple_get_a(x) cannot
    // invalidate the outer assumption at the SMT level.
    //
    // This is the ay-level documentation of #1500: the fix must be in extraction
    // (clearing deep-path facts when a shallower prefix is overwritten).
    //
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "stale nested LetAssume should verify (documents #1500 — fix in extraction): {result:?}"
    );
}
