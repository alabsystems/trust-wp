// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Outside any ITE branch, LetAssume non-Bool body asserts assumption globally.
#[test]
#[timeout(30000)]
fn test_non_bool_let_assume_no_branch_asserts_globally() {
    let mut encoder = AYEncoder::new();

    let expr = let_assume(gt(var("x"), int(5)), add(var("x"), int(1)));
    let term = encoder.encode_pure(&expr).unwrap();

    // x + 1 <= 5 should be UNSAT because x > 5 was asserted globally
    let five = encoder.solver_mut().int_const(5);
    let le_five = encoder.solver_mut().le(term, five);
    encoder.assert_term(le_five);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x > 5 asserted at top level means x + 1 > 6"
    );
}

/// Inside then-branch, assumption is guarded by condition.
/// When branch NOT taken, assumption must not hold.
#[test]
#[timeout(30000)]
fn test_non_bool_let_assume_in_then_branch_guarded() {
    let mut encoder = AYEncoder::new();

    let expr = ite(
        gt(var("y"), int(0)),
        let_assume(gt(var("x"), int(0)), add(var("x"), int(1))),
        int(0),
    );
    let _term = encoder.encode_pure(&expr).unwrap();

    // Force else branch: y <= 0
    let y_neg = encoder.encode_pure(&not(gt(var("y"), int(0)))).unwrap();
    encoder.assert_term(y_neg);

    // x <= 0 should be satisfiable
    let x_neg = encoder.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    encoder.assert_term(x_neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Branch-guarded assumption must not constrain x when branch not taken"
    );
}

/// Nested ITE: path guard should be conjunction of all branch conditions.
#[test]
#[timeout(30000)]
fn test_nested_branches_conjoin_path_conditions() {
    let mut encoder = AYEncoder::new();

    let expr = ite(
        gt(var("a"), int(0)),
        ite(
            gt(var("b"), int(0)),
            let_assume(gt(var("x"), int(100)), add(var("x"), int(1))),
            int(0),
        ),
        int(0),
    );
    let _term = encoder.encode_pure(&expr).unwrap();

    // a > 0 but b <= 0: inner condition not met
    let a_pos = encoder.encode_pure(&gt(var("a"), int(0))).unwrap();
    let b_neg = encoder.encode_pure(&not(gt(var("b"), int(0)))).unwrap();
    encoder.assert_term(a_pos);
    encoder.assert_term(b_neg);

    // x = 0 should be SAT (assumption only fires when BOTH a>0 AND b>0)
    let x_zero = encoder.encode_pure(&eq(var("x"), int(0))).unwrap();
    encoder.assert_term(x_zero);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Nested path guard: assumption only holds when all branch conditions met"
    );
}

/// When nested branch IS taken, the assumption must hold.
#[test]
#[timeout(30000)]
fn test_nested_branches_assumption_enforced_when_taken() {
    let mut encoder = AYEncoder::new();

    let expr = ite(
        gt(var("a"), int(0)),
        ite(
            gt(var("b"), int(0)),
            let_assume(gt(var("x"), int(100)), add(var("x"), int(1))),
            int(0),
        ),
        int(0),
    );
    let _term = encoder.encode_pure(&expr).unwrap();

    // Force both branches: a > 0 AND b > 0
    let a_pos = encoder.encode_pure(&gt(var("a"), int(0))).unwrap();
    let b_pos = encoder.encode_pure(&gt(var("b"), int(0))).unwrap();
    encoder.assert_term(a_pos);
    encoder.assert_term(b_pos);

    // x <= 0 should be UNSAT because (a>0 ∧ b>0) => x > 100
    let x_neg = encoder.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    encoder.assert_term(x_neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When both branch conditions hold, the assumption must constrain x"
    );
}

/// After an error in an Ite branch, the encoder remains usable because
/// the RAII `PathConditionGuard` pops the stale condition on drop. (#1207)
///
/// Regression: the original test used `add(var("x"), int(1))` as follow-up,
/// which doesn't read `path_conditions` and would pass even with a corrupted
/// stack. This version uses a LetAssume inside an Ite to exercise
/// `guard_with_active_path`, which DOES read `path_conditions`. (#1228)
#[test]
#[timeout(30000)]
fn test_ite_branch_error_does_not_corrupt_path_conditions() {
    let mut encoder = AYEncoder::new();

    // Build an Ite where the then-branch returns an encoding error.
    let unencodable = crate::tests::helpers::unencodable_float_order();
    let error_ite = ite(gt(var("a"), int(0)), unencodable, int(0));

    // The Ite encoding should fail because the then-branch is unsupported.
    let result = encoder.encode_pure(&error_ite);
    assert!(
        result.is_err(),
        "expected encoding error from the refused branch: {result:?}"
    );

    // Encode a NEW Ite with a LetAssume in the then-branch. This exercises
    // `guard_with_active_path` which reads `path_conditions`. If the
    // previous error left a stale entry in `path_conditions`, the guard
    // would be a conjunction of (stale condition AND y > 0) instead of
    // just (y > 0), producing incorrect scoping.
    let guarded_ite = ite(
        gt(var("y"), int(0)),
        let_assume(gt(var("x"), int(0)), add(var("x"), int(1))),
        int(0),
    );
    let _term = encoder
        .encode_pure(&guarded_ite)
        .expect("encoder should remain usable after Ite branch error");

    // Force else branch: y <= 0. The assumption x > 0 should NOT hold.
    let y_neg = encoder.encode_pure(&not(gt(var("y"), int(0)))).unwrap();
    encoder.assert_term(y_neg);

    // x <= 0 should be SAT because the assumption is guarded by y > 0,
    // which is false. If path_conditions were corrupted (stale a > 0 entry),
    // the guard would be `implies(a > 0 AND y > 0, x > 0)` and x <= 0
    // could be SAT for wrong reasons (when a <= 0 the implication is vacuously
    // true). We need to also force a > 0 to distinguish corruption from correct
    // behavior.
    let a_pos = encoder.encode_pure(&gt(var("a"), int(0))).unwrap();
    encoder.assert_term(a_pos);

    let x_neg = encoder.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    encoder.assert_term(x_neg);

    // With a > 0 forced: if path_conditions is clean, the guard is
    // `implies(y > 0, x > 0)`. Since y <= 0, x > 0 is unconstrained,
    // so x <= 0 is SAT. If path_conditions is corrupted with stale
    // `a > 0`, the guard would be `implies(a > 0 AND y > 0, x > 0)`.
    // Since a > 0 is true and y <= 0, the conjunction is false, so
    // the implication is vacuously true. x <= 0 is still SAT — but
    // for the wrong reason. To catch this, we also test the branch-taken
    // case below.
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "x <= 0 should be SAT when y <= 0 (assumption not active)"
    );
}

/// Companion to the error-recovery test: verifies the assumption IS enforced
/// when the branch is taken, proving path_conditions scoping is correct
/// after error recovery. (#1228)
#[test]
#[timeout(30000)]
fn test_ite_branch_error_recovery_assumption_enforced_when_taken() {
    let mut encoder = AYEncoder::new();

    // Trigger the same error as the companion test.
    let unsupported_closure = PureExpr::Closure {
        params: vec![],
        body: Arc::new(int(1)),
    };
    let error_ite = ite(gt(var("a"), int(0)), unsupported_closure, int(0));
    let _ = encoder.encode_pure(&error_ite);

    // Encode a clean Ite with LetAssume.
    let guarded_ite = ite(
        gt(var("y"), int(0)),
        let_assume(gt(var("x"), int(100)), add(var("x"), int(1))),
        int(0),
    );
    encoder.encode_pure(&guarded_ite).unwrap();

    // Force then-branch: y > 0. The assumption x > 100 MUST hold.
    let y_pos = encoder.encode_pure(&gt(var("y"), int(0))).unwrap();
    encoder.assert_term(y_pos);

    // x <= 0 should be UNSAT because y > 0 => x > 100.
    let x_neg = encoder.encode_pure(&not(gt(var("x"), int(0)))).unwrap();
    encoder.assert_term(x_neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When branch taken after error recovery, assumption must constrain x"
    );
}
