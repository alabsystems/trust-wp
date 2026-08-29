// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Term, TermKind};
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use crate::{
    encoder::AYEncoder,
    tests::helpers::{
        and, binop, div, eq, exists_with_sort, ge, gt, implies, int, le, logic_fn_call, lt,
        match_expr, method_call, ne, var,
    },
    verify::{
        classify_negated_postcondition_route, encode_and_assert_negated_postconditions,
        encode_negated_postcondition, is_trivially_true_postcondition,
        is_trivially_true_postcondition_under_requires, negate_existential_postcondition,
        result_postcondition_matches_return_expr,
        result_postcondition_matches_return_expr_via_logic_bodies, NegatedPostconditionRoute,
    },
    BinOp, ExprSort, Pattern, PureExpr, UnOp,
};

fn term_contains_negated_quantifier(encoder: &AYEncoder, term: Term) -> bool {
    let solver = encoder.solver();
    let mut stack = vec![term];
    let mut seen = std::collections::HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(solver.term_kind(term), TermKind::Not)
            && solver
                .term_children(term)
                .into_iter()
                .any(|child| matches!(solver.term_kind(child), TermKind::Forall | TermKind::Exists))
        {
            return true;
        }
        stack.extend(solver.term_children(term));
    }
    false
}

// --- negate_existential_postcondition: unit tests ---

/// Single existential: `exists<x:Int> x > 0` → `forall<x:Int> NOT(x > 0)`
#[test]
fn negate_single_existential() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(gt(var("x"), int(0))),
        triggers: vec![],
    };
    let negated = negate_existential_postcondition(&expr).expect("should negate top-level exists");
    match negated {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            assert_eq!(var, "x");
            assert_eq!(var_sort, Some(ExprSort::Int));
            assert!(
                matches!(body.as_ref(), PureExpr::UnOp(UnOp::Not, _)),
                "body should be NOT(...): got {body:?}"
            );
            assert!(triggers.is_empty());
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// Consecutive nested existentials: `exists<a> exists<b> P(a,b)`
/// → `forall<a> forall<b> NOT P(a,b)`
#[test]
fn negate_consecutive_nested_existentials() {
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(and(gt(var("a"), int(0)), var("b"))),
        triggers: vec![],
    };
    let outer = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(inner),
        triggers: vec![],
    };

    let negated = negate_existential_postcondition(&outer).expect("should negate nested exists");

    // Outer: forall<a:Int>
    match &negated {
        PureExpr::Forall {
            var: outer_var,
            var_sort: outer_sort,
            body: outer_body,
            ..
        } => {
            assert_eq!(outer_var, "a");
            assert_eq!(outer_sort, &Some(ExprSort::Int));
            // Inner: forall<b:Bool> NOT(...)
            match outer_body.as_ref() {
                PureExpr::Forall {
                    var: inner_var,
                    var_sort: inner_sort,
                    body: inner_body,
                    ..
                } => {
                    assert_eq!(inner_var, "b");
                    assert_eq!(inner_sort, &Some(ExprSort::Bool));
                    assert!(
                        matches!(inner_body.as_ref(), PureExpr::UnOp(UnOp::Not, _)),
                        "innermost body should be NOT(...): got {inner_body:?}"
                    );
                }
                other => panic!("expected inner Forall, got {other:?}"),
            }
        }
        other => panic!("expected outer Forall, got {other:?}"),
    }
}

/// Non-existential returns None — negate_existential_postcondition only handles
/// top-level Exists.
#[test]
fn negate_non_existential_returns_none() {
    assert!(negate_existential_postcondition(&gt(var("x"), int(0))).is_none());
    assert!(negate_existential_postcondition(&PureExpr::Bool(true)).is_none());
    assert!(negate_existential_postcondition(&var("x")).is_none());
    // Forall is not Exists — should return None
    let forall = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(gt(var("x"), int(0))),
        triggers: vec![],
    };
    assert!(negate_existential_postcondition(&forall).is_none());
}

/// Triggers are preserved through negation.
#[test]
fn negate_existential_preserves_triggers() {
    let trigger = vec![gt(var("x"), int(0))];
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(gt(var("x"), int(0))),
        triggers: vec![trigger.clone()],
    };
    let negated = negate_existential_postcondition(&expr).expect("should negate");
    match negated {
        PureExpr::Forall { triggers, .. } => {
            assert_eq!(triggers.len(), 1, "trigger should be preserved");
            assert_eq!(triggers[0], trigger);
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// var_sort None is preserved.
#[test]
fn negate_existential_preserves_none_sort() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![],
    };
    let negated = negate_existential_postcondition(&expr).expect("should negate");
    match negated {
        PureExpr::Forall { var_sort, .. } => {
            assert_eq!(var_sort, None);
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

// --- encode_and_assert_negated_postconditions: slow path ---

/// Mixed existential + non-existential postconditions use the slow path
/// in `encode_and_assert_negated_postconditions`, where each postcondition
/// is negated individually (De Morgan for existentials, ay-level NOT for
/// others) and combined with OR.
///
/// Verifies: when the conjunction `P AND exists<a:Bool> a` holds, the
/// negation `NOT P OR forall<a> NOT a` is not satisfiable (i.e. the
/// postcondition is verified). Uses Bool-sorted quantifier for decidability.
#[test]
#[timeout(30000)]
fn slow_path_mixed_existential_and_non_existential_postcondition() {
    // Postconditions: [result > 0, exists<a:Bool> a]
    // Precondition: result == 5 (makes result > 0 true)
    // exists<a:Bool> a is true (a = true is a witness).
    // So the conjunction holds, and the negation should be UNSAT.
    let ensures = vec![
        gt(var("result"), int(0)),
        exists_with_sort("a", ExprSort::Bool, var("a")),
    ];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // Assert the precondition: result == 5
    let result_val = encoder
        .encode_pure(&binop(var("result"), BinOp::Eq, int(5)))
        .expect("precondition should encode");
    encoder.assert_term(result_val);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted, "non-empty ensures should assert terms");

    // Negation of (result > 0 AND exists a. a) with result == 5 should be UNSAT.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "slow path negation of valid postconditions should be UNSAT"
    );
}

/// The slow path must correctly combine with OR: if ANY postcondition fails,
/// the negation is satisfiable. Verifies: `[result > 0, result < 0]` with
/// `result == 5` — the second postcondition fails, so negation is SAT.
#[test]
#[timeout(30000)]
fn slow_path_mixed_existential_negation_detects_failure() {
    // Postconditions: [exists<a:Bool> a, result < 0]
    // Precondition: result == 5 (makes result < 0 false)
    // NOT(exists<a> a) OR NOT(result < 0) — second disjunct is true.
    let ensures = vec![
        exists_with_sort("a", ExprSort::Bool, var("a")),
        binop(var("result"), BinOp::Lt, int(0)),
    ];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_val = encoder
        .encode_pure(&binop(var("result"), BinOp::Eq, int(5)))
        .expect("precondition should encode");
    encoder.assert_term(result_val);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted, "non-empty ensures should assert negation terms");

    // One postcondition fails (result < 0 when result == 5), so negation is SAT.
    assert_ne!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "slow path should detect failing postcondition"
    );
}

/// Fast path (no existentials): verify it still works correctly.
#[test]
#[timeout(30000)]
fn fast_path_non_existential_postconditions_verified() {
    let ensures = vec![
        gt(var("result"), int(0)),
        binop(var("result"), BinOp::Lt, int(10)),
    ];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_val = encoder
        .encode_pure(&binop(var("result"), BinOp::Eq, int(5)))
        .expect("precondition should encode");
    encoder.assert_term(result_val);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(
        asserted,
        "fast path non-empty ensures should assert negation terms"
    );

    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "fast path negation should be UNSAT: got {sat_result:?}"
    );
}

/// Empty ensures with no division obligations returns Ok(false).
#[test]
#[timeout(30000)]
fn empty_ensures_returns_false() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &[], None, None)
        .expect("should succeed");
    assert!(!asserted, "empty ensures should return false");
}

#[test]
#[timeout(30000)]
fn top_level_implication_negation_is_equivalent_when_verified() {
    let ensure = binop(var("a"), BinOp::Implies, var("b"));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let a = encoder.encode_formula(&var("a")).expect("encode a");
    encoder.assert_term(a);
    let b = encoder.encode_formula(&var("b")).expect("encode b");
    encoder.assert_term(b);

    let negated = encode_negated_postcondition(&mut encoder, &ensure, None, None)
        .expect("implication negation should encode");
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "a && b should make NOT(a ==> b) unsatisfiable"
    );
}

#[test]
#[timeout(30000)]
fn top_level_implication_negation_detects_counterexample() {
    let ensure = binop(var("a"), BinOp::Implies, var("b"));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let a = encoder.encode_formula(&var("a")).expect("encode a");
    encoder.assert_term(a);
    let b = encoder.encode_formula(&var("b")).expect("encode b");
    let not_b = encoder.solver_mut().not(b);
    encoder.assert_term(not_b);

    let negated = encode_negated_postcondition(&mut encoder, &ensure, None, None)
        .expect("implication negation should encode");
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "a && !b should satisfy NOT(a ==> b)"
    );
}

// --- encode_and_assert_negated_postconditions: nested existential (#1152) ---

/// A postcondition with a nested existential (not top-level) must still
/// trigger the slow path. Before #1152, `x > 0 && exists<a:Bool> a` was
/// treated as a non-existential postcondition (fast path), because the
/// top-level constructor is `BinOp`, not `Exists`. The slow path handles
/// embedded existentials via `encode_negated_postcondition`.
#[test]
#[timeout(30000)]
fn slow_path_nested_existential_in_conjunction() {
    // Single postcondition: `result > 0 AND exists<a:Bool> a`
    // Precondition: result == 5 (makes result > 0 true)
    // exists<a:Bool> a is satisfiable (a = true). Conjunction holds.
    let nested_exists = exists_with_sort("a", ExprSort::Bool, var("a"));
    let ensures = vec![and(gt(var("result"), int(0)), nested_exists)];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_val = encoder
        .encode_pure(&binop(var("result"), BinOp::Eq, int(5)))
        .expect("precondition should encode");
    encoder.assert_term(result_val);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted, "non-empty ensures should assert terms");

    // Negation of valid postcondition should be UNSAT.
    let sat_result = encoder.check_sat();
    assert_ne!(
        sat_result,
        SolveResult::Sat,
        "slow path negation of valid nested-existential postcondition should not be SAT"
    );
}

/// Nested existential with a failing non-existential sibling: the slow
/// path must still detect the failure. `result < 0` fails when result == 5.
#[test]
#[timeout(30000)]
fn slow_path_nested_existential_detects_failure() {
    // Single postcondition: `result < 0 AND exists<a:Bool> a`
    // Precondition: result == 5 → result < 0 is false → conjunction is false.
    let nested_exists = exists_with_sort("a", ExprSort::Bool, var("a"));
    let ensures = vec![and(binop(var("result"), BinOp::Lt, int(0)), nested_exists)];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_val = encoder
        .encode_pure(&binop(var("result"), BinOp::Eq, int(5)))
        .expect("precondition should encode");
    encoder.assert_term(result_val);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted, "non-empty ensures should assert terms");

    // Postcondition is false (result < 0 fails), so negation should be SAT.
    assert_ne!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "slow path should detect failing nested-existential postcondition"
    );
}

// --- encode_and_assert_negated_postconditions: division obligations (#1629) ---

/// Division obligations from body encoding are drained and conjoined with
/// postconditions. When the obligation is unsatisfied (divisor could be 0),
/// the negated conjunction is SAT (= verification failure). (#1629)
#[test]
#[timeout(30000)]
fn division_obligation_makes_negated_conjunction_sat() {
    let mut encoder = AYEncoder::new();
    // Simulate body encoding that produced a division by unconstrained `y`.
    // encode_pure(div(x, y)) creates the obligation and the int_div term.
    let body_term = encoder
        .encode_pure(&div(var("x"), var("y")))
        .expect("body should encode");
    assert_eq!(encoder.division_obligations_for_test().len(), 1);

    // Assert body: result = x / y
    let result_var = encoder
        .get_or_declare_var("result", ay_dpll::api::Sort::Int)
        .expect("declare result");
    let eq_term = encoder.solver_mut().eq(result_var, body_term);
    encoder.assert_term(eq_term);

    // Postcondition: result >= 0 (would otherwise verify without obligations)
    let ensures = [ge(var("result"), int(0))];

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted);

    // Obligations drained
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "obligations must be drained after encode_and_assert_negated_postconditions"
    );

    // The negated conjunction includes NOT(obligation), so the solver can
    // find y=0 as a counterexample. Result should NOT be Unsat.
    let result = encoder.check_sat();
    assert_ne!(
        result,
        SolveResult::unsat(),
        "with unproven division obligation, negated postcondition must not be UNSAT"
    );
}

/// When a precondition asserts y != 0, the division obligation is satisfied
/// and verification succeeds (negated conjunction is UNSAT). (#1629)
#[test]
#[timeout(30000)]
fn division_obligation_satisfied_by_precondition() {
    let mut encoder = AYEncoder::new();
    // Precondition: y != 0
    let precond = encoder
        .encode_pure(&ne(var("y"), int(0)))
        .expect("precond should encode");
    encoder.assert_term(precond);

    // Body: x / y
    let body_term = encoder
        .encode_pure(&div(var("x"), var("y")))
        .expect("body should encode");
    assert_eq!(encoder.division_obligations_for_test().len(), 1);

    // The test is about obligation discharge, not quotient semantics.
    let _ = body_term;
    let ensures = [PureExpr::Bool(true)];

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted);

    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "division obligation satisfied by y != 0 precondition should verify, got {sat:?}"
    );
}

/// Empty ensures but with division obligations: the obligations alone
/// are asserted as a negated conjunction so that unproven divisor safety
/// prevents trivial verification. (#1629)
#[test]
#[timeout(30000)]
fn empty_ensures_with_division_obligations_asserts() {
    let mut encoder = AYEncoder::new();
    // Simulate body that divided by unconstrained y
    let _body = encoder
        .encode_pure(&div(var("x"), var("y")))
        .expect("body should encode");
    assert_eq!(encoder.division_obligations_for_test().len(), 1);

    // No postconditions — but obligations exist
    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &[], None, None)
        .expect("should succeed");
    assert!(
        asserted,
        "empty ensures with division obligations should return true (asserted)"
    );

    // The negated obligation NOT(y != 0) = y == 0 is satisfiable
    assert_ne!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "unproven obligation with empty ensures must not be UNSAT"
    );
}

// --- negate_existential_postcondition: non-consecutive ---

/// Non-consecutive existentials: `exists<a> (a > 0 AND exists<b> b > 0)`
/// Only the outer exists is rewritten; the inner exists inside the AND
/// is NOT reachable by the recursive De Morgan (it only handles consecutive
/// exists nodes, not exists nested under other operators).
#[test]
#[timeout(30000)]
fn negate_non_consecutive_existential_only_rewrites_outer() {
    let inner_exists = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(gt(var("b"), int(0))),
        triggers: vec![],
    };
    // exists<a> (a > 0 AND exists<b> b > 0)
    let expr = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(and(gt(var("a"), int(0)), inner_exists.clone())),
        triggers: vec![],
    };

    let negated =
        negate_existential_postcondition(&expr).expect("top-level existential should be rewritten");

    // Should produce: forall<a> NOT(a > 0 AND exists<b> b > 0)
    // The inner exists<b> should be preserved (NOT pushed into AND, not through exists<b>).
    match negated {
        PureExpr::Forall { var, body, .. } => {
            assert_eq!(var, "a");
            // Body should be NOT(original_body) — a single UnOp::Not wrapping the AND
            match body.as_ref() {
                PureExpr::UnOp(UnOp::Not, inner) => {
                    // The inner should be (a > 0 AND exists<b> b > 0) — unchanged
                    match inner.as_ref() {
                        PureExpr::BinOp(_, BinOp::And, rhs) => {
                            // RHS should still be exists<b>, not forall<b>
                            assert!(
                                matches!(rhs.as_ref(), PureExpr::Exists { .. }),
                                "inner exists should NOT be rewritten through AND: got {rhs:?}"
                            );
                        }
                        other => panic!("expected AND body, got {other:?}"),
                    }
                }
                other => panic!("expected NOT wrapper, got {other:?}"),
            }
        }
        other => panic!("expected forall rewrite, got {other:?}"),
    }
}

// --- encode_and_assert_negated_postconditions: non-Bool sort rejection ---

/// Non-boolean postconditions/assertions (e.g., a bare integer) are rejected
/// with an `EncodingError` before reaching ay's `mk_not`. (#1028)
#[test]
#[timeout(30000)]
fn non_bool_postcondition_returns_encoding_error() {
    let ensures = vec![int(0)]; // Int, not Bool
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None);
    let err_msg = result
        .expect_err("non-Bool ensures should return Err")
        .to_string();
    assert!(
        err_msg.contains("boolean"),
        "error should mention 'boolean': {err_msg}"
    );
}

/// A mix of Bool and non-Bool postconditions is rejected if any is non-Bool.
#[test]
#[timeout(30000)]
fn mixed_bool_and_int_postcondition_returns_encoding_error() {
    let ensures = vec![
        gt(var("result"), int(0)), // Bool
        int(42),                   // Int — invalid
    ];
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None);
    let _ = result.expect_err("mixed ensures with non-Bool should return Err");
}

// --- encode_and_assert_negated_postconditions: Bool formula context (#2245) ---

/// Regression for #2245: a bare `predicate.index_logic(...)` postcondition must
/// not panic with "sort mismatch in not: expected Bool, got Int". The
/// `encode_formula` path seeds Bool-context hints before encoding, so Mapping-
/// like predicate lookups are routed through Bool-context dispatch. This test
/// models `proof_assert!(predicate[-y@ - 1])` from `such_that.rs`.
#[test]
#[timeout(30000)]
fn predicate_index_logic_postcondition_does_not_panic_2245() {
    use crate::tests::helpers::{method_call, neg};

    // Postcondition: predicate.index_logic(-y - 1)
    // This models the `predicate[-y@ - 1]` proof_assert from such_that.rs.
    let predicate_lookup = method_call(
        var("predicate"),
        "index_logic",
        vec![binop(neg(var("y")), BinOp::Sub, int(1))],
    );
    let ensures = vec![predicate_lookup];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // The critical property: encoding must not panic with sort mismatch.
    let result = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None);
    assert!(
        result.is_ok(),
        "predicate.index_logic postcondition should encode without panic: {result:?}"
    );
}

// --- encode_and_assert_negated_postconditions: logic_fns + return_expr threading (#2580) ---

/// Regression for #2580: `encode_and_assert_negated_postconditions` previously
/// hardcoded `None` for both `logic_fns` and `return_expr` when delegating to
/// `encode_negated_postcondition`, making the skolemization and witness
/// instantiation paths unreachable. This test verifies the `logic_fns`
/// parameter is now threaded through by exercising the skolemization path
/// for a universal postcondition when an open logic function is present.
#[test]
#[timeout(30000)]
fn logic_fns_threading_enables_skolemization_path_2580() {
    // Mixed ensures: [forall<a:Int> a > 0, exists<b:Bool> b]
    // The exists triggers the slow path. The forall hits the
    // has_open_logic_fns → skolemize_negated_universal branch when
    // logic_fns is Some.
    let ensures = vec![
        PureExpr::Forall {
            var: "a".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(gt(var("a"), int(0))),
            triggers: vec![],
        },
        exists_with_sort("b", ExprSort::Bool, var("b")),
    ];

    // Open logic function triggers the skolemization path.
    let mut logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    );
    logic_fn.set_mode(LogicMode::Open);
    let fns = [logic_fn];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // forall<a:Int> a > 0 is FALSE (counterexample: a=0).
    // Negation: NOT(forall<a> a > 0) is SAT.
    // exists<b:Bool> b is TRUE (b=true).
    // Negation: forall<b:Bool> NOT b is FALSE (b=true refutes).
    // Combined: NOT(forall a>0) OR NOT(exists b. b) should be SAT.
    let asserted =
        encode_and_assert_negated_postconditions(&mut encoder, &ensures, Some(&fns), None)
            .expect("should encode with logic_fns");
    assert!(asserted, "non-empty ensures should assert terms");

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "negation of (forall a>0 AND exists b) should be SAT \
         (forall a>0 is false). Got {result:?}"
    );
}

// --- is_trivially_true_postcondition: unit tests (#2696) ---

/// `Bool(true)` is trivially true.
#[test]
fn trivially_true_bool_literal() {
    assert!(is_trivially_true_postcondition(&PureExpr::Bool(true)));
    assert!(!is_trivially_true_postcondition(&PureExpr::Bool(false)));
}

/// Reflexive equality `x == x` is trivially true.
#[test]
fn trivially_true_reflexive_equality() {
    let x = var("x");
    let expr = eq(x.clone(), x);
    assert!(is_trivially_true_postcondition(&expr));
}

/// Non-reflexive equality `x == y` is NOT trivially true.
#[test]
fn non_reflexive_equality_not_trivially_true() {
    assert!(!is_trivially_true_postcondition(&eq(var("x"), var("y"))));
}

// ★ #125 pins: the no-solve accepting path (`Verified(None)` via
// `is_trivially_true_postcondition_under_requires`, a path that BYPASSES the
// solver) must never fold or structurally accept `Final(<literal>)` — the
// print of the driver's borrow-chain advance of a borrowed place's constant
// value, the 8d7bf70 false-accept class. Mirrors
// `AYEncoder::refuse_prophecy_over_constant`'s fail-closed semantics.

#[test]
fn final_over_literal_never_trivially_accepts() {
    use crate::tests::helpers::{final_expr, forall};

    // The folding route: `^3 == 3` is the exact evil-shape goal the driver
    // minted pre-#124 (`x` lowered to `Final(Int(3))`).
    let folded = eq(final_expr(int(3)), int(3));
    assert!(!is_trivially_true_postcondition(&folded));
    assert!(!is_trivially_true_postcondition_under_requires(
        &folded,
        &[]
    ));

    // The reflexive route: `^3 == ^3` is structurally identical on both
    // sides, but the two prints may denote DIFFERENT conflated prophecies
    // (the `7 + 7 == 9` conflation closed by #124) — the sort-agnostic
    // reflexivity arm must not accept it without a solve.
    let reflexive = eq(final_expr(int(3)), final_expr(int(3)));
    assert!(!is_trivially_true_postcondition(&reflexive));
    assert!(!is_trivially_true_postcondition_under_requires(
        &reflexive,
        &[]
    ));

    // Quantifier wrapping must not launder either shape (the #126 gate's
    // probe family: quantifier-wrapped variants ACCEPTED at 4d809ba).
    let forall_wrapped = forall("i", folded.clone());
    assert!(!is_trivially_true_postcondition_under_requires(
        &forall_wrapped,
        &[]
    ));

    // A requires premise must not license it either.
    assert!(!is_trivially_true_postcondition_under_requires(
        &folded,
        &[ge(final_expr(int(3)), int(0))]
    ));

    // Controls: same-state projections keep folding — the refusal is scoped
    // to `Final`.
    assert!(is_trivially_true_postcondition(&eq(
        PureExpr::Old(Arc::new(int(3))),
        int(3)
    )));
    assert!(is_trivially_true_postcondition(&eq(
        PureExpr::Deref(Arc::new(int(3))),
        int(3)
    )));
}

#[test]
fn binder_erased_prophetic_logic_body_still_trivially_accepts() {
    // Capability control for the #125 refusal: `prophetic_id(5) == 5` with
    // body `^x` stays discharged WITHOUT a solve, because the binder-erasing
    // inlining substitution normalises `^x [x := 5]` to `5` before the
    // evaluators run (the shape the old RESIDUAL fold existed to serve —
    // `test_prophetic_verification_with_final_body`'s layer-local twin).
    let logic_fn = LogicFnDef::new(
        "prophetic_id".to_string(),
        "test::prophetic_id".to_string(),
        vec!["x".to_string()],
        PureExpr::Final(Arc::new(var("x"))),
    )
    .with_mode(LogicMode::Prophetic);

    let ensure = eq(logic_fn_call("prophetic_id", vec![int(5)]), int(5));
    assert!(result_postcondition_matches_return_expr_via_logic_bodies(
        &ensure,
        Some(std::slice::from_ref(&logic_fn)),
        Some(&int(0)),
        &[],
    ));
}

#[test]
fn reflexive_division_requires_nonzero_divisor_fact() {
    let divisor = PureExpr::View(Arc::new(var("y")));
    let body = binop(div(var("x"), divisor.clone()), BinOp::Mul, var("z"));
    let expr = eq(body.clone(), body.clone());

    assert!(
        !is_trivially_true_postcondition(&expr),
        "division should not bypass safety without requirements"
    );
    assert!(
        !is_trivially_true_postcondition_under_requires(&expr, &[]),
        "division should not bypass safety with no divisor fact"
    );
    assert!(is_trivially_true_postcondition_under_requires(
        &expr,
        &[gt(divisor.clone(), int(0))]
    ));

    let ensure = eq(var("result"), body.clone());
    assert!(result_postcondition_matches_return_expr(
        &ensure,
        Some(&body),
        &[gt(divisor, int(0))]
    ));
    assert!(!result_postcondition_matches_return_expr(
        &ensure,
        Some(&body),
        &[]
    ));
}

/// `guard ==> (x == x)` is trivially true (implication with trivially-true consequent).
#[test]
fn trivially_true_guarded_reflexive() {
    let guard_impl_refl = binop(gt(var("x"), int(0)), BinOp::Implies, eq(var("x"), var("x")));
    assert!(is_trivially_true_postcondition(&guard_impl_refl));
}

/// `(x == x) && (y == y)` is trivially true (conjunction of reflexive equalities).
#[test]
fn trivially_true_conjunction_of_reflexive() {
    let both = and(eq(var("x"), var("x")), eq(var("y"), var("y")));
    assert!(is_trivially_true_postcondition(&both));
}

/// `forall<a> a == a` is trivially true (quantifier with trivially-true body).
#[test]
fn trivially_true_forall_reflexive() {
    let forall_refl = PureExpr::Forall {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(eq(var("a"), var("a"))),
        triggers: vec![],
    };
    assert!(is_trivially_true_postcondition(&forall_refl));
}

/// `forall<a> a > 0` is NOT trivially true.
#[test]
fn forall_non_trivial_not_trivially_true() {
    let forall_gt = PureExpr::Forall {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(gt(var("a"), int(0))),
        triggers: vec![],
    };
    assert!(!is_trivially_true_postcondition(&forall_gt));
}

/// Encoding negation of a trivially-true postcondition produces `false`.
/// This verifies the short-circuit in `encode_and_assert_negated_postconditions`.
/// When the only postcondition is `x == x`, the fast path short-circuits it to
/// `bool_const(true)`, then negates to get `false`, which is UNSAT. (#2696)
#[test]
#[timeout(30000)]
fn trivially_true_postcondition_negated_to_false() {
    let ensures = [eq(var("x"), var("x"))]; // x == x is trivially true
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // No need to declare x -- the trivially-true check short-circuits before
    // encoding, so the variable is never touched by the encoder.

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(
        asserted,
        "trivially-true ensures should still report asserted=true"
    );

    // NOT(true) = false. The solver should find this UNSAT.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "negation of trivially-true postcondition should be UNSAT (= Verified). Got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn result_equals_return_expr_via_logic_body_negates_to_false() {
    let body = binop(var("x"), BinOp::Add, int(1));
    let mut logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        body,
    );
    logic_fn.set_mode(LogicMode::Open);
    let logic_fns = [logic_fn];

    let return_expr = binop(var("y"), BinOp::Add, int(1));
    let ensures = [eq(
        var("result"),
        PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![var("y")],
        },
    )];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let asserted = encode_and_assert_negated_postconditions(
        &mut encoder,
        &ensures,
        Some(&logic_fns),
        Some(&return_expr),
    )
    .expect("logic-body self equality should encode");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "result == f(y) should be statically true when f's body is the return expression; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn result_logic_body_match_folds_usize_bits_const() {
    let val = var("val");
    let leading_zeros = method_call(val.clone(), "leading_zeros_logic", vec![]);
    let body = binop(var("USIZE_BITS"), BinOp::Sub, leading_zeros.clone());
    let mut logic_fn = LogicFnDef::new(
        "ffs_logic".to_string(),
        "test::ffs_logic".to_string(),
        vec!["val".to_string()],
        body,
    );
    logic_fn.set_mode(LogicMode::Open);
    let logic_fns = [logic_fn];

    let return_expr = binop(
        int((std::mem::size_of::<usize>() * 8) as i64),
        BinOp::Sub,
        leading_zeros,
    );
    let ensures = [eq(
        var("result"),
        PureExpr::LogicFnCall {
            name: "ffs_logic".to_string(),
            args: vec![val],
        },
    )];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let asserted = encode_and_assert_negated_postconditions(
        &mut encoder,
        &ensures,
        Some(&logic_fns),
        Some(&return_expr),
    )
    .expect("logic-body equality should fold USIZE_BITS");
    assert!(asserted);
    assert!(
        encoder.var_term("USIZE_BITS").is_none(),
        "USIZE_BITS should fold before the postcondition shortcut encodes anything"
    );

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "result == ffs_logic(val) should negate to false after USIZE_BITS normalization; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn result_logic_body_equality_inlines_before_solver_encoding() {
    let body = binop(var("x"), BinOp::Add, int(1));
    let mut logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        body,
    );
    logic_fn.set_mode(LogicMode::Open);
    let logic_fns = [logic_fn];

    let ensures = [eq(
        var("result"),
        PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![var("y")],
        },
    )];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let y_is_two = encoder
        .encode_pure(&eq(var("y"), int(2)))
        .expect("encode y == 2");
    encoder.assert_term(y_is_two);
    let result_is_three = encoder
        .encode_pure(&eq(var("result"), int(3)))
        .expect("encode result == 3");
    encoder.assert_term(result_is_three);

    let asserted =
        encode_and_assert_negated_postconditions(&mut encoder, &ensures, Some(&logic_fns), None)
            .expect("logic-body equality should inline");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "inlined result == y + 1 should verify under y == 2 and result == 3; got {result:?}"
    );
}

/// Mixed trivially-true and non-trivially-true postconditions: the non-trivially-true
/// one dominates the result. The trivially-true one contributes `true` to the
/// conjunction, which is harmless.
#[test]
#[timeout(30000)]
fn mixed_trivial_and_nontrivial_postconditions() {
    // ensures(x == x && result > 0) with result == 5
    let ensures = [eq(var("x"), var("x")), gt(var("result"), int(0))];
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Assert result == 5
    let result_val = encoder
        .encode_pure(&eq(var("result"), int(5)))
        .expect("encode result == 5");
    encoder.assert_term(result_val);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted);

    // NOT(true AND result > 0) with result == 5 should be UNSAT (verified).
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "verified: result > 0 holds when result == 5, trivially-true conjunct doesn't interfere. Got {result:?}"
    );
}

// --- Unconditional Skolemization tests (#2696) ---

/// Mixed universal/non-universal postconditions WITHOUT open logic fns
/// should still encode successfully via the slow path and Skolemize
/// the universal. Previously, Skolemization was gated on
/// `has_open_logic_fns()`, which meant this pattern would fall through
/// to ay-level NOT on the forall. The unconditional Skolemization
/// change (#2696) ensures the Skolem constant `sk_a` is created
/// regardless of logic fn availability.
///
/// This test verifies encoding does not error. The SAT check validates
/// that both the UNSAT postcondition (result==5 satisfies result>0)
/// and the false-by-counterexample universal are handled without
/// crashing or producing ay sort errors.
#[test]
#[timeout(30000)]
fn unconditional_skolemization_encodes_without_error() {
    // Mixed ensures: [forall<a:Int> a > 0, result > 0]
    // The forall is universal, `result > 0` is non-universal → mixed.
    let ensures = vec![
        PureExpr::Forall {
            var: "a".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(gt(var("a"), int(0))),
            triggers: vec![],
        },
        gt(var("result"), int(0)),
    ];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_var = encoder
        .get_or_declare_var("result", ay_dpll::api::Sort::Int)
        .expect("declare result");
    let five = encoder.solver_mut().int_const(5);
    let eq_term = encoder.solver_mut().eq(result_var, five);
    encoder.assert_term(eq_term);

    // No open logic fns: pass None. Should still encode via slow path
    // with unconditional Skolemization.
    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode without open logic fns — unconditional Skolemization");
    assert!(asserted, "non-empty ensures should assert terms");
}

/// An embedded universal nested under a non-universal wrapper should still
/// route to the slow path. This guards the quantifier-selection logic against
/// missing universals that are not top-level `Forall` nodes.
#[test]
#[timeout(30000)]
fn embedded_universal_in_conjunction_uses_slow_path() {
    let guarded_tautology = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(binop(
            ge(var("i"), int(0)),
            BinOp::Implies,
            ge(var("i"), int(0)),
        )),
        triggers: vec![],
    };
    let ensures = vec![and(gt(var("result"), int(0)), guarded_tautology)];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_var = encoder
        .get_or_declare_var("result", ay_dpll::api::Sort::Int)
        .expect("declare result");
    let five = encoder.solver_mut().int_const(5);
    let eq_term = encoder.solver_mut().eq(result_var, five);
    encoder.assert_term(eq_term);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("embedded universal should encode");
    assert!(asserted, "non-empty ensures should assert terms");

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "embedded universal under conjunction should be handled by the slow path; got {result:?}"
    );
}

/// A universal under a selected `match result` arm should be exposed before
/// negation, so the existing top-level universal Skolemization path can produce
/// a ground refutation query.
#[test]
#[timeout(30000)]
fn selected_result_match_arm_universal_is_skolemized_with_unsat_evidence() {
    let none_arm = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(le(var("i"), var("j")), lt(var("j"), var("n"))),
            ne(var("p"), var("p")),
        )),
        triggers: vec![],
    };
    let ensure = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                none_arm,
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("hit".to_string()))),
                },
                ge(var("hit"), var("i")),
            ),
        ],
    );
    let return_expr = logic_fn_call("None", vec![]);

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let range_empty = encoder
        .encode_formula(&ge(var("i"), var("n")))
        .expect("encode range-empty assumption");
    encoder.assert_term(range_empty);

    let asserted =
        encode_and_assert_negated_postconditions(&mut encoder, &[ensure], None, Some(&return_expr))
            .expect("selected match-arm universal should encode");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "selected match-arm universal should be discharged by real UNSAT evidence; got {result:?}"
    );
}

/// A constructor-valued ITE return expression should specialize each selected
/// `match result` arm under its branch condition. This keeps the solver
/// evidence for the branch while exposing a nested universal to Skolemization.
#[test]
#[timeout(30000)]
fn selected_result_match_arm_specializes_ite_return_branches_for_skolemization() {
    let none_arm = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(le(var("i"), var("j")), lt(var("j"), var("n"))),
            ne(var("p"), var("p")),
        )),
        triggers: vec![],
    };
    let ensure = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                none_arm,
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("hit".to_string()))),
                },
                ge(var("hit"), int(0)),
            ),
        ],
    );
    let return_expr = PureExpr::Ite(
        Arc::new(ge(var("i"), var("n"))),
        Arc::new(logic_fn_call("None", vec![])),
        Arc::new(logic_fn_call("Some", vec![int(0)])),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let asserted =
        encode_and_assert_negated_postconditions(&mut encoder, &[ensure], None, Some(&return_expr))
            .expect("selected ITE-backed match arms should encode");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ITE-backed selected match-arm universal should be Skolemized with branch evidence; got {result:?}"
    );
}

/// If one ITE branch is a recursive call or other non-constructor value, the
/// concrete branch should still be specialized instead of giving up on the
/// whole selected-arm path.
#[test]
#[timeout(30000)]
fn selected_result_match_arm_keeps_concrete_ite_branch_with_fallback_sibling() {
    let none_arm = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(le(var("i"), var("j")), lt(var("j"), var("n"))),
            ne(var("p"), var("p")),
        )),
        triggers: vec![],
    };
    let ensure = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                none_arm,
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("hit".to_string()))),
                },
                ge(var("hit"), int(0)),
            ),
        ],
    );
    let range_empty = ge(var("i"), var("n"));
    let return_expr = PureExpr::Ite(
        Arc::new(range_empty.clone()),
        Arc::new(logic_fn_call("None", vec![])),
        Arc::new(var("recursive_result")),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let assumption = encoder
        .encode_formula(&range_empty)
        .expect("range-empty assumption should encode");
    encoder.assert_term(assumption);

    let asserted =
        encode_and_assert_negated_postconditions(&mut encoder, &[ensure], None, Some(&return_expr))
            .expect("selected ITE-backed match arm should encode with fallback sibling");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "concrete ITE branch should be specialized even with a fallback sibling; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn selected_result_option_match_fallback_exposes_universal_arm_negation() {
    let none_arm = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(le(var("i"), var("j")), lt(var("j"), var("n"))),
            ne(var("p"), var("p")),
        )),
        triggers: vec![],
    };
    let ensure = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                none_arm,
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("hit".to_string()))),
                },
                ge(var("hit"), int(0)),
            ),
        ],
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let asserted = encode_and_assert_negated_postconditions(
        &mut encoder,
        &[ensure],
        None,
        Some(&PureExpr::Ite(
            Arc::new(PureExpr::Bool(false)),
            Arc::new(logic_fn_call("Some", vec![int(0)])),
            Arc::new(var("recursive_result")),
        )),
    )
    .expect("fallback Option match negation should encode");
    assert!(asserted);

    assert!(
        encoder
            .solver()
            .assertions()
            .into_iter()
            .all(|assertion| !term_contains_negated_quantifier(&encoder, assertion)),
        "fallback Option match negation should route arm bodies through PureExpr-level negation"
    );
}

/// Route classification should surface the reusable negated-postcondition
/// decision point for mixed and triggerless universal postconditions.
#[test]
fn classify_negated_postcondition_route_matches_quantifier_shape() {
    let mixed_universal = vec![and(
        gt(var("result"), int(0)),
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(ge(var("i"), int(0))),
            triggers: vec![],
        },
    )];
    assert_eq!(
        classify_negated_postcondition_route(&mixed_universal),
        NegatedPostconditionRoute::SlowMixedUniversal
    );

    let triggerless_universal = vec![PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(ge(var("i"), int(0))),
        triggers: vec![],
    }];
    assert_eq!(
        classify_negated_postcondition_route(&triggerless_universal),
        NegatedPostconditionRoute::SlowTriggerlessUniversal
    );

    let fast_path = vec![gt(var("result"), int(0)), ne(var("result"), int(1))];
    assert_eq!(
        classify_negated_postcondition_route(&fast_path),
        NegatedPostconditionRoute::Fast
    );
}

/// Trivially-true postcondition in fast path: when all postconditions
/// are non-quantifier formulas and one is trivially true, the trivially-true
/// clause should be encoded as `true` (identity element in conjunction).
/// The overall VC remains correct: NOT(true AND P) = NOT P.
#[test]
#[timeout(30000)]
fn trivially_true_in_fast_path_conjunction_verified() {
    // ensures: [x == x, result > 0]
    // x == x is trivially true → encoded as `true` (skipping logic fn axioms).
    // result > 0 with result == 5 → verified.
    // NOT(true AND result > 0) = NOT(result > 0) should be UNSAT.
    let ensures = vec![eq(var("x"), var("x")), gt(var("result"), int(0))];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result_var = encoder
        .get_or_declare_var("result", ay_dpll::api::Sort::Int)
        .expect("declare result");
    let five = encoder.solver_mut().int_const(5);
    let eq_term = encoder.solver_mut().eq(result_var, five);
    encoder.assert_term(eq_term);

    let asserted = encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, None)
        .expect("should encode");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "verified: NOT(true AND result>0) with result==5 should be UNSAT. Got {result:?}"
    );
}

// --- encode_and_assert_requires: chained Mapping<_, Bool>::get witness (#5) ---

/// Regression for the second `such_that` witness in
/// `tests/should_succeed/such_that.rs` (issue #5, design
/// `2026-05-19-such-that-strict-pass-residual.md` Gap 1).
///
/// Shape:
/// ```text
///   let mapping   = snapshot!(|x: Int| x + y@);                  // Mapping<Int, Int>
///   let predicate = snapshot!(|x: Int| mapping[x] + 1 == 0);     // Mapping<Int, Bool>
///   let x = snapshot!(such_that(*predicate));                    // Int
///   // driver injects assumption: (*predicate).get(*x)            (Bool)
/// ```
///
/// Before the defensive coercion at the precondition/assumption
/// `assert_term` boundary, encoding `(*predicate).get(witness)` together
/// with the mapping-closure forall axioms panicked ay with
/// `sort mismatch in assert_term: expected Bool, got Int`, because sort
/// inference loses the Bool context through `Deref` + `MethodCall` for
/// the chained `Mapping<Int, Bool>::get` call. The fix coerces via
/// `!= 0` (Bool encoded as 0/1 Int) at `setup::encode_and_assert_requires`
/// before calling `assert_term`. This test asserts that `assert_term` does
/// not panic for this chained-witness shape.
#[test]
#[timeout(30000)]
fn chained_predicate_get_witness_assumption_does_not_panic_5() {
    use crate::{
        tests::helpers::{add, deref, forall_with_sort, neg},
        verify::setup::encode_and_assert_requires,
    };

    // mapping forall axiom: forall<x:Int> mapping.get(x) == x + y_view
    let mapping_get_x = method_call(var("mapping"), "get", vec![var("x")]);
    let mapping_body = add(var("x"), var("y_view"));
    let mapping_forall =
        forall_with_sort("x", ExprSort::Int, eq(mapping_get_x.clone(), mapping_body));

    // predicate forall axiom: forall<x:Int> predicate.get(x) == (mapping.get(x) + 1 == 0)
    // Predicate is Mapping<Int, Bool>, so the equality is between a Bool-valued
    // predicate lookup and a Bool body.
    let predicate_get_x = method_call(var("predicate"), "get", vec![var("x")]);
    let predicate_body = eq(add(mapping_get_x, int(1)), int(0));
    let predicate_forall =
        forall_with_sort("x", ExprSort::Int, eq(predicate_get_x, predicate_body));

    // The chained-witness assumption injected by `such_that::specs::SUCH_THAT`:
    //   (*predicate).get(witness)
    // This is the term that panicked before the fix.
    let chained_witness_assumption =
        method_call(deref(var("predicate")), "get", vec![var("witness")]);

    // The follow-up proof_assert from such_that.rs (line 14):
    //   *x + y@ + 1 == 0  ==>  witness + y_view + 1 == 0
    // Included so the test mirrors the full witness shape, even though the
    // critical assertion is the no-panic property on the chained `.get(...)`.
    let witness_satisfies = eq(add(add(var("witness"), var("y_view")), int(1)), int(0));

    let requires = vec![
        mapping_forall,
        predicate_forall,
        chained_witness_assumption,
        witness_satisfies,
    ];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // The critical property: encoding must not panic with sort mismatch at
    // `encoder.assert_term(...)` even when `encode_pure` returns an Int-sorted
    // term for the chained `(*predicate).get(witness)` assumption.
    let result = encode_and_assert_requires(&mut encoder, &requires);
    assert!(
        result.is_ok(),
        "chained `(*predicate).get(witness)` assumption should encode \
         without panic at the assert_term boundary: {result:?}"
    );

    // Belt-and-suspenders: directly exercise the coerce-then-assert pattern
    // on an Int-sorted term. This pins the behavior of the new defensive
    // coercion: an Int term coerced through `!= 0` becomes Bool and
    // `assert_term` accepts it. Use the negation form `neg(witness)` to
    // produce a fresh Int symbol path.
    let int_witness_term = encoder
        .encode_pure(&neg(var("witness")))
        .expect("encode -witness");
    let coerced = encoder.coerce_bool_operand(int_witness_term);
    // Must not panic: assert_term accepts a Bool sort.
    encoder.assert_term(coerced);
}

// --- BV-absorption shortcut for set-bit obligations (#5) ---

/// Construct the `has_bit` logic function (bits.rs: `bitvec & (1 << bit) != 0`).
///
/// The mode must be `Open` so `logic_fn_body_available_under_requires`
/// returns `true` and inlining fires inside
/// `result_postcondition_matches_return_expr_via_logic_bodies`.
fn make_has_bit_logic_fn() -> LogicFnDef {
    let body = binop(
        binop(
            var("bitvec"),
            BinOp::BitAnd,
            binop(int(1), BinOp::Shl, var("bit")),
        ),
        BinOp::Ne,
        int(0),
    );
    let mut logic_fn = LogicFnDef::new(
        "has_bit".to_string(),
        "has_bit".to_string(),
        vec!["bitvec".to_string(), "bit".to_string()],
        body,
    );
    logic_fn.set_mode(LogicMode::Open);
    logic_fn
}

/// `has_bit(result, bit)` with `result = bitvec | (1 << bit)` should
/// discharge to trivially-true under `0 <= bit < 64`, because BV absorption
/// `(A | M) & M = M` reduces the inlined postcondition to `(1 << bit) != 0`
/// and the shift-in-range check completes the proof. This is the fast-path
/// fix for the `set_bit` slice in `bitvectors/bits.rs`.
#[test]
fn set_bit_postcondition_trivially_true_via_bv_absorption() {
    let ensure = logic_fn_call("has_bit", vec![var("result"), var("bit")]);
    let return_expr = binop(
        var("bitvec"),
        BinOp::BitOr,
        binop(int(1), BinOp::Shl, var("bit")),
    );
    let logic_fns = [make_has_bit_logic_fn()];
    // Requires: `bit.view = bit AND 0 <= bit.view AND bit.view < 64`.
    // The driver materializes the `bit@ < USIZE_BITS@` precondition through
    // `View(...)` wrappers; the trivially-true shortcut must look through
    // those to read the integer bounds.
    let requires = [
        binop(PureExpr::View(Arc::new(var("bit"))), BinOp::Lt, int(64)),
        binop(int(0), BinOp::Le, PureExpr::View(Arc::new(var("bit")))),
    ];
    assert!(
        result_postcondition_matches_return_expr_via_logic_bodies(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &requires,
        ),
        "set_bit-shape postcondition should reduce to true under bit-range requires"
    );
}

/// The same shape WITHOUT the `bit < 64` requires should NOT trivially
/// discharge: `(1 << bit) != 0` only holds when `bit` is in the proof BV
/// width range. Missing the upper bound must keep the slice unverified so
/// the solver path runs.
#[test]
fn set_bit_postcondition_requires_shift_upper_bound() {
    let ensure = logic_fn_call("has_bit", vec![var("result"), var("bit")]);
    let return_expr = binop(
        var("bitvec"),
        BinOp::BitOr,
        binop(int(1), BinOp::Shl, var("bit")),
    );
    let logic_fns = [make_has_bit_logic_fn()];
    let requires_missing_upper = [binop(
        int(0),
        BinOp::Le,
        PureExpr::View(Arc::new(var("bit"))),
    )];
    assert!(
        !result_postcondition_matches_return_expr_via_logic_bodies(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &requires_missing_upper,
        ),
        "without an upper bound on bit the shortcut must not fire"
    );
}

/// The `unset_bit` shape: `!has_bit(result, bit)` with
/// `result = bitvec & !(1 << bit)` reduces (via the `(A & ~M) & M = 0`
/// absorption) to `!(0 != 0)`, which is trivially true without any
/// range requirements on `bit`.
#[test]
fn unset_bit_postcondition_trivially_true_via_complement_absorption() {
    let ensure = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(logic_fn_call("has_bit", vec![var("result"), var("bit")])),
    );
    let return_expr = binop(
        var("bitvec"),
        BinOp::BitAnd,
        PureExpr::UnOp(
            UnOp::BitNot,
            Arc::new(binop(int(1), BinOp::Shl, var("bit"))),
        ),
    );
    let logic_fns = [make_has_bit_logic_fn()];
    assert!(
        result_postcondition_matches_return_expr_via_logic_bodies(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ),
        "unset_bit-shape postcondition should reduce to true via (A & ~M) & M = 0"
    );
}
