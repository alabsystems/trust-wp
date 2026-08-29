// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for expression-structure match arms in `pure_encoding.rs`.
//!
//! These tests target encoding paths that depend on expression structure
//! (LetAssume, LetObligation, Deref/Final collapse, Deref/Final rewriting)
//! rather than sort-sensitive dispatch.
//!
//! Companion to `pure_encoding_sort_sensitive.rs`, which covers sort-dependent
//! match arms (Bool iff, Seq decomposition, sort ratcheting, etc.).
//!
//! Part of #1946 (pure_encoding.rs unit tests).

use super::*;

// ── LetAssume encoding (#815) ────────────────────────────────────────

/// In Bool context, LetAssume encodes as implication: (assumption => body).
///
/// Semantic: `let_assume(x > 0, x > -1)` is logically `(x>0) => (x>-1)`.
/// Since x>0 implies x>-1, the whole formula is a tautology — negation is UNSAT.
#[test]
#[timeout(30000)]
fn let_assume_bool_context_implication_encoding() {
    let mut encoder = AYEncoder::new();

    let expr = let_assume(gt(var("x"), int(0)), gt(var("x"), int(-1)));
    let term = encoder
        .encode_pure(&expr)
        .expect("LetAssume in Bool context should encode");

    // (x>0 => x>-1) is a tautology. NOT(tautology) is UNSAT.
    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(x>0 => x>-1) must be UNSAT — implication is a tautology"
    );
}

/// In Bool context, LetAssume with false assumption is vacuously true.
///
/// Semantic: `let_assume(false, false)` is `false => false` = true.
/// Negation of true is UNSAT.
#[test]
#[timeout(30000)]
fn let_assume_false_assumption_vacuously_true() {
    let mut encoder = AYEncoder::new();

    let expr = let_assume(bool_expr(false), bool_expr(false));
    let term = encoder
        .encode_pure(&expr)
        .expect("LetAssume with false assumption should encode");

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(false => false) must be UNSAT — vacuous implication is true"
    );
}

// ── LetObligation encoding (#815, #1029) ─────────────────────────────

/// In Bool context, LetObligation encodes as conjunction: (obligation AND body).
///
/// Semantic: `let_obligation(x > 0, x < 10)` is `(x>0) AND (x<10)`.
/// With x=5, both are true, so negation is UNSAT.
#[test]
#[timeout(30000)]
fn let_obligation_bool_context_conjunction_encoding() {
    let mut encoder = AYEncoder::new();

    let expr = let_obligation(gt(var("x"), int(0)), lt(var("x"), int(10)));
    let term = encoder
        .encode_pure(&expr)
        .expect("LetObligation in Bool context should encode");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x, five);
    encoder.solver.assert_term(x_eq);

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5, NOT(x>0 AND x<10) must be UNSAT"
    );
}

/// LetObligation with constant-false obligation returns encoding error.
///
/// A constant-false obligation comes from opaque call `requires(false)`.
/// Previously encoded as `false AND true` = false, which was accidentally
/// sound only in the Bool body case. Now returns an encoding error to
/// prevent false proofs regardless of body sort. (#2663)
#[test]
#[timeout(30000)]
fn let_obligation_false_obligation_returns_encoding_error() {
    let mut encoder = AYEncoder::new();

    let expr = let_obligation(bool_expr(false), bool_expr(true));
    let result = encoder.encode_pure(&expr);

    assert!(
        result.is_err(),
        "LetObligation with Bool(false) should return encoding error, got {result:?}"
    );
}

// ── Deref/Final quantifier-bound variable collapse (#717) ────────────

/// *y for quantifier-bound y collapses to the bound variable itself.
///
/// Without collapse, *y would encode to a free `y_current` variable
/// disconnected from the quantifier binding, making the formula vacuously
/// satisfiable. (#717)
///
/// Semantic: `forall y. *y > 0` with collapse means the quantifier actually
/// constrains *y. If we also assert `exists y. *y <= 0`, it should be
/// satisfiable since the forall is falsifiable.
#[test]
#[timeout(30000)]
fn deref_bound_var_collapses_to_quantifier_var() {
    let mut encoder = AYEncoder::new();

    // forall y. *y > 0  (this is a formula the solver tries to falsify)
    let forall_expr = forall("y", gt(deref(var("y")), int(0)));
    let forall_term = encoder
        .encode_pure(&forall_expr)
        .expect("forall y. *y > 0 should encode with deref collapse");

    // Negate: NOT(forall y. *y > 0) means exists y. *y <= 0
    let neg = encoder.solver.not(forall_term);
    encoder.solver.assert_term(neg);

    // This should be SAT — there exists an integer y <= 0
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "NOT(forall y. *y > 0) should be SAT — the deref must collapse to bound var, got {result:?}"
    );

    // Also verify no `y_current` variable was created
    assert!(
        encoder.var_sort("y_current").is_none(),
        "Deref of bound var must not create y_current — must collapse to bound y"
    );
}

/// ^y for quantifier-bound y collapses to the bound variable itself.
///
/// Same principle as Deref collapse: Final(Var(y)) for bound y should
/// return the bound variable term, not create a free `y_final`. (#717)
#[test]
#[timeout(30000)]
fn final_bound_var_collapses_to_quantifier_var() {
    let mut encoder = AYEncoder::new();

    // forall y. ^y > 0
    let forall_expr = forall("y", gt(final_expr(var("y")), int(0)));
    let forall_term = encoder
        .encode_pure(&forall_expr)
        .expect("forall y. ^y > 0 should encode with final collapse");

    // Negate: NOT(forall y. ^y > 0) means exists y. ^y <= 0
    let neg = encoder.solver.not(forall_term);
    encoder.solver.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "NOT(forall y. ^y > 0) should be SAT — the final must collapse to bound var, got {result:?}"
    );

    // Verify no y_final was created
    assert!(
        encoder.var_sort("y_final").is_none(),
        "Final of bound var must not create y_final — must collapse to bound y"
    );
}

// ── Deref rewriting into LogicFnCall (#738) ──────────────────────────

/// *(f(x)) rewrites to f(*x), pushing Deref inside LogicFnCall args.
///
/// This preserves connection to tuple/struct axioms: tuple_get_0(*x)
/// benefits from axiom `tuple_get_0(tuple2(a,b)) = a` when *x is
/// constrained to a tuple value.
///
/// Semantic: declare tuple2, encode `*(tuple_get_0(x))` and
/// `tuple_get_0(*x)`. Both should produce the same term.
#[test]
#[timeout(30000)]
fn deref_logic_fn_call_pushes_deref_into_args() {
    let mut encoder = AYEncoder::new();

    // Encode *(__trust_wp_tuple_get_0(x))
    let deref_fn = deref(logic_fn_call("__trust_wp_tuple_get_0", vec![var("x")]));
    let t1 = encoder
        .encode_pure(&deref_fn)
        .expect("*(f(x)) should encode via Deref rewrite");

    // Encode __trust_wp_tuple_get_0(*x) directly
    let fn_deref = logic_fn_call("__trust_wp_tuple_get_0", vec![deref(var("x"))]);
    let t2 = encoder.encode_pure(&fn_deref).expect("f(*x) should encode");

    // Both must produce the same term
    let neq = encoder.solver.neq(t1, t2);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*(f(x)) must equal f(*x) via Deref rewrite into LogicFnCall args"
    );
}

/// *(expr.method(args)) rewrites to (*expr).method(args). (#738, #780)
///
/// Semantic: `*(x.len())` should be equivalent to `(*x).len()`.
#[test]
#[timeout(30000)]
fn deref_method_call_pushes_deref_into_receiver() {
    let mut encoder = AYEncoder::new();

    // Encode *(x.len())
    let deref_method = deref(method_call(var("x"), "len", vec![]));
    let t1 = encoder
        .encode_pure(&deref_method)
        .expect("*(x.len()) should encode via Deref rewrite");

    // Encode (*x).len() directly
    let method_deref = method_call(deref(var("x")), "len", vec![]);
    let t2 = encoder
        .encode_pure(&method_deref)
        .expect("(*x).len() should encode");

    // Both must produce the same term
    let neq = encoder.solver.neq(t1, t2);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*(x.len()) must equal (*x).len() via Deref rewrite into MethodCall receiver"
    );
}

// ── Deref/Final on literal constants (#1075) ─────────────────────────

/// *5 strips the Deref wrapper: Deref(Int(5)) == Int(5).
///
/// MIR extraction may produce Deref(Int(n)) when a literal participates
/// in reborrow-chain substitution. The encoder strips the wrapper. (#1075)
#[test]
#[timeout(30000)]
fn deref_literal_strips_wrapper() {
    let mut encoder = AYEncoder::new();

    let deref_lit = deref(int(42));
    let t1 = encoder
        .encode_pure(&deref_lit)
        .expect("*42 should encode by stripping Deref");

    let lit = int(42);
    let t2 = encoder.encode_pure(&lit).expect("42 should encode");

    let neq = encoder.solver.neq(t1, t2);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*42 must equal 42 — Deref on literal is identity"
    );
}

/// `^true` REFUSES fail-closed rather than stripping the wrapper. (tract19;
/// was #1075 "Final on literal is identity")
///
/// A literal in wrapper position is what the driver substitutes for a borrowed
/// local whose CURRENT value is a constant, so stripping the wrapper asserts
/// `^p == *p` and hides every mutation through the borrow from the contract.
/// See `tests/coverage_gaps/final_deref_encoding.rs` for the live false-accept
/// reproducer this closed. The `Deref` sibling still strips, and must.
#[test]
#[timeout(30000)]
fn final_literal_refuses_fail_closed() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_pure(&final_expr(bool_expr(true)));
    assert!(
        matches!(result, Err(crate::error::EncodingError::Unsupported { .. })),
        "`^true` must refuse fail-closed, got {result:?}"
    );
}
