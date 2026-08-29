// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pins for the assertion-boundary prenex push
//! ([`AYEncoder::prenex_push_assertion`]).
//!
//! ay's quantifier soundness gate distrusts the E-matched instances of a
//! `forall` that is not in top-level conjunctive position, so a guard-wrapped
//! universal `G ⇒ ∀k. B(k)` is discounted wholesale. We assert the logically
//! identical `∀k. (G ⇒ B(k))` instead. These pins fix the three properties that
//! make that safe: the shape really is pushed, the guard really is preserved,
//! and a guard that mentions the binder is really refused. (#quantifier-frontier)

use ay_dpll::api::{SolveResult, Sort, TermKind};

use crate::encoder::AYEncoder;

/// A guard-wrapped universal reaches the solver as a `forall`, not a
/// disjunction — the shape ay's conjunctive-position check accepts.
#[test]
fn guarded_universal_is_asserted_in_prenex_form() {
    let mut encoder = AYEncoder::new();
    let k = encoder.solver.fresh_var("qk", Sort::Int);
    let p = encoder
        .solver
        .declare_fun("p_pin", &[Sort::Int], Sort::Bool);
    let body = encoder.solver.apply(&p, &[k]);
    let fact = encoder.solver.forall_with_triggers(&[k], body, &[&[body]]);
    let guard = encoder.solver.bool_var("g_pin");
    let guarded = encoder.solver.implies(guard, fact);

    let pushed = encoder
        .prenex_push_assertion(guarded)
        .expect("a closed guard over a universal must be pushed");

    assert!(
        matches!(encoder.solver.term_kind(pushed), TermKind::Forall),
        "pushed assertion should be a forall, got {:?}",
        encoder.solver.term_kind(pushed)
    );
}

/// The rewrite is verdict-preserving in both directions: with the guard TRUE the
/// body is available at every ground instance (so `g ∧ ¬p(0)` is UNSAT), and
/// with the guard FALSE nothing is claimed (so `¬g ∧ ¬p(0)` stays SAT). A push
/// that dropped or strengthened the guard would break one of the two.
#[test]
fn pushed_universal_keeps_exactly_the_guarded_content() {
    for guard_holds in [true, false] {
        let mut encoder = AYEncoder::new();
        let k = encoder.solver.fresh_var("qk", Sort::Int);
        let p = encoder
            .solver
            .declare_fun("p_pin", &[Sort::Int], Sort::Bool);
        let body = encoder.solver.apply(&p, &[k]);
        let fact = encoder.solver.forall_with_triggers(&[k], body, &[&[body]]);
        let guard = encoder.solver.bool_var("g_pin");
        let guarded = encoder.solver.implies(guard, fact);
        encoder.assert_term(guarded);

        let zero = encoder.solver.int_const(0);
        let p0 = encoder.solver.apply(&p, &[zero]);
        let not_p0 = encoder.solver.not(p0);
        encoder.assert_term(not_p0);
        let guard_lit = if guard_holds {
            guard
        } else {
            encoder.solver.not(guard)
        };
        encoder.assert_term(guard_lit);

        let result = encoder.check_sat();
        if guard_holds {
            assert!(
                matches!(result, SolveResult::Unsat(_)),
                "guard true: the universal must be usable at 0, got {result:?}"
            );
        } else {
            assert!(
                !matches!(result, SolveResult::Unsat(_)),
                "guard false: the universal must claim nothing, got {result:?}"
            );
        }
    }
}

/// When the guard mentions the binder the two shapes are NOT equivalent, so the
/// rewrite must be refused.
#[test]
fn guard_mentioning_the_binder_is_refused() {
    let mut encoder = AYEncoder::new();
    let k = encoder.solver.fresh_var("qk", Sort::Int);
    let p = encoder
        .solver
        .declare_fun("p_pin", &[Sort::Int], Sort::Bool);
    let body = encoder.solver.apply(&p, &[k]);
    let fact = encoder.solver.forall_with_triggers(&[k], body, &[&[body]]);
    let zero = encoder.solver.int_const(0);
    let guard = encoder.solver.gt(k, zero);
    let guarded = encoder.solver.implies(guard, fact);

    assert!(
        encoder.prenex_push_assertion(guarded).is_none(),
        "a guard mentioning the binder must not be pushed inside it"
    );
}

/// A disjunction carrying TWO universals is refused: pushing one would leave the
/// other in place, which is not the intended normal form.
#[test]
fn two_universals_under_one_disjunction_are_refused() {
    let mut encoder = AYEncoder::new();
    let k = encoder.solver.fresh_var("qk", Sort::Int);
    let p = encoder
        .solver
        .declare_fun("p_pin", &[Sort::Int], Sort::Bool);
    let q = encoder
        .solver
        .declare_fun("q_pin", &[Sort::Int], Sort::Bool);
    let pb = encoder.solver.apply(&p, &[k]);
    let qb = encoder.solver.apply(&q, &[k]);
    let fa = encoder.solver.forall_with_triggers(&[k], pb, &[&[pb]]);
    let fb = encoder.solver.forall_with_triggers(&[k], qb, &[&[qb]]);
    let guard = encoder.solver.bool_var("g_pin");
    let disj = encoder.solver.or_many(&[guard, fa, fb]);

    assert!(
        encoder.prenex_push_assertion(disj).is_none(),
        "a disjunction with two universals must be left alone"
    );
}

/// Ground assertions are untouched — the overwhelmingly common path must not
/// change shape.
#[test]
fn ground_assertion_is_not_rewritten() {
    let mut encoder = AYEncoder::new();
    let g = encoder.solver.bool_var("g_pin");
    let f = encoder.solver.bool_var("f_pin");
    let implication = encoder.solver.implies(g, f);
    assert!(encoder.prenex_push_assertion(implication).is_none());
    assert!(encoder.prenex_push_assertion(g).is_none());
}

/// End-to-end through the real assertion path: `assert_term` — the single
/// funnel every named production assertion passes through
/// (`assert_term_conjuncts` -> `assert_solver_term` -> `try_assert_named`) —
/// must leave a `forall` in the solver's assertion list, not a disjunction.
/// This is the property the corpus census measures. (#quantifier-frontier)
#[test]
fn assert_term_leaves_a_conjunctive_position_forall() {
    let mut encoder = AYEncoder::new();
    let k = encoder.solver.fresh_var("qk", Sort::Int);
    let p = encoder
        .solver
        .declare_fun("p_pin", &[Sort::Int], Sort::Bool);
    let body = encoder.solver.apply(&p, &[k]);
    let fact = encoder.solver.forall_with_triggers(&[k], body, &[&[body]]);
    let guard = encoder.solver.bool_var("g_pin");
    let guarded = encoder.solver.implies(guard, fact);

    let before = encoder.solver.assertions().len();
    encoder.assert_term(guarded);
    let asserted: Vec<_> = encoder.solver.assertions()[before..].to_vec();

    assert_eq!(asserted.len(), 1, "expected exactly one new assertion");
    assert!(
        matches!(encoder.solver.term_kind(asserted[0]), TermKind::Forall),
        "the asserted term must be a forall (conjunctive position), got {:?}",
        encoder.solver.term_kind(asserted[0])
    );
}
