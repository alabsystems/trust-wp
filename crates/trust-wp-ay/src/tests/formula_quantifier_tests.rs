// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `encoder::quantifier::formula_quantifier`.
//!
//! The formula-level quantifier encoding path handles:
//! - Bool expansion (finite domain case splitting for ∀/∃ over Bool)
//! - Sep-logic trigger synthesis (PointsTo domain/permission, MutBorrow current/final/id)
//! - PureExpr trigger synthesis fallback
//! - Trigger budget enforcement (TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT = 2)
//! - Nested quantifier boundary (stops trigger collection at inner ∀/∃)
//!
//! Prior coverage:
//! - Bool expansion: 2 tests in `proof_coverage_1667.rs`
//! - Trigger synthesis merge: 2 tests in `encoder/quantifier/tests.rs`
//! - Formula sort inference: 5+ tests in `quantifier_sort_regressions.rs`
//!
//! This file covers the remaining gaps:
//! - PointsTo location-match trigger extraction (domain + permission)
//! - MutBorrow trigger extraction (current/final mentions)
//! - Nested quantifier boundary halts collection
//! - Trigger budget exhaustion from sep-logic alone
//! - Formula connective traversal for trigger collection
//! - Full encode_formula_quantifier integration for non-Bool quantifiers
//!
//! Part of #2514.

use std::sync::Arc;

use ay_dpll::{api::Sort, SolveResult};
use ntest::timeout;
use trust_wp_core::{formula::Formula, logic::LogicFnDef};

use super::helpers::*;
use crate::encoder::AYEncoder;

// ── PointsTo location-match triggers ─────────────────────────────────

/// When a PointsTo's location matches the quantifier variable, the encoder
/// should extract domain and permission select terms as triggers.
#[test]
#[timeout(30000)]
fn pointsto_matching_location_extracts_domain_trigger() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = points_to("x", int(42));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    // Location match → domain select + permission select = 2 triggers
    assert_eq!(
        patterns.len(),
        2,
        "PointsTo with matching location should extract 2 trigger patterns (domain + permission)"
    );
}

/// When a PointsTo's location does NOT match the quantifier variable,
/// no domain/permission triggers are extracted (value is a literal, not a trigger candidate).
#[test]
#[timeout(30000)]
fn pointsto_nonmatching_location_no_domain_trigger() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = points_to("y", int(42));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert!(
        patterns.is_empty(),
        "PointsTo with non-matching location and literal value should not extract triggers"
    );
}

/// PointsTo value containing a LogicFnCall mentioning the bound variable
/// should extract the value term as a trigger even when location doesn't match.
#[test]
#[timeout(30000)]
fn pointsto_value_logic_fn_trigger() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_def = LogicFnDef::new(
        "f".to_string(),
        "crate::fq::f".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register f logic fn");

    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // PointsTo("slot", f(x)) — location "slot" doesn't match "x", but
    // the value f(x) mentions "x" and is a LogicFnCall (trigger candidate)
    let body = points_to("slot", logic_fn_call("f", vec![var("x")]));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert_eq!(
        patterns.len(),
        1,
        "PointsTo with LogicFnCall value mentioning bound var should extract 1 trigger"
    );
}

// ── MutBorrow trigger extraction ─────────────────────────────────────

/// MutBorrow with current mentioning the bound variable extracts a trigger.
#[test]
#[timeout(30000)]
fn mutborrow_current_mentions_bound_var() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_def = LogicFnDef::new(
        "f".to_string(),
        "crate::fq::f".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register f logic fn");

    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = Formula::MutBorrow {
        var: "b".to_string(),
        current: Arc::new(logic_fn_call("f", vec![var("x")])),
        final_val: Arc::new(int(0)),
        id: Arc::new(int(1)),
    };

    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert_eq!(
        patterns.len(),
        1,
        "MutBorrow with current mentioning bound var should extract 1 trigger"
    );
}

/// MutBorrow with final_val mentioning the bound variable extracts a trigger.
#[test]
#[timeout(30000)]
fn mutborrow_final_mentions_bound_var() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let g_def = LogicFnDef::new(
        "g".to_string(),
        "crate::fq::g".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register g logic fn");

    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = Formula::MutBorrow {
        var: "b".to_string(),
        current: Arc::new(int(0)),
        final_val: Arc::new(logic_fn_call("g", vec![var("x")])),
        id: Arc::new(int(1)),
    };

    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert_eq!(
        patterns.len(),
        1,
        "MutBorrow with final_val mentioning bound var should extract 1 trigger"
    );
}

/// MutBorrow where neither current/final/id mentions the bound var → no triggers.
#[test]
#[timeout(30000)]
fn mutborrow_no_mention_no_trigger() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = Formula::MutBorrow {
        var: "b".to_string(),
        current: Arc::new(int(0)),
        final_val: Arc::new(int(1)),
        id: Arc::new(int(2)),
    };

    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert!(
        patterns.is_empty(),
        "MutBorrow with no mention of bound var should not extract triggers"
    );
}

// ── Nested quantifier boundary ───────────────────────────────────────

/// Trigger collection must NOT descend into nested forall bodies.
/// Variables from inner quantifiers would capture the wrong binder.
#[test]
#[timeout(30000)]
fn nested_forall_boundary_stops_trigger_collection() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Body: forall y. PointsTo("x", 42)
    // The inner forall boundary should prevent trigger collection
    let inner = points_to("x", int(42));
    let body = formula_forall("y", inner);

    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert!(
        patterns.is_empty(),
        "triggers should NOT be collected from inside nested forall body"
    );
}

/// Same boundary applies to nested exists.
#[test]
#[timeout(30000)]
fn nested_exists_boundary_stops_trigger_collection() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let inner = points_to("x", int(42));
    let body = formula_exists("y", inner);

    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert!(
        patterns.is_empty(),
        "triggers should NOT be collected from inside nested exists body"
    );
}

// ── Trigger budget enforcement ───────────────────────────────────────

/// When sep-logic already fills the trigger budget (2 patterns), pure
/// trigger synthesis should not add more.
#[test]
#[timeout(30000)]
fn budget_exhausted_by_sep_logic_blocks_pure_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_def = LogicFnDef::new(
        "f".to_string(),
        "crate::fq::f".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register f logic fn");

    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // PointsTo("x", ...) fills domain + permission = 2 patterns = budget full.
    // Pure(gt(f(x), 0)) would add a trigger, but budget is already at limit.
    let body = Formula::And(
        Arc::new(points_to("x", int(42))),
        Arc::new(pure(gt(logic_fn_call("f", vec![var("x")]), int(0)))),
    );

    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert_eq!(
        patterns.len(),
        2,
        "trigger count should be capped at TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT (2)"
    );
}

// ── Formula connective traversal ─────────────────────────────────────

/// Trigger collection traverses through Or connectives.
#[test]
#[timeout(30000)]
fn trigger_collection_traverses_or() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = formula_or(Formula::True, points_to("x", int(42)));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert_eq!(
        patterns.len(),
        2,
        "trigger collection should traverse Or and find PointsTo triggers"
    );
}

/// Trigger collection traverses through Implies connectives.
#[test]
#[timeout(30000)]
fn trigger_collection_traverses_implies() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = formula_implies(Formula::True, points_to("x", int(42)));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert_eq!(
        patterns.len(),
        2,
        "trigger collection should traverse Implies and find PointsTo triggers"
    );
}

/// Trigger collection traverses through SepConj connectives.
#[test]
#[timeout(30000)]
fn trigger_collection_traverses_sep_conj() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = sep_conj(Formula::True, points_to("x", int(42)));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert!(
        !patterns.is_empty(),
        "trigger collection should traverse SepConj and find PointsTo triggers"
    );
}

/// Trigger collection traverses through MagicWand connectives.
#[test]
#[timeout(30000)]
fn trigger_collection_traverses_magic_wand() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    let body = magic_wand(Formula::True, points_to("x", int(42)));
    let patterns = encoder
        .synthesize_formula_trigger_terms("x", &body)
        .expect("synthesis should succeed");

    assert!(
        !patterns.is_empty(),
        "trigger collection should traverse MagicWand and find PointsTo triggers"
    );
}

// ── Full encode_formula_quantifier integration ───────────────────────

/// Non-Bool forall quantifier encodes successfully with no triggers.
#[test]
#[timeout(30000)]
fn encode_formula_forall_int_no_triggers() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let body = pure(gt(var("x"), int(0)));
    let formula = formula_forall("x", body);

    let result = encoder.encode(&formula);
    assert!(
        result.is_ok(),
        "encoding forall x. (x > 0) should succeed: {:?}",
        result.err()
    );
}

/// Non-Bool exists quantifier encodes successfully.
#[test]
#[timeout(30000)]
fn encode_formula_exists_int_no_triggers() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let body = pure(gt(var("x"), int(0)));
    let formula = formula_exists("x", body);

    let result = encoder.encode(&formula);
    assert!(
        result.is_ok(),
        "encoding exists x. (x > 0) should succeed: {:?}",
        result.err()
    );
}

/// Nested same-kind formula quantifiers should synthesize triggers from the
/// collapsed multi-variable body, not just the outer binder.
///
/// This mirrors the `cell/03_as_slice_of_cells.rs` pattern:
/// `forall<i> forall<x> ... result[i]@[x] == _pred[i][x]`.
#[test]
#[timeout(30000)]
fn encode_formula_nested_forall_uses_collapsed_trigger_synthesis() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "p".to_string(),
        "crate::fq::p".to_string(),
        vec!["i".to_string(), "x".to_string()],
        add(var("i"), var("x")),
    )
    .with_opaque(true);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register opaque logic fn");

    // Ground fact that should contradict the quantified property once the
    // synthesized trigger instantiates the quantified body at (0, 1).
    let ground = eq(logic_fn_call("p", vec![int(0), int(1)]), int(-1));
    let ground_term = encoder.encode_pure(&ground).expect("encode ground fact");
    encoder.assert_term(ground_term);

    let inner = formula_forall(
        "x",
        pure(gt(logic_fn_call("p", vec![var("i"), var("x")]), int(0))),
    );
    let formula = formula_forall("i", inner);
    let quantified_term = encoder
        .encode(&formula)
        .expect("encode nested forall with collapsed synthesis");
    encoder.assert_term(quantified_term);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "nested formula quantifier should be UNSAT with collapsed trigger synthesis"
    );
}

/// Forall over Bool with tautology body (b ∨ ¬b) should be UNSAT when negated.
/// Bool expansion: ∀b. (b ∨ ¬b) → (true ∨ false) ∧ (false ∨ true) = true.
#[test]
#[timeout(30000)]
fn forall_bool_tautology_is_unsat_when_negated() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let b_or_not_b = pure(or(var("b"), not(var("b"))));
    let formula = formula_forall("b", b_or_not_b);

    let forall_term = encoder
        .encode(&formula)
        .expect("encode forall b. (b || !b)");

    let neg = encoder.solver.not(forall_term);
    encoder.solver.assert_term(neg);
    let result = encoder.check_sat();
    assert!(
        !result.is_sat(),
        "negated tautological forall should be UNSAT (Bool expansion)"
    );
}

/// Exists over Bool with unsatisfiable body (b ∧ ¬b) should be UNSAT.
/// Bool expansion: ∃b. (b ∧ ¬b) → (true ∧ false) ∨ (false ∧ true) = false.
#[test]
#[timeout(30000)]
fn exists_bool_contradiction_is_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let b_and_not_b = pure(and(var("b"), not(var("b"))));
    let formula = formula_exists("b", b_and_not_b);

    let exists_term = encoder
        .encode(&formula)
        .expect("encode exists b. (b && !b)");
    encoder.solver.assert_term(exists_term);
    let result = encoder.check_sat();
    assert!(
        !result.is_sat(),
        "contradictory exists should be UNSAT (Bool expansion)"
    );
}
