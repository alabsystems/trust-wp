// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for witness-based existential elimination and constant body
//! optimization in `encoder/quantifier/pure_quantifier.rs`.
//!
//! Coverage targets:
//! - Witness probe loop: witnesses 0, 1, -1 individually (lines 487-509)
//! - Multi-variable witness substitution (line 491-493)
//! - Guard: forall does NOT use witness elimination (line 483)
//! - Guard: >2 Int vars skips witness elimination (line 484)
//! - Guard: non-Int sort skips witness elimination (line 485)
//! - All witnesses fail → falls through to ay quantifier (line 508-509)
//! - Constant body optimization: forall<x> false = false (lines 451-461)
//! - Constant body optimization: exists<x> false = false (lines 451-461)
//! - Constant body optimization: forall<x> true = true (lines 451-461)
//!
//! These tests verify semantic correctness by checking that eliminated
//! quantifiers produce the expected bool constant terms, and that
//! non-eliminated quantifiers produce valid ay quantifier terms.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

// ── Witness probe: each witness value ─────────────────────────────────

/// Witness value 1 satisfies `exists x. x > 0` → eliminated to true.
///
/// This is the most common witness success path. The type invariant
/// `self > 0` evaluates to true for witness 1.
///
/// Re: #726 — witness-based existential elimination
#[test]
#[timeout(30000)]
fn test_witness_probe_value_1_succeeds() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a type invariant: Positive requires self > 0
    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("Positive", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("Positive");
    let expr = exists("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder.encode_pure(&expr).expect("exists should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists x. x > 0 should witness-eliminate with w=1 → true"
    );
}

/// Witness value 0 satisfies `exists x. x >= 0` → eliminated to true.
///
/// Tests that the witness probe tries 0 before 1, and that the 0 witness
/// can satisfy a non-strict inequality invariant.
///
/// Re: #726 — witness 0 path
#[test]
#[timeout(30000)]
fn test_witness_probe_value_0_succeeds() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register invariant: NonNegative requires self >= 0
    let invariant_body = ge(var("self"), int(0));
    encoder
        .register_type_invariant("NonNegative", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("NonNegative");
    let expr = exists("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder.encode_pure(&expr).expect("exists should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists x. x >= 0 should witness-eliminate with w=0 → true"
    );
}

/// Witness value -1 satisfies `exists x. x < 0` → eliminated to true.
///
/// Tests that the witness probe reaches the -1 witness (third in the loop)
/// when 0 and 1 fail.
///
/// Re: #726 — witness -1 path
#[test]
#[timeout(30000)]
fn test_witness_probe_value_neg1_succeeds() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register invariant: Negative requires self < 0
    let invariant_body = lt(var("self"), int(0));
    encoder
        .register_type_invariant("Negative", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("Negative");
    let expr = exists("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder.encode_pure(&expr).expect("exists should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists x. x < 0 should witness-eliminate with w=-1 → true"
    );
}

// ── All witnesses fail → ay quantifier ────────────────────────────────

/// When no witness (0, 1, -1) satisfies the body, the elimination falls
/// through and creates a ay quantifier term. The resulting term should NOT
/// be bool_const(true) or bool_const(false).
///
/// Re: #726 — witness fallthrough to ay quantifier
#[test]
#[timeout(30000)]
fn test_witness_probe_all_fail_falls_through_to_quantifier() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register invariant: BigPositive requires self > 100
    // None of 0, 1, -1 satisfy self > 100.
    let invariant_body = gt(var("self"), int(100));
    encoder
        .register_type_invariant("BigPositive", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("BigPositive");
    let expr = exists("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder.encode_pure(&expr).expect("exists should encode");

    // The term should NOT be a constant — it should be a real quantifier
    let true_term = encoder.solver.bool_const(true);
    let false_term = encoder.solver.bool_const(false);
    assert!(
        term != true_term && term != false_term,
        "exists x. x > 100 should NOT be witness-eliminated (0, 1, -1 all fail)"
    );
}

// ── Multi-variable witness substitution ───────────────────────────────

/// Multi-variable exists: `exists x, y. x + y == 0` should be eliminated
/// because witness (0, 0) satisfies 0 + 0 == 0 → true.
///
/// The witness loop substitutes the same witness value for ALL variables
/// (not independent values), so witnesses {0, 1, -1} for (x, y) try
/// (0,0), (1,1), (-1,-1).
///
/// Re: #726 — multi-variable witness substitution
#[test]
#[timeout(30000)]
fn test_multi_variable_witness_elimination() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // exists<x, y>. x + y == 0
    // The witness loop substitutes the same value for all variables.
    // (0, 0): 0 + 0 == 0 → true.
    let inner = exists("y", eq(add(var("x"), var("y")), int(0)));
    let expr = exists("x", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("nested exists should encode");

    // x=0, y=0: 0 + 0 == 0 → true. Both variables get witness 0 in the loop.
    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists x, y. x + y == 0 should witness-eliminate with (0, 0)"
    );
}

/// Multi-variable witness where (1, 1) satisfies: `exists x, y. x * y > 0`.
/// (0, 0) fails (0 > 0 is false), (1, 1) succeeds (1 > 0).
///
/// Re: #726 — multi-variable witness value 1
#[test]
#[timeout(30000)]
fn test_multi_variable_witness_value_1() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let inner = exists("y", gt(mul(var("x"), var("y")), int(0)));
    let expr = exists("x", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("nested exists should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists x, y. x * y > 0 should witness-eliminate with (1, 1)"
    );
}

// ── Guard: forall does NOT use witness elimination ────────────────────

/// `forall<x> x > 0` should NOT be witness-eliminated even though witness 1
/// satisfies the body. Forall requires ALL values to satisfy, not just one.
///
/// The forall guard (line 483: `kind == Exists`) prevents witness elimination.
///
/// Re: #726 — forall guard
#[test]
#[timeout(30000)]
fn test_forall_skips_witness_elimination() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("Pos", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("Pos");
    let expr = forall("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder.encode_pure(&expr).expect("forall should encode");

    // forall x. x > 0 is FALSE (e.g., x = -1), so it should NOT be
    // true (which would happen if witness elimination fired for forall).
    assert_ne!(
        term,
        encoder.solver.bool_const(true),
        "forall x. x > 0 must NOT be witness-eliminated to true"
    );
}

// ── Guard: >2 Int vars skips witness ──────────────────────────────────

/// Witness elimination with 2 nested exists variables (the max).
/// `exists x. exists y. x + y == 100` — no single witness value
/// satisfies this (0+0=0, 1+1=2, -1+-1=-2), so both levels fall through.
///
/// Key: inner `exists y. x + y == 100` also fails witness elimination
/// for any substituted x ∈ {0, 1, -1}, because y ∈ {0, 1, -1} cannot
/// produce sums of 100.
///
/// Re: #726 — variable count limit (<=2 is the boundary)
#[test]
#[timeout(30000)]
fn test_two_vars_witness_fails_falls_through() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // exists x. exists y. x + y == 100
    // Outer witnesses: x ∈ {0, 1, -1}
    //   x=0: inner exists y. y == 100 → witnesses 0,1,-1 fail
    //   x=1: inner exists y. y == 99  → witnesses 0,1,-1 fail
    //   x=-1: inner exists y. y == 101 → witnesses 0,1,-1 fail
    let inner = exists("y", eq(add(var("x"), var("y")), int(100)));
    let expr = exists("x", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("2-var exists should encode");

    // All witness pairs fail (same value for all vars), so falls through
    // to ay quantifier. Term should NOT be a bool constant.
    let true_term = encoder.solver.bool_const(true);
    let false_term = encoder.solver.bool_const(false);
    assert!(
        term != true_term && term != false_term,
        "exists x, y. x+y==100 should NOT be witness-eliminated \
         (witnesses 0,1,-1 all fail at both nesting levels)"
    );
}

// ── Guard: non-Int sort skips witness ─────────────────────────────────

/// Exists with a Bool-sorted variable should NOT use witness elimination
/// (guard: all sorts must be Int). Bool variables go through Bool expansion
/// instead.
///
/// Re: #726, #1027 — Bool variables use expansion, not witness
#[test]
#[timeout(30000)]
fn test_bool_sort_skips_witness_uses_expansion() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // exists<b: Bool> b == true
    // Bool sort → goes through Bool expansion (Phase 6), not witness.
    let expr = exists_with_sort(
        "b",
        trust_wp_core::formula::ExprSort::Bool,
        eq(var("b"), bool_expr(true)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool exists should encode");

    // Bool expansion produces: (true == true) OR (false == true)
    // = true OR false = true
    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists<b: Bool> b == true should expand to true via Bool case splitting"
    );
}

// ── Constant body optimization ────────────────────────────────────────

/// `forall<x> true = true` (trivially decidable).
///
/// Re: #1296 — constant body optimization
#[test]
#[timeout(30000)]
fn test_constant_body_forall_true_equals_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = forall("x", bool_expr(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("forall true should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "forall<x> true should optimize to true"
    );
}

/// `forall<x> false = false` (inhabited domain, all elements fail).
///
/// Re: #1296 — constant body optimization, false path
#[test]
#[timeout(30000)]
fn test_constant_body_forall_false_equals_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = forall("x", bool_expr(false));
    let term = encoder
        .encode_pure(&expr)
        .expect("forall false should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(false),
        "forall<x> false should optimize to false (inhabited domain)"
    );
}

/// `exists<x> true = true` (any witness satisfies).
///
/// Re: #1296 — constant body optimization
#[test]
#[timeout(30000)]
fn test_constant_body_exists_true_equals_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = exists("x", bool_expr(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("exists true should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists<x> true should optimize to true"
    );
}

/// `exists<x> false = false` (no witness exists).
///
/// Re: #1296 — constant body optimization, false path
#[test]
#[timeout(30000)]
fn test_constant_body_exists_false_equals_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = exists("x", bool_expr(false));
    let term = encoder
        .encode_pure(&expr)
        .expect("exists false should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(false),
        "exists<x> false should optimize to false (no witness)"
    );
}

// ── Semantic SAT/UNSAT for witness elimination ────────────────────────

/// Witness-eliminated existential (= true) composes with other expressions.
/// Encoding `and(eliminated_exists, x > 5)` after witness elimination should
/// produce a non-false term, demonstrating that the eliminated `true` constant
/// participates correctly in logical conjunction.
///
/// Re: #726 — semantic composability of witness elimination
#[test]
#[timeout(30000)]
fn test_witness_eliminated_existential_composes_in_conjunction() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let invariant_body = ge(var("self"), int(0));
    encoder
        .register_type_invariant("NonNeg", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("NonNeg");
    let exists_expr = exists("y", method_call(var("y"), &method_name, vec![]));
    let exists_term = encoder
        .encode_pure(&exists_expr)
        .expect("exists should encode");

    // The exists was eliminated to true
    let true_term = encoder.solver.bool_const(true);
    assert_eq!(
        exists_term, true_term,
        "exists y. y >= 0 should be witness-eliminated to true"
    );

    // Encoding more expressions after elimination succeeds without error
    let x_gt_5 = encoder.encode_pure(&gt(var("x"), int(5))).unwrap();

    // The eliminated term (true) conjoined with x > 5 should not collapse to false
    let conjunction = encoder.solver.and(exists_term, x_gt_5);
    let false_term = encoder.solver.bool_const(false);
    assert_ne!(
        conjunction, false_term,
        "true AND (x > 5) should not be false"
    );
}

/// After witness elimination, asserting NOT(eliminated) should be UNSAT
/// (it was eliminated to true, so negation is false).
///
/// Re: #726 — negation of witness-eliminated existential
#[test]
#[timeout(30000)]
fn test_negated_witness_eliminated_existential_is_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("Pos2", "self", Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("Pos2");
    let expr = exists("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder.encode_pure(&expr).expect("exists should encode");
    let neg = encoder.solver.not(term);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(witness-eliminated existential) should be UNSAT"
    );
}
