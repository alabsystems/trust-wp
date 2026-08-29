// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// `∀a,b. a ∨ b` is NOT a tautology — it's false when a=false, b=false.
/// With 2-var Bool expansion: (T∨T)∧(T∨F)∧(F∨T)∧(F∨F) = T∧T∧T∧F = false.
/// Asserting it yields Unsat.
#[test]
#[timeout(30000)]
fn test_forall_two_bool_vars_non_tautology_is_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register both vars as Bool via pre-scan
    let hint_a = not(var("a"));
    let hint_b = not(var("b"));
    encoder.register_sort_hints(&[hint_a, hint_b]);

    // ∀a. ∀b. a ∨ b  (nested quantifiers collapsed to multi-var expansion)
    let inner = forall("b", or(var("a"), var("b")));
    let expr = forall("a", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("forall two Bool vars should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "∀a,b. a ∨ b is false (a=F,b=F counterexample) — must be Unsat: got {result:?}"
    );
}

/// `∀a,b. a ∨ ¬a` is a tautology independent of b.
/// With 2-var expansion: all 4 branches yield true. Must be Sat.
#[test]
#[timeout(30000)]
fn test_forall_two_bool_vars_tautology_is_sat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let hint_a = not(var("a"));
    let hint_b = not(var("b"));
    encoder.register_sort_hints(&[hint_a, hint_b]);

    // ∀a. ∀b. a ∨ ¬a (tautology regardless of b)
    let inner = forall("b", or(var("a"), not(var("a"))));
    let expr = forall("a", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("forall two Bool vars tautology should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "∀a,b. a ∨ ¬a is a tautology — must be Sat"
    );
}

/// `∃a,b. a ∧ b` is satisfiable (witness: a=T, b=T).
/// With 2-var expansion: (T∧T)∨(T∧F)∨(F∧T)∨(F∧F) = T∨F∨F∨F = true.
#[test]
#[timeout(30000)]
fn test_exists_two_bool_vars_satisfiable() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let hint_a = not(var("a"));
    let hint_b = not(var("b"));
    encoder.register_sort_hints(&[hint_a, hint_b]);

    // ∃a. ∃b. a ∧ b
    let inner = exists("b", and(var("a"), var("b")));
    let expr = exists("a", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("exists two Bool vars should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "∃a,b. a ∧ b is satisfiable (a=T,b=T) — must be Sat"
    );
}

/// `∃a,b. a ∧ ¬a` is unsatisfiable (contradiction regardless of b).
/// With 2-var expansion: all 4 branches contain a∧¬a which is false.
/// (T∧¬T)∨(T∧¬T)∨(F∧¬F)∨(F∧¬F) = F∨F∨F∨F = false.
#[test]
#[timeout(30000)]
fn test_exists_two_bool_vars_contradiction_is_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let hint_a = not(var("a"));
    let hint_b = not(var("b"));
    encoder.register_sort_hints(&[hint_a, hint_b]);

    // ∃a. ∃b. a ∧ ¬a (contradiction — b is irrelevant)
    let inner = exists("b", and(var("a"), not(var("a"))));
    let expr = exists("a", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("exists two Bool vars contradiction should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "∃a,b. a ∧ ¬a is a contradiction — must be Unsat: got {result:?}"
    );
}

/// `∀a,b. (a → b) → (¬b → ¬a)` is the contrapositive tautology.
/// With 2-var expansion, all 4 branches evaluate to true.
/// This tests that multi-var expansion preserves logical equivalences.
#[test]
#[timeout(30000)]
fn test_forall_two_bool_vars_contrapositive_tautology() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let hint_a = not(var("a"));
    let hint_b = not(var("b"));
    encoder.register_sort_hints(&[hint_a, hint_b]);

    // ∀a. ∀b. (a → b) → (¬b → ¬a)
    let a_implies_b = implies(var("a"), var("b"));
    let not_b_implies_not_a = implies(not(var("b")), not(var("a")));
    let contrapositive = implies(a_implies_b, not_b_implies_not_a);
    let inner = forall("b", contrapositive);
    let expr = forall("a", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("contrapositive tautology should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "∀a,b. (a→b)→(¬b→¬a) is a tautology — must be Sat"
    );

    // UNSAT dual: assert negation. If expansion is correct, ¬(∀a,b. contrapositive) is false.
    let mut encoder2 = AYEncoder::new_pure_with_quantifiers();
    encoder2.register_sort_hints(&[not(var("a")), not(var("b"))]);
    let inner2 = forall(
        "b",
        implies(
            implies(var("a"), var("b")),
            implies(not(var("b")), not(var("a"))),
        ),
    );
    let expr2 = forall("a", inner2);
    let term2 = encoder2
        .encode_pure(&expr2)
        .expect("contrapositive tautology should encode (2)");
    let neg = encoder2.solver_mut().not(term2);
    encoder2.assert_term(neg);

    let result2 = encoder2.check_sat();
    assert!(
        matches!(result2, SolveResult::Unsat(_)),
        "¬(∀a,b. contrapositive) should be Unsat: got {result2:?}"
    );
}

/// Binding restoration test: after multi-var Bool expansion, pre-existing
/// variable bindings must be restored. Verify that encoding a variable
/// that was bound before the quantifier still works.
#[test]
#[timeout(30000)]
fn test_multi_bool_expansion_restores_bindings() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let hint_a = not(var("a"));
    let hint_b = not(var("b"));
    encoder.register_sort_hints(&[hint_a, hint_b]);

    // Pre-bind "x" to a concrete Int value
    let x_val = encoder.solver_mut().int_const(42);
    encoder.vars_mut_for_test().insert("x".to_string(), x_val);

    // Encode ∀a. ∀b. a ∨ ¬a (uses a,b but not x)
    let inner = forall("b", or(var("a"), not(var("a"))));
    let expr = forall("a", inner);
    let _term = encoder.encode_pure(&expr).expect("forall should encode");

    // After expansion, "x" must still be bound to 42
    let x_after = *encoder
        .vars_for_test()
        .get("x")
        .expect("x should still be bound after expansion");
    let forty_two = encoder.solver_mut().int_const(42);
    let eq = encoder.solver_mut().eq(x_after, forty_two);
    encoder.assert_term(eq);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "x should still equal 42 after multi-Bool expansion"
    );
}
