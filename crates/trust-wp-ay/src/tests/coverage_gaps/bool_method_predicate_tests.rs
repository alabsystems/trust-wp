// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;

use super::*;

/// Encoding a MethodCall with method "invariant" should produce a
/// Bool-sorted UF. Verify by asserting both p and NOT p are individually
/// satisfiable (proving the UF is Bool-sorted and genuinely unconstrained).
#[test]
#[timeout(30000)]
fn test_invariant_method_encodes_as_bool() {
    let mut encoder = AYEncoder::new();

    let inv_expr = method_call(var("x"), "invariant", vec![]);

    let inv_term = encoder
        .encode_pure(&inv_expr)
        .expect("x.invariant() should encode");

    // Positive direction: inv(x) is satisfiable
    encoder.assert_term(inv_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "x.invariant() asserted should be satisfiable: {result:?}"
    );

    // Negative direction (fresh context): NOT inv(x) is also satisfiable,
    // proving the UF is genuinely unconstrained (not axiomatized to true).
    let mut encoder2 = AYEncoder::new();
    let inv_term2 = encoder2
        .encode_pure(&method_call(var("x"), "invariant", vec![]))
        .expect("x.invariant() should encode (2nd context)");
    let negated = {
        let solver = encoder2.solver_mut();
        solver.not(inv_term2)
    };
    encoder2.assert_term(negated);
    let result2 = encoder2.check_sat();
    assert!(
        matches!(result2, SolveResult::Sat),
        "NOT x.invariant() should be satisfiable (unconstrained UF): {result2:?}"
    );
}

/// Invariant predicate must be Bool-sorted: `inv(x) AND NOT inv(x)` is UNSAT.
/// This is a stronger check than the SAT-only pattern — it proves the term
/// is a proper Boolean expression (contradictions are unsatisfiable).
#[test]
#[timeout(30000)]
fn test_invariant_method_contradiction_unsat() {
    let mut encoder = AYEncoder::new();

    let inv_expr = method_call(var("x"), "invariant", vec![]);

    let inv_term = encoder
        .encode_pure(&inv_expr)
        .expect("x.invariant() should encode");

    // inv(x) AND NOT inv(x) must be UNSAT for any Bool-sorted term
    let contradiction = {
        let solver = encoder.solver_mut();
        let neg = solver.not(inv_term);
        solver.and(inv_term, neg)
    };
    encoder.assert_term(contradiction);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "inv(x) AND NOT inv(x) must be UNSAT (Bool consistency): {result:?}"
    );
}

/// Type-specific invariant method (__trust_wp_invariant_MyStruct) should
/// encode as a distinct UF from the generic "invariant".
#[test]
#[timeout(30000)]
fn test_typed_invariant_method_distinct_from_generic() {
    let mut encoder = AYEncoder::new();

    let generic_inv = method_call(var("x"), "invariant", vec![]);
    let typed_inv = method_call(var("x"), "__trust_wp_invariant_MyStruct", vec![]);

    let generic_term = encoder
        .encode_pure(&generic_inv)
        .expect("x.invariant() should encode");
    let typed_term = encoder
        .encode_pure(&typed_inv)
        .expect("x.__trust_wp_invariant_MyStruct() should encode");

    // Assert generic holds but typed does not — should be SAT
    // because they are distinct UFs
    let both = {
        let solver = encoder.solver_mut();
        let neg_typed = solver.not(typed_term);
        solver.and(generic_term, neg_typed)
    };
    encoder.assert_term(both);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Generic and typed invariant should be independent UFs: {result:?}"
    );
}

/// Encoding "completed" method should produce a Bool-sorted UF.
/// Verify via contradiction: `completed(x) AND NOT completed(x)` is UNSAT.
#[test]
#[timeout(30000)]
fn test_completed_method_encodes_as_bool() {
    let mut encoder = AYEncoder::new();

    let completed_expr = method_call(var("iter"), "completed", vec![]);

    let completed_term = encoder
        .encode_pure(&completed_expr)
        .expect("iter.completed() should encode");

    // completed(iter) AND NOT completed(iter) must be UNSAT (Bool sort)
    let contradiction = {
        let solver = encoder.solver_mut();
        let neg = solver.not(completed_term);
        solver.and(completed_term, neg)
    };
    encoder.assert_term(contradiction);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "completed(x) AND NOT completed(x) must be UNSAT (Bool sort): {result:?}"
    );
}

/// Encoding `public()` should stay on the value-accessor UF lane.
/// The current placeholder encoding models that lane with Int sort until
/// associated-type-aware method returns exist. (#994)
#[test]
#[timeout(30000)]
fn test_public_method_encodes_as_int_value_accessor() {
    let mut encoder = AYEncoder::new();

    let public_expr = method_call(var("inv"), "public", vec![]);

    let public_term = encoder
        .encode_pure(&public_expr)
        .expect("inv.public() should encode");

    assert!(
        encoder.solver().get_sort(public_term) == Sort::Int,
        "public(x) should encode on the value-accessor Int lane, got {:?}",
        encoder.solver().get_sort(public_term)
    );
}
