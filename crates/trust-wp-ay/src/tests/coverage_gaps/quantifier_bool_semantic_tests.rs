// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Semantic companion for `test_encode_forall_bool_bound_variable`.
///
/// `∀b. ¬b` is logically false (b=true is a counterexample). With Bool
/// expansion (#1027), this becomes `¬true ∧ ¬false` = `false`, so
/// asserting it yields Unsat.
#[test]
#[timeout(30000)]
fn test_forall_bool_bound_semantic_not_sat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register "b" as Bool via pre-scan
    let body = not(var("b"));
    encoder.register_sort_hints(std::slice::from_ref(&body));

    // Assert: ∀b. ¬b
    let forall_expr = forall("b", not(var("b")));
    let forall_term = encoder
        .encode_pure(&forall_expr)
        .expect("forall Bool should encode");
    encoder.assert_term(forall_term);

    // With Bool expansion (#1027), ∀b. ¬b becomes ¬true ∧ ¬false = false.
    // Asserting false makes context Unsat.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "∀b. ¬b is false — must be Unsat after Bool expansion: got {result:?}"
    );
}

/// Semantic companion for `test_encode_exists_bool_bound_variable`.
///
/// `∃b. b == true` is satisfiable (witness: b=true). With Bool
/// quantifier expansion (#1027), this becomes `(true == true) ∨
/// (false == true)` which is trivially Sat.
#[test]
#[timeout(30000)]
fn test_exists_bool_bound_semantic_not_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register "b" as Bool via pre-scan
    let body = eq(var("b"), bool_expr(true));
    encoder.register_sort_hints(std::slice::from_ref(&body));

    // Assert: ∃b. b == true
    let exists_expr = exists("b", eq(var("b"), bool_expr(true)));
    let exists_term = encoder
        .encode_pure(&exists_expr)
        .expect("exists Bool should encode");
    encoder.assert_term(exists_term);

    // With Bool expansion (#1027), ∃b. b == true becomes
    // (true == true) ∨ (false == true) = true. Must be Sat.
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "∃b. b == true must be Sat after Bool expansion"
    );
}

/// Semantic companion: `∀b. b ∨ ¬b` (tautology) should be Sat.
///
/// With Bool expansion (#1027), this becomes `(true ∨ ¬true) ∧
/// (false ∨ ¬false)` = `true ∧ true` = `true`. Must be Sat.
#[test]
#[timeout(30000)]
fn test_forall_bool_tautology_not_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register "b" as Bool via pre-scan (Not forces Bool context)
    let hint = not(var("b"));
    encoder.register_sort_hints(std::slice::from_ref(&hint));

    // Assert: ∀b. b ∨ ¬b (tautology — always true)
    let forall_expr = forall("b", or(var("b"), not(var("b"))));
    let forall_term = encoder
        .encode_pure(&forall_expr)
        .expect("forall Bool tautology should encode");
    encoder.assert_term(forall_term);

    // With Bool expansion (#1027), this reduces to true ∧ true. Must be Sat.
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "∀b. b ∨ ¬b must be Sat after Bool expansion"
    );
}
