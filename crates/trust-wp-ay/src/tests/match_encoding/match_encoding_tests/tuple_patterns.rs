// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use trust_wp_core::formula::Pattern;

use super::*;

// Pattern::Tuple tests (#592 — zero coverage before this)
// =========================================================================

/// Basic tuple pattern: match t { (a, b) => a + b }
/// Bindings should use tuple getter UFs: __`trust_wp_tuple_get_0`, __`trust_wp_tuple_get_1`.
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_binding() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("t"),
        vec![(
            Pattern::Tuple(vec![
                Pattern::Binding("a".into()),
                Pattern::Binding("b".into()),
            ]),
            add(var("a"), var("b")),
        )],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Should encode match with tuple binding pattern: {result:?}"
    );

    // Tuple getters should be declared as UF spec functions
    assert!(
        encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "Should declare __trust_wp_tuple_get_0 UF"
    );
    assert!(
        encoder.decls().has_spec_func("__trust_wp_tuple_get_1"),
        "Should declare __trust_wp_tuple_get_1 UF"
    );

    // Semantic: match result should equal get_0(t) + get_1(t)
    let match_term = result.unwrap();
    let t = encoder.get_or_declare_var("t", Sort::Int).unwrap();
    let getter_0 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .unwrap()
        .clone();
    let getter_1 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_1")
        .unwrap()
        .clone();
    let t0 = encoder.solver.apply(&getter_0, &[t]);
    let t1 = encoder.solver.apply(&getter_1, &[t]);
    let expected = encoder.solver.add(t0, t1);
    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match t {{ (a,b) => a+b }} should equal get_0(t) + get_1(t) (UNSAT expected)"
    );
}

/// Tuple pattern with literal sub-pattern: match t { (0, b) => b, _ => -1 }
/// The condition for the first arm should be: __`trust_wp_tuple_get_0(t)` == 0.
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_with_literal() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("t"),
        vec![
            (
                Pattern::Tuple(vec![Pattern::Literal(int(0)), Pattern::Binding("b".into())]),
                var("b"),
            ),
            (Pattern::Wildcard, int(-1)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Should encode tuple with literal sub-pattern");

    // Semantic: when tuple_get_0(t) == 0, the first arm matches and
    // the result is b = tuple_get_1(t). Assert this and check UNSAT.
    let t = *encoder.vars_for_test().get("t").unwrap();
    let getter_0 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .expect("tuple getter 0 should be declared")
        .clone();
    let getter_1 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_1")
        .expect("tuple getter 1 should be declared")
        .clone();
    let t0 = encoder.solver.apply(&getter_0, &[t]);
    let t1 = encoder.solver.apply(&getter_1, &[t]);
    let zero = encoder.solver.int_const(0);
    let t0_eq_0 = encoder.solver.eq(t0, zero);
    // When t.0 == 0, match result should equal t.1
    let match_eq_t1 = encoder.solver.eq(match_term, t1);
    let match_neq_t1 = encoder.solver.not(match_eq_t1);
    encoder.solver.assert_term(t0_eq_0);
    encoder.solver.assert_term(match_neq_t1);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When t.0==0, match (0,b)=>b should return t.1 (UNSAT expected)"
    );
}

/// Verify tuple binding semantics via UNSAT check.
/// match t { (a, _) => a } should equal __`trust_wp_tuple_get_0(t)`.
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_binding_semantics() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("t"),
        vec![(
            Pattern::Tuple(vec![Pattern::Binding("a".into()), Pattern::Wildcard]),
            var("a"),
        )],
    );

    let match_term = encoder.encode_pure(&expr).unwrap();

    // Build the expected term: __trust_wp_tuple_get_0(t)
    let t_term = encoder.get_or_declare_var("t", Sort::Int).unwrap();
    let getter = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .expect("tuple getter should be declared")
        .clone();
    let expected = encoder.solver.apply(&getter, &[t_term]);

    // Assert match_term != expected; UNSAT proves they're equal
    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Tuple binding should alias to getter application (expected UNSAT, got {result:?})"
    );
}

/// Tuple with wildcard sub-patterns: match t { (_, _) => 42 }
/// Condition should be trivially true (wildcard always matches).
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_all_wildcards() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("t"),
        vec![(
            Pattern::Tuple(vec![Pattern::Wildcard, Pattern::Wildcard]),
            int(42),
        )],
    );

    let match_term = encoder.encode_pure(&expr).unwrap();

    // All-wildcard tuple should always match, so result == 42
    let expected = encoder.solver.int_const(42);
    let neq = encoder.solver.neq(match_term, expected);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "All-wildcard tuple should match unconditionally (expected UNSAT, got {result:?})"
    );
}

/// 3-element tuple: match t { (a, b, c) => a + b + c }
/// Should declare getters for indices 0, 1, 2.
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_three_elements() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("t"),
        vec![(
            Pattern::Tuple(vec![
                Pattern::Binding("a".into()),
                Pattern::Binding("b".into()),
                Pattern::Binding("c".into()),
            ]),
            add(add(var("a"), var("b")), var("c")),
        )],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Should encode 3-element tuple pattern: {result:?}"
    );

    // Verify all three getters declared
    for i in 0..3 {
        let getter_name = format!("__trust_wp_tuple_get_{i}");
        assert!(
            encoder.decls().has_spec_func(&getter_name),
            "Should declare {getter_name} UF"
        );
    }

    // Semantic: match result should equal get_0(t) + get_1(t) + get_2(t)
    let match_term = result.unwrap();
    let t = encoder.get_or_declare_var("t", Sort::Int).unwrap();
    let g0 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .unwrap()
        .clone();
    let g1 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_1")
        .unwrap()
        .clone();
    let g2 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_2")
        .unwrap()
        .clone();
    let t0 = encoder.solver.apply(&g0, &[t]);
    let t1 = encoder.solver.apply(&g1, &[t]);
    let t2 = encoder.solver.apply(&g2, &[t]);
    let sum_01 = encoder.solver.add(t0, t1);
    let expected = encoder.solver.add(sum_01, t2);
    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match t {{ (a,b,c) => a+b+c }} should equal sum of getters (UNSAT expected)"
    );
}

/// Tuple pattern does not use ADT datatypes — it uses UF getters.
/// Verify no datatypes are declared for tuple matches.
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_no_datatype_declared() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("t"),
        vec![(
            Pattern::Tuple(vec![
                Pattern::Binding("a".into()),
                Pattern::Binding("b".into()),
            ]),
            var("a"),
        )],
    );

    let _ = encoder.encode_pure(&expr).unwrap();
    assert!(
        encoder.decls().datatypes_is_empty(),
        "Tuple patterns should not declare any datatypes, got: {:?}",
        encoder.decls().datatype_names().collect::<Vec<_>>()
    );
}
