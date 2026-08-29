// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use super::*;
#[test]
#[timeout(30000)]
fn test_encode_match_literal_pattern() {
    // match x { 0 => false, _ => true }
    // Should encode as: ite(x == 0, false, true)
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("x"),
        vec![
            (Pattern::Literal(int(0)), bool_expr(false)),
            (Pattern::Wildcard, bool_expr(true)),
        ],
    );

    let match_term = encoder.encode_pure(&expr).unwrap();

    // Semantic: when x=0, result is false (literal arm matches)
    let x = *encoder.vars_for_test().get("x").unwrap();
    let zero = encoder.solver.int_const(0);
    let x_eq_0 = encoder.solver.eq(x, zero);
    let result_false = encoder.solver.bool_const(false);
    let match_eq_false = encoder.solver.eq(match_term, result_false);
    // x==0 => match==false; negate to check: x==0 AND match!=false should be UNSAT
    let match_neq_false = encoder.solver.not(match_eq_false);
    encoder.solver.assert_term(x_eq_0);
    encoder.solver.assert_term(match_neq_false);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When x=0, match result should be false (UNSAT expected)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_wildcard_only() {
    // match x { _ => 42 }
    // Should just return 42 (wildcard is always true, only one arm)
    let mut encoder = AYEncoder::new();

    let expr = match_expr(var("x"), vec![(Pattern::Wildcard, int(42))]);

    let match_term = encoder.encode_pure(&expr).unwrap();

    // Semantic: result is always 42 regardless of x; assert result != 42 → UNSAT
    let forty_two = encoder.solver.int_const(42);
    let eq = encoder.solver.eq(match_term, forty_two);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Wildcard match should always return 42 (UNSAT expected)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_binding_pattern() {
    // match x { y => y + 1 }
    // Should encode as: x + 1 (binding introduces alias)
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("x"),
        vec![(Pattern::Binding("y".into()), add(var("y"), int(1)))],
    );

    let match_term = encoder.encode_pure(&expr).unwrap();

    let expected = add(var("x"), int(1));
    let expected_term = encoder.encode_pure(&expected).unwrap();

    // Assert inequality; UNSAT proves binding aliasing semantics.
    let eq = encoder.solver.eq(match_term, expected_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Binding pattern should alias body variable to scrutinee (expected UNSAT, got {result:?})"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_some_pattern() {
    // match opt { Some(v) => true, None => false }
    // Should encode as: ite((is Some) opt, true, false)
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                bool_expr(false),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Should encode match with Some/None");

    // Semantic: when opt is Some, result should be true.
    // Assert (is Some opt) AND match_result != true → UNSAT
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let is_some = encoder.solver.datatype_tester("Some", opt);
    let result_true = encoder.solver.bool_const(true);
    let match_eq_true = encoder.solver.eq(match_term, result_true);
    let match_neq_true = encoder.solver.not(match_eq_true);
    encoder.solver.assert_term(is_some);
    encoder.solver.assert_term(match_neq_true);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When opt is Some, match should return true (UNSAT expected)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_none_pattern() {
    // match opt { None => 0, _ => 1 }
    // Now encoded as: ite(opt == None(), 0, 1)
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
            (Pattern::Wildcard, int(1)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Should encode match with None pattern");

    // Semantic: when opt is None(), result should be 0.
    // Assert opt == None() AND match_result != 0 → UNSAT
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let dt = encoder.decls().get_datatype("OptionInt").unwrap().clone();
    let none_term = encoder.solver.datatype_constructor(&dt, "None", &[]);
    let opt_eq_none = encoder.solver.eq(opt, none_term);
    encoder.solver.assert_term(opt_eq_none);
    let zero = encoder.solver.int_const(0);
    let match_eq_0 = encoder.solver.eq(match_term, zero);
    let match_neq_0 = encoder.solver.not(match_eq_0);
    encoder.solver.assert_term(match_neq_0);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When opt is None, match should return 0 (UNSAT expected)"
    );
}

/// Ordinary match encoding may materialize a generic Seq bridge while encoding
/// an inactive `None => x.len() == 0` arm, but it must not seed a concrete
/// len-zero fact for `x_view`; arm-specific facts belong in the
/// selected-arm/postcondition paths.
#[test]
#[timeout(30000)]
fn test_encode_match_none_branch_does_not_synthesize_global_len_zero_seq_value() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                eq(method_call(view(var("x")), "len", vec![]), int(0)),
            ),
        ],
    );

    let _ = encoder
        .encode_pure(&expr)
        .expect("match encoding should succeed");

    if let Some(x_view_term) = encoder.var_term("x_view") {
        let seq_value = encoder
            .seq_state_for_test()
            .get_seq_value(&x_view_term)
            .expect("x_view should have the generic Seq bridge created by len encoding");
        assert_ne!(
            seq_value.known_len,
            Some(0),
            "inactive None branch len-zero should not seed a concrete empty SeqValue for x_view"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_encode_match_custom_constructor() {
    // match result { Ok(v) => v, Err(_) => 0 }
    // Should encode with datatype testers for Ok/Err
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "Err".into(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                int(0),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Should encode match with Ok/Err constructors");

    // Semantic: when result is not Ok, the ITE default branch returns 0.
    // Assert NOT(is_ok(result)) AND match_result != 0 → UNSAT.
    //
    // Uses negated is_ok rather than is_err because the ITE condition is
    // is_ok; ay's datatype theory may not derive is_err ↔ ¬is_ok without
    // additional cross-tester reasoning (tracked upstream in ay).
    let result_var = *encoder.vars_for_test().get("result").unwrap();
    let is_ok = encoder.solver.datatype_tester("Ok", result_var);
    let not_ok = encoder.solver.not(is_ok);
    let zero = encoder.solver.int_const(0);
    let match_eq_0 = encoder.solver.eq(match_term, zero);
    let match_neq_0 = encoder.solver.not(match_eq_0);
    encoder.solver.assert_term(not_ok);
    encoder.solver.assert_term(match_neq_0);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When result is not Ok, match should return 0 (UNSAT expected)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_empty_arms() {
    // match x { } (no arms) should return false
    let mut encoder = AYEncoder::new();

    let expr = match_expr(var("x"), vec![]);

    let match_term = encoder.encode_pure(&expr).unwrap();

    // Semantic: empty match returns false; assert it's true → UNSAT
    encoder.solver.assert_term(match_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Empty match should encode as false (UNSAT expected)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_option_uses_declared_datatype() {
    // Verify Option-pattern matches use native datatype declarations.
    let mut encoder = AYEncoder::new();

    let expr1 = match_expr(
        var("x"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: None,
                },
                bool_expr(true),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    );

    let expr2 = match_expr(
        var("y"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: None,
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    // Encode both expressions
    let _r1 = encoder.encode_pure(&expr1).unwrap();
    let _r2 = encoder.encode_pure(&expr2).unwrap();

    // OptionInt should be declared once and no UF fallback tester needed.
    assert_eq!(
        encoder.decls().datatype_count(),
        1,
        "Should declare one OptionInt datatype"
    );
    assert!(
        encoder.decls().has_datatype("OptionInt"),
        "Should declare OptionInt datatype"
    );
    assert!(
        encoder.decls().spec_funcs_is_empty(),
        "Option/Result constructors should not use UF tester fallback"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_constructor_binding_uses_selector() {
    // match opt { Some(v) => v, None => 0 } should bind v via selector, not fresh const.
    let mut encoder = AYEncoder::new();
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let _ = encoder.encode_pure(&expr).unwrap();
    let var_names = encoder.var_names();
    assert!(
        !var_names.iter().any(|name| name == "v"),
        "Constructor payload binding should not introduce fresh variable 'v'"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_option_and_result_bindings_do_not_conflict() {
    // Regression test for selector symbol collisions across datatype families.
    // Ensure we can encode Option and Result payload bindings repeatedly in one solver.
    let mut encoder = AYEncoder::new();

    let option_match = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let result_match = match_expr(
        var("res"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".into(),
                    inner: Some(Box::new(Pattern::Binding("w".into()))),
                },
                var("w"),
            ),
            (
                Pattern::Constructor {
                    name: "Err".into(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                int(0),
            ),
        ],
    );

    let option_match_again = match_expr(
        var("opt2"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v2".into()))),
                },
                var("v2"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    encoder.encode_pure(&option_match).unwrap();
    encoder.encode_pure(&result_match).unwrap();
    let encoded = encoder.encode_pure(&option_match_again);
    assert!(
            encoded.is_ok(),
            "Option payload selector should remain usable after Result selector declaration: {encoded:?}"
        );
    assert_eq!(
        encoder.decls().datatype_count(),
        2,
        "Both OptionInt and ResultIntInt should be declared exactly once"
    );
    assert!(
        encoder.decls().has_datatype("OptionInt"),
        "OptionInt datatype should stay registered after mixed-family encoding"
    );
    assert!(
        encoder.decls().has_datatype("ResultIntInt"),
        "ResultIntInt datatype should stay registered after mixed-family encoding"
    );
    assert!(
        encoder.decls().spec_funcs_is_empty(),
        "Option/Result constructors should remain on datatype tester path"
    );
    let names = encoder.var_names();
    assert!(
        !names
            .iter()
            .any(|name| matches!(name.as_str(), "v" | "w" | "v2")),
        "Constructor payload bindings should not leak fresh binding variables"
    );
}

/// Regression test for #2670: Deref(LogicFnCall) scrutinees must trigger
/// datatype inference. This pattern arises when postcondition substitution
/// replaces `self` with a concrete constructor (e.g., `None()`) inside
/// `match *self { ... }`, producing `match *None() { ... }`.
#[test]
#[timeout(30000)]
fn test_encode_match_deref_constructor_scrutinee() {
    let mut encoder = AYEncoder::new();
    let scrutinee = deref(logic_fn_call("None", vec![]));
    let expr = match_expr(
        scrutinee,
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(42),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Deref(Constructor) scrutinee should encode successfully");
    let forty_two = encoder.solver.int_const(42);
    let eq = encoder.solver.eq(match_term, forty_two);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match *None() {{ Some(v) => v, None => 42 }} should evaluate to 42 (UNSAT expected)"
    );
}
