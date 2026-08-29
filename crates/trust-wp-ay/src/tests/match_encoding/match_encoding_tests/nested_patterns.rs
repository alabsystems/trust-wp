// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use trust_wp_core::formula::Pattern;

use super::*;

// =========================================================================
// Nested pattern tests (#710 — Constructor-in-Tuple, Tuple-in-Constructor)
// =========================================================================

/// `Some((a, b))`: Constructor with Tuple inner should bind both a and b.
/// Before #710 fix, this returned empty bindings.
#[test]
#[timeout(30000)]
fn test_encode_match_constructor_with_tuple_inner() {
    let mut encoder = AYEncoder::new();

    // match opt { Some((a, b)) => a + b, None => 0 }
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".into()),
                        Pattern::Binding("b".into()),
                    ]))),
                },
                add(var("a"), var("b")),
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

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Some((a, b)) should encode without error");

    // Semantic: when opt is Some, the result should be
    // get_0(unwrap(opt)) + get_1(unwrap(opt)).
    // Assert is_some AND result != expected → UNSAT.
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let is_some = encoder.solver.datatype_tester("Some", opt);
    let payload = encoder
        .solver
        .datatype_selector("option_some_value", opt, Sort::Int);
    let g0 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .expect("tuple getter 0 should be declared for inner tuple")
        .clone();
    let g1 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_1")
        .expect("tuple getter 1 should be declared for inner tuple")
        .clone();
    let a_val = encoder.solver.apply(&g0, &[payload]);
    let b_val = encoder.solver.apply(&g1, &[payload]);
    let expected = encoder.solver.add(a_val, b_val);
    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(is_some);
    encoder.solver.assert_term(neq);
    assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "Some((a,b)) => a+b should equal get_0(payload)+get_1(payload) when is_some (UNSAT expected)"
        );
}

/// `(Some(x), y)`: Tuple with Constructor sub-pattern should bind both x and y.
/// Before #710 fix, x binding was dropped because Tuple passed datatype=None
/// and Constructor required a datatype for selector lookup.
#[test]
#[timeout(30000)]
fn test_encode_match_tuple_with_constructor_subpattern() {
    let mut encoder = AYEncoder::new();

    // match t { (Some(x), y) => x + y, _ => 0 }
    // Without datatype (tuple context), Constructor uses UF accessor fallback.
    let expr = match_expr(
        var("t"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "Some".into(),
                        inner: Some(Box::new(Pattern::Binding("x".into()))),
                    },
                    Pattern::Binding("y".into()),
                ]),
                add(var("x"), var("y")),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("(Some(x), y) should encode without error");

    // Semantic: when the first arm matches (is_some(get_0(t))),
    // the result should be spec_unwrap(get_0(t)) + get_1(t).
    let t = *encoder.vars_for_test().get("t").unwrap();
    let g0 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .expect("tuple getter 0 should be declared")
        .clone();
    let g1 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_1")
        .expect("tuple getter 1 should be declared")
        .clone();
    let t0 = encoder.solver.apply(&g0, &[t]);
    let t1 = encoder.solver.apply(&g1, &[t]);

    // Constructor inside Tuple uses UF tester/accessor
    let is_some_fn = encoder
        .decls()
        .get_spec_func("is_some")
        .expect("is_some UF tester should be declared for Constructor-in-Tuple")
        .clone();
    let is_some_cond = encoder.solver.apply(&is_some_fn, &[t0]);
    let unwrap_fn = encoder
        .decls()
        .get_spec_func("spec_unwrap")
        .expect("spec_unwrap UF accessor should be declared for Constructor-in-Tuple")
        .clone();
    let x_val = encoder.solver.apply(&unwrap_fn, &[t0]);
    let expected = encoder.solver.add(x_val, t1);

    // When is_some(get_0(t)), match result should equal expected
    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(is_some_cond);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "(Some(x), y) => x+y should bind x via UF accessor (UNSAT expected)"
    );
}

/// `Some(42)`: Constructor with Literal inner should generate condition
/// `is_some(scrutinee) AND option_some_value(scrutinee) == 42`.
/// Before #710 fix, the literal condition was ignored.
#[test]
#[timeout(30000)]
fn test_encode_match_constructor_with_literal_inner() {
    let mut encoder = AYEncoder::new();

    // match opt { Some(42) => true, _ => false }
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                bool_expr(true),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Some(42) should encode without error");

    // Semantic: when opt is Some(42), the first arm matches and result is true.
    // Assert is_some AND payload==42 AND result!=true → UNSAT.
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let is_some = encoder.solver.datatype_tester("Some", opt);
    let payload = encoder
        .solver
        .datatype_selector("option_some_value", opt, Sort::Int);
    let forty_two = encoder.solver.int_const(42);
    let payload_eq_42 = encoder.solver.eq(payload, forty_two);
    let result_true = encoder.solver.bool_const(true);
    let eq = encoder.solver.eq(match_term, result_true);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(is_some);
    encoder.solver.assert_term(payload_eq_42);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When opt is Some(42), match Some(42)=>true should return true (UNSAT expected)"
    );
}

/// Negative case for `Some(42)`: when payload != 42, the first arm should NOT match.
/// The wildcard arm returns false, so result should be false.
#[test]
#[timeout(30000)]
fn test_encode_match_constructor_literal_negative() {
    let mut encoder = AYEncoder::new();

    // match opt { Some(42) => true, _ => false }
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                bool_expr(true),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Some(42) should encode without error");

    // When opt is Some(99), the literal check fails, wildcard matches, result is false.
    // Assert is_some AND payload==99 AND result!=false → UNSAT.
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let is_some = encoder.solver.datatype_tester("Some", opt);
    let payload = encoder
        .solver
        .datatype_selector("option_some_value", opt, Sort::Int);
    let ninety_nine = encoder.solver.int_const(99);
    let payload_eq_99 = encoder.solver.eq(payload, ninety_nine);
    let result_false = encoder.solver.bool_const(false);
    let eq = encoder.solver.eq(match_term, result_false);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(is_some);
    encoder.solver.assert_term(payload_eq_99);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When opt is Some(99), match Some(42)=>true should fall through to false (UNSAT expected)"
    );
}

/// Test: `match result { Some(true) => true, _ => false }` with Bool return_expr. (#1055)
///
/// Models `fn h() -> Option<bool> { Some(true) }` where MIR simplifies
/// return_expr to `Bool(true)`. The encoder must:
/// 1. Detect the Datatype match postcondition
/// 2. Declare `result` as Datatype(OptionInt)
/// 3. Construct `result = Some(ite(true, 1, 0))` for the body assertion
/// 4. Coerce the `true` literal to Int in the pattern condition
/// 5. Not error with sort conflict
#[test]
#[timeout(30000)]
fn test_match_result_option_bool_no_sort_conflict() {
    use crate::verify::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Literal(PureExpr::Bool(true)))),
                },
                body: PureExpr::Bool(true),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Bool(false),
            },
        ],
    }];

    let return_expr = PureExpr::Bool(true);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&return_expr))
            .timeout(Some(std::time::Duration::from_secs(10))),
    );

    // The original bug caused an EncodingError (sort conflict). This must now
    // verify without relying on demotion through Bool-to-Int sort fallback.
    match &result {
        Ok(VerificationResult::Verified(_)) => {}
        other => panic!("Option<bool> match should verify without Unknown demotion: {other:?}"),
    }
}

/// Regression for #1553 cluster 3: if return_expr already encodes to
/// OptionInt (for example `Some(1)`), verify_function must not wrap it as
/// `Some(Some(1))`.
#[test]
#[timeout(30000)]
fn test_match_result_option_body_already_datatype_not_double_wrapped() {
    use crate::verify::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Literal(PureExpr::Int(1)))),
                },
                body: PureExpr::Bool(true),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Bool(false),
            },
        ],
    }];

    // Important: this expression itself is already an Option constructor.
    // #1553 previously double-wrapped this in verify/function.rs.
    let return_expr = PureExpr::LogicFnCall {
        name: "Some".to_string(),
        args: vec![PureExpr::Int(1)],
    };

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&return_expr))
            .timeout(Some(std::time::Duration::from_secs(10))),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Option<Int> constructor body should verify without double-wrapping: {result:?}"
    );
}

/// Regression for #1553 cluster 4: when a match scrutinee has an existing
/// term but no sort metadata, native datatype encoding must be skipped.
#[test]
#[timeout(30000)]
fn test_match_scrutinee_without_sort_metadata_skips_datatype_encoding() {
    let mut encoder = AYEncoder::new();
    let name = "shadow_opt";
    let int_term = encoder.solver.declare_const(name, Sort::Int);
    encoder
        .vars_mut_for_test()
        .insert(name.to_string(), int_term);

    let expr = match_expr(
        var(name),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let _ = encoder
        .encode_pure(&expr)
        .expect("encoding should succeed via UF fallback");
    assert!(
        encoder.decls().datatypes_is_empty(),
        "datatype encoding must be skipped when scrutinee sort metadata is unknown"
    );
}

/// Regression for #994: scoped bindings can carry a native datatype term in
/// `vars` without an entry in `var_sorts`. The match encoder must preserve
/// the native OptionInt path instead of demoting to UF fallback.
#[test]
#[timeout(30000)]
fn test_match_scrutinee_without_sort_metadata_keeps_native_datatype_term() {
    let mut encoder = AYEncoder::new();
    let datatype = SwitchTarget::OptionInt.datatype();
    encoder.ensure_datatype_declared(&datatype);

    let name = "shadow_native_opt";
    let seven = encoder.solver.int_const(7);
    let some_seven = encoder
        .solver
        .datatype_constructor(&datatype, "Some", &[seven]);
    encoder
        .vars_mut_for_test()
        .insert(name.to_string(), some_seven);

    let expr = match_expr(
        var(name),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("native datatype scrutinee should not be demoted to UF fallback");

    let seven_term = encoder.solver.int_const(7);
    let eq = encoder.solver.eq(match_term, seven_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match on a native OptionInt term should preserve Some(7) semantics"
    );
    assert!(
        encoder.is_option_asserted_for_test().is_empty(),
        "native datatype matching should not assert __trust_wp_is_option"
    );
    assert!(
        !encoder.decls().has_spec_func("is_some"),
        "native datatype matching should not declare UF constructor testers"
    );
}

/// Low-level test: directly encode the bug/1504 pattern with ay datatypes.
///
/// Verifies that ay's native datatype theory correctly handles:
/// - result = Some(1) [where 1 represents true]
/// - match result { Some(true) => true, _ => false } evaluates to true
#[test]
#[timeout(30000)]
fn test_match_option_bool_datatype_direct() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Declare result: OptionInt; assert result = Some(1) [true mapped to 1]
    let result_var = encoder
        .get_or_declare_var("result", Sort::Datatype(dt.clone()))
        .unwrap();
    let one = encoder.solver.int_const(1);
    let some_one = encoder.solver.datatype_constructor(&dt, "Some", &[one]);
    let eq = encoder.solver.eq(result_var, some_one);
    encoder.solver.assert_term(eq);

    // Encode the match expression on result
    let match_expr = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Literal(PureExpr::Bool(true)))),
                },
                bool_expr(true),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    );
    let match_term = encoder
        .encode_pure(&match_expr)
        .expect("match encoding should not error");

    // Negate: NOT(match_result) — should be UNSAT
    let neg = encoder.solver.not(match_term);
    encoder.solver.assert_term(neg);
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "result=Some(1) with match Some(true)=>true should be UNSAT, got: {sat_result:?}"
    );
}

/// Pure ay API test: verify datatype theory works without encoder.
///
/// Constructs the same problem manually using raw ay API to isolate
/// whether the SAT result is a ay theory issue or an encoder issue.
#[test]
#[timeout(30000)]
fn test_ay_datatype_theory_raw() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver};

    let mut solver = Solver::try_new(Logic::Uflia).unwrap();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver.declare_datatype(&dt);

    // Declare result: OptionInt
    let result = solver.declare_const("result", Sort::Datatype(dt.clone()));
    // Assert: result = Some(1)
    let one = solver.int_const(1);
    let some_one = solver.datatype_constructor(&dt, "Some", &[one]);
    let eq = solver.eq(result, some_one);
    solver.assert_term(eq);

    // Test 1: just is_Some(result) — should be provably true
    let is_some = solver.datatype_tester("Some", result);
    let not_is_some = solver.not(is_some);
    solver.push();
    solver.assert_term(not_is_some);
    let sat1 = solver.check_sat().into_inner();
    eprintln!("Test 1 - NOT(is_Some(result)): {sat1:?} (expect UNSAT)");
    solver.pop();

    // Test 2: just payload == 1 — should be provably true
    let payload = solver.datatype_selector("option_some_value", result, Sort::Int);
    let payload_eq_1 = solver.eq(payload, one);
    let not_payload_eq = solver.not(payload_eq_1);
    solver.push();
    solver.assert_term(not_payload_eq);
    let sat2 = solver.check_sat().into_inner();
    eprintln!("Test 2 - NOT(payload==1): {sat2:?} (expect UNSAT)");
    solver.pop();

    // Test 3: conjunction NOT(is_Some AND payload == 1)
    let is_some2 = solver.datatype_tester("Some", result);
    let payload2 = solver.datatype_selector("option_some_value", result, Sort::Int);
    let payload_eq_1_2 = solver.eq(payload2, one);
    let conj = solver.and(is_some2, payload_eq_1_2);
    let neg = solver.not(conj);
    solver.push();
    solver.assert_term(neg);
    let sat3 = solver.check_sat().into_inner();
    eprintln!("Test 3 - NOT(is_Some AND payload==1): {sat3:?} (expect UNSAT)");
    solver.pop();

    // Test 4: simple equality check
    let eq_check = solver.eq(result, some_one);
    let not_eq = solver.not(eq_check);
    solver.push();
    solver.assert_term(not_eq);
    let sat4 = solver.check_sat().into_inner();
    eprintln!("Test 4 - NOT(result == Some(1)): {sat4:?} (expect UNSAT)");
    solver.pop();

    // Print all results for diagnosis
    eprintln!("Summary: T1={sat1:?} T2={sat2:?} T3={sat3:?} T4={sat4:?}");
    // At least Test 4 should definitely be UNSAT
    assert!(
        matches!(sat4, ay_dpll::api::SolveResult::Unsat(_)),
        "Pure ay: result=Some(1), NOT(result==Some(1)) should be UNSAT, got: {sat4:?}"
    );
}
