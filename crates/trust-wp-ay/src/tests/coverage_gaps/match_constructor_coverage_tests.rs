// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use trust_wp_core::formula::Pattern;

use super::*;

/// Build `match opt { Some(v) => v + 1, None => 0 }` expression.
fn some_v_plus_one_match() -> PureExpr {
    match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                add(var("v"), int(1)),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ],
    )
}

/// Match encoding produces a deterministic term: encoding the same match
/// expression twice must yield equal terms (UNSAT for inequality).
///
/// Strengthened from trivial unconstrained SAT check (#1685): previously
/// only asserted the encoding doesn't crash and is SAT, which is trivially
/// true for any well-formed encoding. Now verifies the encoded term is
/// deterministic — a wrong encoding that produced different terms on
/// repeated calls would be caught.
#[test]
#[timeout(30000)]
fn test_match_some_none_encoding_is_deterministic() {
    let mut encoder = AYEncoder::new();
    let match_term_1 = encoder
        .encode_pure(&some_v_plus_one_match())
        .expect("Some/None match should encode");
    let match_term_2 = encoder
        .encode_pure(&some_v_plus_one_match())
        .expect("second encoding should succeed");

    // Determinism: same expression → same term (UNSAT for !=)
    let neq = encoder.solver_mut().neq(match_term_1, match_term_2);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoding the same match expression twice must produce equal terms"
    );
}

/// UNSAT: when opt is None, the None arm returns 0.
/// Assert opt=None AND result!=0 → UNSAT.
#[test]
#[timeout(30000)]
fn test_match_none_arm_returns_zero_unsat() {
    let mut encoder = AYEncoder::new();
    let match_term = encoder
        .encode_pure(&some_v_plus_one_match())
        .expect("match should encode");
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let dt = encoder.decls().get_datatype("OptionInt").unwrap().clone();
    let none = encoder.solver_mut().datatype_constructor(&dt, "None", &[]);
    let opt_eq_none = encoder.solver_mut().eq(opt, none);
    encoder.assert_term(opt_eq_none);
    let zero = encoder.solver_mut().int_const(0);
    let result_eq_0 = encoder.solver_mut().eq(match_term, zero);
    let result_neq_0 = encoder.solver_mut().not(result_eq_0);
    encoder.assert_term(result_neq_0);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "opt=None AND result!=0 should be Unsat (None arm returns 0)"
    );
}

/// Match on None arm returning a value: verify None branch is selected
/// when scrutinee is None.
#[test]
#[timeout(30000)]
fn test_match_none_branch_selected_correctly() {
    let mut encoder = AYEncoder::new();

    // match opt { Some(v) => v, None => 99 }
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
                int(99),
            ),
        ],
    );

    let match_term = encoder.encode_pure(&expr).expect("match should encode");

    // When opt is None, result should be 99
    let opt = *encoder.vars_for_test().get("opt").unwrap();
    let dt = encoder.decls().get_datatype("OptionInt").unwrap().clone();
    let none = encoder.solver_mut().datatype_constructor(&dt, "None", &[]);
    let opt_eq_none = encoder.solver_mut().eq(opt, none);
    encoder.assert_term(opt_eq_none);

    let ninety_nine = encoder.solver_mut().int_const(99);
    let result_eq_99 = encoder.solver_mut().eq(match_term, ninety_nine);
    let result_neq_99 = encoder.solver_mut().not(result_eq_99);
    encoder.assert_term(result_neq_99);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "opt=None AND result!=99 should be Unsat (None branch returns 99)"
    );
}

// --- Sort-conflict UF fallback tests for match encoding (#2026) ---
//
// When a scrutinee is pre-declared as Sort::Int (first-declaration-wins lock-in),
// the match encoder's `scrutinee_has_conflicting_sort` check in
// `match_enc/sort_conflict.rs` nullifies the datatype, forcing the entire
// match to use UF fallback encoding. This is the first line of defense. The
// sort guards in `pattern_condition` are a second safety net for cases where a
// datatype IS passed but the term's ay sort doesn't match. These tests
// exercise the first defense (conflict detection → datatype nullification →
// UF path).

/// Sort-conflict fallback: pre-declared Int scrutinee uses UF encoding.
///
/// When the scrutinee is already declared as Sort::Int (from
/// first-declaration-wins lock-in), `scrutinee_has_conflicting_sort` in
/// `match_enc/sort_conflict.rs` detects the mismatch and nullifies the
/// datatype. The match encodes entirely via the UF fallback path — no
/// OptionInt datatype is declared, no native selectors are attempted. (#2026)
#[test]
#[timeout(30000)]
fn test_sort_guard_int_scrutinee_uses_uf_fallback() {
    let mut encoder = AYEncoder::new();

    // Pre-declare "opt" as Int — simulating first-declaration-wins lock-in.
    encoder
        .get_or_declare_var("opt", ay_dpll::api::Sort::Int)
        .expect("should declare opt as Int");

    // match opt { Some(v) => v + 1, None => 0 }
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                add(var("v"), int(1)),
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

    // Should encode successfully via UF fallback — scrutinee_has_conflicting_sort
    // nullifies the datatype, preventing native Datatype selector attempts.
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "match with Int-sorted scrutinee should encode via UF fallback, got: {result:?}"
    );

    // The UF path for Some uses `spec_unwrap` as the accessor name in
    // `pattern_condition`. The absence of OptionInt in declared_datatypes
    // confirms we took the UF fallback path.
    assert!(
        !encoder.decls().has_datatype("OptionInt"),
        "Int-sorted scrutinee should NOT trigger OptionInt datatype declaration"
    );
}

/// Positive case: undeclared scrutinee uses native Datatype selectors.
///
/// When the scrutinee is NOT pre-declared, `scrutinee_has_conflicting_sort`
/// returns false (no var_sorts entry), the inferred OptionInt datatype is
/// preserved, and the match uses native Datatype encoding. (#2026)
#[test]
#[timeout(30000)]
fn test_sort_guard_correct_datatype_uses_native_selectors() {
    let mut encoder = AYEncoder::new();

    // Don't pre-declare "opt" — let the match encoder declare it as Datatype.
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                add(var("v"), int(1)),
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

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "match with native Datatype scrutinee should encode: {result:?}"
    );

    // The OptionInt datatype should be declared when not locked-in to Int.
    assert!(
        encoder.decls().has_datatype("OptionInt"),
        "native path should declare OptionInt datatype"
    );
}

/// Deref scrutinees should run the same Int-sort conflict guard through their
/// current-name alias (`self_current`) before native datatype encoding. (#2020)
#[test]
#[timeout(30000)]
fn test_sort_guard_deref_int_scrutinee_uses_uf_fallback() {
    let mut encoder = AYEncoder::new();

    encoder
        .get_or_declare_var("self_current", Sort::Int)
        .expect("should declare self_current as Int");

    let expr = match_expr(
        deref(var("self")),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                add(var("v"), int(1)),
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

    let _match_term = encoder
        .encode_pure(&expr)
        .expect("deref match with Int-sorted self_current should use UF fallback");

    assert!(
        matches!(encoder.var_sort("self_current"), Some(Sort::Int)),
        "the derived current-name alias should keep its Int sort when the conflict guard falls back to UFs: {:?}",
        encoder.var_sort("self_current")
    );
    assert!(
        !encoder.decls().has_datatype("OptionInt"),
        "the deref conflict guard should avoid declaring OptionInt on the native path"
    );
}

/// Related predeclarations must still use native datatype encoding.
///
/// A weaker `Uninterpreted("Option")` predeclaration should upgrade to the
/// inferred `OptionInt` datatype instead of forcing the match down the UF
/// fallback path. This mirrors ghost-context postconditions where the driver
/// predeclares a temporary as `Option`, then encodes `match result { Some(..),
/// None => .. }`. (#2209)
#[test]
#[timeout(30000)]
fn test_sort_guard_related_option_predeclaration_upgrades_to_native_datatype() {
    let mut encoder = AYEncoder::new();

    encoder
        .get_or_declare_var(
            "opt",
            ay_dpll::api::Sort::Uninterpreted("Option".to_string()),
        )
        .expect("should declare opt as a weak Option sort");

    let expr = some_v_plus_one_match();
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "related Option predeclaration should still encode natively: {result:?}"
    );

    assert!(
        encoder.decls().has_datatype("OptionInt"),
        "match should still declare OptionInt for a related weak Option sort"
    );
    assert!(
        matches!(encoder.var_sort("opt"), Some(ay_dpll::api::Sort::Datatype(ref dt)) if dt.name == "OptionInt"),
        "opt should upgrade from Uninterpreted(\"Option\") to Datatype(OptionInt)"
    );
}

/// Sort-conflict fallback: Result-like match with Int scrutinee uses UF path.
///
/// Similar to the Option test but with Ok/Err constructors, verifying the
/// conflict detection protects multi-constructor matches as well. (#2026)
#[test]
#[timeout(30000)]
fn test_sort_guard_result_int_scrutinee_uf_fallback() {
    let mut encoder = AYEncoder::new();

    // Pre-declare "res" as Int to trigger conflict detection.
    encoder
        .get_or_declare_var("res", ay_dpll::api::Sort::Int)
        .expect("should declare res as Int");

    // match res { Ok(v) => v, Err(_) => 0 }
    let expr = match_expr(
        var("res"),
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
                    inner: Some(Box::new(Pattern::Binding("e".into()))),
                },
                int(0),
            ),
        ],
    );

    // Should encode successfully — conflict detection redirects to UF path.
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "match with Int-sorted result scrutinee should encode via UF fallback: {result:?}"
    );
}

/// Match with bool literal pattern inside constructor: `Some(true)`.
/// This exercises `try_encode_constructor_equality` which handles
/// Bool-to-Int sort mismatch coercion.
///
/// Strengthened (#1685): now verifies encoding produces a deterministic
/// term by checking that two encodings of the same expression are equal (UNSAT
/// of their inequality).
#[test]
#[timeout(30000)]
fn test_match_constructor_bool_literal_coercion() {
    let mut encoder = AYEncoder::new();

    // match opt { Some(true) => 1, _ => 0 }
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Literal(bool_expr(true)))),
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let term1 = encoder
        .encode_pure(&expr)
        .expect("match with Some(true) literal should encode without error");
    let term2 = encoder
        .encode_pure(&expr)
        .expect("second encoding should succeed");

    // Two encodings of the same match expression must produce the same term.
    // Assert term1 != term2 → UNSAT (functional determinism).
    let neq = encoder.solver.neq(term1, term2);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "two encodings of the same match(Some(true)) must be equal (UNSAT of neq)"
    );
}
