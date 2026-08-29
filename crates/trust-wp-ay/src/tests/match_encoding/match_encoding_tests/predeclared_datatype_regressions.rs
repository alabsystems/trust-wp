// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use trust_wp_core::formula::Pattern;

use super::*;

/// Regression for #1763: match over a pre-declared user-defined datatype
/// where both constructors have fields.
///
/// When a variable is already declared with `Sort::Datatype(EitherInt)` using
/// custom field names (e.g., `either_left_value`), the match encoder's
/// auto-inferred datatype has different field names (e.g., `eitherint_left_0`).
/// `scrutinee_has_conflicting_sort` detects this difference and previously
/// cleared the datatype to `None`, causing the UF fallback path to apply an
/// `Int -> Int` accessor to a Datatype-sorted scrutinee — a sort mismatch.
///
/// Fix: when the scrutinee already has a Datatype sort, use the existing
/// DatatypeSort instead of clearing to `None`.
#[test]
#[timeout(30000)]
fn test_match_predeclared_user_defined_datatype_both_ctors_have_fields() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult};

    let mut encoder = AYEncoder::new();

    // Pre-declare EitherInt with custom field names (as the upstream
    // pipeline would when encoding constructor calls earlier).
    let dt = DatatypeSort {
        name: "EitherInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Left".to_string(),
                fields: vec![DatatypeField {
                    name: "either_left_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Right".to_string(),
                fields: vec![DatatypeField {
                    name: "either_right_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Declare the scrutinee variable with the pre-declared datatype sort.
    encoder
        .get_or_declare_var("e", Sort::Datatype(dt.clone()))
        .expect("should declare e as EitherInt");

    // Encode: match e { Left(v) => v, Right(w) => w }
    let expr = match_expr(
        var("e"),
        vec![
            (
                Pattern::Constructor {
                    name: "Left".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "Right".into(),
                    inner: Some(Box::new(Pattern::Binding("w".into()))),
                },
                var("w"),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("match over pre-declared EitherInt should encode without sort mismatch");

    // Semantic: when e is Left(42), result should be 42.
    let e = *encoder.vars_for_test().get("e").unwrap();
    let forty_two = encoder.solver.int_const(42);
    let left_42 = encoder
        .solver
        .datatype_constructor(&dt, "Left", &[forty_two]);
    let e_eq_left = encoder.solver.eq(e, left_42);
    let match_eq_42 = encoder.solver.eq(match_term, forty_two);
    let match_neq_42 = encoder.solver.not(match_eq_42);
    encoder.solver.assert_term(e_eq_left);
    encoder.solver.assert_term(match_neq_42);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When e is Left(42), match should return 42 (UNSAT expected)"
    );
}

/// Regression for #1763: verify that the Right arm also works correctly
/// when encoding a match over a pre-declared user-defined datatype.
#[test]
#[timeout(30000)]
fn test_match_predeclared_datatype_right_arm_semantic() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "EitherInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Left".to_string(),
                fields: vec![DatatypeField {
                    name: "either_left_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Right".to_string(),
                fields: vec![DatatypeField {
                    name: "either_right_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("e", Sort::Datatype(dt.clone()))
        .expect("declare e");

    // match e { Left(v) => v + 1, Right(w) => w }
    let expr = match_expr(
        var("e"),
        vec![
            (
                Pattern::Constructor {
                    name: "Left".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                add(var("v"), int(1)),
            ),
            (
                Pattern::Constructor {
                    name: "Right".into(),
                    inner: Some(Box::new(Pattern::Binding("w".into()))),
                },
                var("w"),
            ),
        ],
    );

    let match_term = encoder.encode_pure(&expr).expect("encoding should succeed");

    // When e is Right(99), result should be 99.
    let e = *encoder.vars_for_test().get("e").unwrap();
    let ninety_nine = encoder.solver.int_const(99);
    let right_99 = encoder
        .solver
        .datatype_constructor(&dt, "Right", &[ninety_nine]);
    let e_eq_right = encoder.solver.eq(e, right_99);
    let match_eq_99 = encoder.solver.eq(match_term, ninety_nine);
    let match_neq_99 = encoder.solver.not(match_eq_99);
    encoder.solver.assert_term(e_eq_right);
    encoder.solver.assert_term(match_neq_99);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When e is Right(99), match should return 99 (UNSAT expected)"
    );
}

/// Regression for #2020: old-prefixed match encoding should reuse the
/// authoritative datatype sort already registered for the base scrutinee
/// instead of synthesizing a fresh `Adt_*` datatype from constructor names.
#[test]
#[timeout(30000)]
fn test_old_prefixed_match_reuses_predeclared_datatype_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "EitherInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Left".to_string(),
                fields: vec![DatatypeField {
                    name: "either_left_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Right".to_string(),
                fields: vec![DatatypeField {
                    name: "either_right_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("e", Sort::Datatype(dt.clone()))
        .expect("declare e");

    let expr = old(match_expr(
        var("e"),
        vec![
            (
                Pattern::Constructor {
                    name: "Left".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "Right".into(),
                    inner: Some(Box::new(Pattern::Binding("w".into()))),
                },
                var("w"),
            ),
        ],
    ));

    let match_term = encoder
        .encode_pure(&expr)
        .expect("old-prefixed match over a predeclared datatype should encode");

    assert!(
        matches!(encoder.var_sort("old_e"), Some(Sort::Datatype(existing)) if existing.name == dt.name),
        "old-prefixed match scrutinees should reuse the authoritative base datatype sort: {:?}",
        encoder.var_sort("old_e")
    );
    assert!(
            encoder.decls().get_datatype("Adt_Left_Right").is_none(),
            "old-prefixed match should not synthesize a replacement datatype when the base sort is already declared"
        );
    assert!(
        matches!(encoder.solver.get_sort(match_term), Sort::Int),
        "old-prefixed datatype match should still encode an Int-typed body result"
    );
}

/// Regression for #2020: the native match datatype preflight must honor
/// the outer `old_` prefix for derived `_current` scrutinee names.
///
/// Without the prefix-aware lookup, `old(match *e { ... })` ignored the
/// authoritative `old_e_current` datatype registration, synthesized
/// `Adt_Left_Right`, and declared the scrutinee under the wrong sort before
/// payload selector encoding began.
#[test]
#[timeout(30000)]
fn test_old_deref_match_reuses_prefixed_current_datatype_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "EitherInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Left".to_string(),
                fields: vec![DatatypeField {
                    name: "either_left_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Right".to_string(),
                fields: vec![DatatypeField {
                    name: "either_right_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("old_e_current", Sort::Datatype(dt.clone()))
        .expect("declare old_e_current");

    let expr = old(match_expr(
        deref(var("e")),
        vec![
            (
                Pattern::Constructor {
                    name: "Left".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "Right".into(),
                    inner: Some(Box::new(Pattern::Binding("w".into()))),
                },
                var("w"),
            ),
        ],
    ));

    let match_term = encoder
        .encode_pure(&expr)
        .expect("old-prefixed deref match over a predeclared datatype should encode");

    assert!(
        matches!(encoder.var_sort("old_e_current"), Some(Sort::Datatype(existing)) if existing.name == dt.name),
        "old-prefixed deref scrutinees should reuse the authoritative current datatype sort: {:?}",
        encoder.var_sort("old_e_current")
    );
    assert!(
            encoder.decls().get_datatype("Adt_Left_Right").is_none(),
            "old-prefixed deref match should not synthesize a replacement datatype when the prefixed current sort is already declared"
        );
    assert!(
        matches!(encoder.solver.get_sort(match_term), Sort::Int),
        "old-prefixed deref datatype match should still encode an Int-typed body result"
    );
}
