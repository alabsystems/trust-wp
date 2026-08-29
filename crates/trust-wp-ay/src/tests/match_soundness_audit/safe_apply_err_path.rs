// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- safe_apply Err path tests (#2155) ---
//
// After #2155, pattern_condition.rs uses safe_apply for UF tester/accessor
// applications. The Err path fires when the UF function (Int -> ...) is
// applied to a scrutinee with an incompatible sort. Previously this would
// panic; now safe_apply catches it and returns EncodingError.

/// Create a AYEncoder with a Datatype-sorted "dt_val" variable (MySome(42)).
fn encoder_with_datatype_scrutinee() -> AYEncoder {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = DatatypeSort {
        name: "MyOption".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "MySome".to_string(),
                fields: vec![DatatypeField {
                    name: "payload".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "MyNone".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.solver.declare_datatype(&dt);
    let forty_two = encoder.solver.int_const(42);
    let ctor = encoder
        .solver
        .datatype_constructor(&dt, "MySome", &[forty_two]);
    let ctor_sort = encoder.solver.get_sort(ctor);
    encoder
        .vars_mut_for_test()
        .insert("dt_val".to_string(), ctor);
    encoder
        .var_sorts_mut_for_test()
        .insert("dt_val".to_string(), ctor_sort);
    encoder
}

/// `assert_is_option` (datatype_spec.rs:101) uses `solver.apply` (not
/// `safe_apply`), so it panics on Datatype-sorted scrutinee.
///
/// Verify assert_is_option does not panic on Datatype-sorted terms (#2155).
/// After W3-106 sort-aware encoding, Datatype scrutinees get sort-tagged UFs
/// and encoding succeeds rather than erroring.
#[test]
#[timeout(30000)]
fn test_assert_is_option_graceful_error_on_datatype_scrutinee() {
    let mut encoder = encoder_with_datatype_scrutinee();

    // Match dt_val against Some(x)/None — hits UF fallback where
    // assert_is_option calls safe_apply. With sort-aware encoding,
    // the Datatype-sorted scrutinee gets a sort-tagged UF and succeeds.
    let expr = match_expr(
        var("dt_val"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                add(var("x"), int(1)),
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

    // #2155 goal: no panic. With sort-aware encoding, this now succeeds.
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Datatype scrutinee should encode via sort-tagged UF fallback: {result:?}"
    );
}

/// Verify that tuple binding on a non-Int scrutinee uses a sort-aware getter.
#[test]
#[timeout(30000)]
fn test_tuple_pattern_safe_apply_non_int_scrutinee() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Create a scrutinee with Uninterpreted sort (not Int)
    let scrutinee = encoder
        .solver
        .declare_const("tuple_val", Sort::Uninterpreted("Tuple2".to_string()));

    encoder
        .vars_mut_for_test()
        .insert("tuple_val".to_string(), scrutinee);
    encoder.var_sorts_mut_for_test().insert(
        "tuple_val".to_string(),
        Sort::Uninterpreted("Tuple2".to_string()),
    );

    // Match tuple_val against (a, b) => a + b
    let expr = match_expr(
        var("tuple_val"),
        vec![(
            Pattern::Tuple(vec![
                Pattern::Binding("a".to_string()),
                Pattern::Binding("b".to_string()),
            ]),
            add(var("a"), var("b")),
        )],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("tuple bindings on Tuple2 scrutinee should encode");
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "non-Int tuple binding should not reuse bare Int-domain getter"
    );
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_1"),
        "non-Int tuple binding should not reuse bare Int-domain getter"
    );

    assert_sort_aware_tuple_getters(&mut encoder, scrutinee, match_term, "Tuple2");
}

/// Verify sort-aware tuple getters were declared and produce correct results.
fn assert_sort_aware_tuple_getters(
    encoder: &mut AYEncoder,
    scrutinee: Term,
    match_term: Term,
    expected_sort_name: &str,
) {
    use ay_dpll::api::Sort;

    let getter_0_name = tuple_logic_getter_decl_name(encoder, 0);
    let getter_1_name = tuple_logic_getter_decl_name(encoder, 1);

    let getter_0 = encoder
        .decls()
        .get_logic_func(&getter_0_name)
        .unwrap()
        .clone();
    let getter_1 = encoder
        .decls()
        .get_logic_func(&getter_1_name)
        .unwrap()
        .clone();

    let expected_domain = vec![Sort::Uninterpreted(expected_sort_name.to_string())];
    assert_eq!(
        getter_0.domain(),
        expected_domain,
        "getter_0 domain mismatch"
    );
    assert_eq!(
        getter_1.domain(),
        expected_domain,
        "getter_1 domain mismatch"
    );

    let t0 = encoder.solver.apply(&getter_0, &[scrutinee]);
    let t1 = encoder.solver.apply(&getter_1, &[scrutinee]);
    let expected = encoder.solver.add(t0, t1);
    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match (a, b) => a + b should equal sort-aware getters on {expected_sort_name} scrutinee"
    );
}
