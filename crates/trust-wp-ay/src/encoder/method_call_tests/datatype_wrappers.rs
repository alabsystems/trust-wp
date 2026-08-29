// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- as_ref / as_mut / unwrap_or_default tests (#1296) ---

/// `as_ref` on a Datatype-sorted OptionInt receiver returns the receiver
/// term unchanged — identity in SMT. Part of #1296.
#[test]
#[timeout(30000)]
fn as_ref_option_returns_identity() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

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
    let opt_term = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt))
        .expect("declare opt");

    let result = encoder.encode_datatype_spec_method(&var("opt"), "as_ref", None);
    assert!(
        result.is_ok(),
        "as_ref on OptionInt should encode: {result:?}"
    );

    // as_ref is identity — result term should equal the receiver.
    let as_ref_term = result.unwrap();
    let neq = encoder.solver.neq(opt_term, as_ref_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "as_ref(opt) should be identical to opt (negation is UNSAT)"
    );
}

/// `as_mut` on a Datatype-sorted ResultIntInt receiver returns the
/// receiver term unchanged — identity in SMT. Part of #1296.
#[test]
#[timeout(30000)]
fn as_mut_result_returns_identity() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);
    let res_term = encoder
        .get_or_declare_var("res", Sort::Datatype(dt))
        .expect("declare res");

    let result = encoder.encode_datatype_spec_method(&var("res"), "as_mut", None);
    assert!(
        result.is_ok(),
        "as_mut on ResultIntInt should encode: {result:?}"
    );

    let as_mut_term = result.unwrap();
    let neq = encoder.solver.neq(res_term, as_mut_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "as_mut(res) should be identical to res (negation is UNSAT)"
    );
}

/// `as_ref` on Int-sorted (UF fallback) receiver still works as identity.
/// Part of #1296.
#[test]
#[timeout(30000)]
fn as_ref_int_sorted_returns_identity() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_datatype_spec_method(&var("x"), "as_ref", None);
    assert!(
        result.is_ok(),
        "as_ref on Int-sorted receiver should encode: {result:?}"
    );
}

/// `unwrap_or_default` on Datatype-sorted OptionInt: returns payload
/// for Some, 0 for None. Part of #1296.
#[test]
#[timeout(30000)]
fn unwrap_or_default_option_some_returns_payload() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

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
    encoder.ensure_datatype_declared(&dt.clone());

    // Build Some(42) and assert receiver = Some(42).
    let forty_two = encoder.solver.int_const(42);
    let some_42 = encoder
        .solver
        .datatype_constructor(&dt, "Some", &[forty_two]);
    let opt_var = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt))
        .expect("declare opt");
    let eq_some = encoder.solver.eq(opt_var, some_42);
    encoder.assert_term(eq_some);

    let result = encoder.encode_datatype_spec_method(&var("opt"), "unwrap_or_default", None);
    assert!(
        result.is_ok(),
        "unwrap_or_default on OptionInt should encode: {result:?}"
    );

    // unwrap_or_default(Some(42)) should be 42.
    let uod_term = result.unwrap();
    let expected = encoder.solver.int_const(42);
    let neq = encoder.solver.neq(uod_term, expected);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_or_default(Some(42)) should equal 42 (negation is UNSAT)"
    );
}

/// `unwrap_or_default` on Datatype-sorted OptionInt: returns 0 for None.
/// Part of #1296.
#[test]
#[timeout(30000)]
fn unwrap_or_default_option_none_returns_zero() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

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
    encoder.ensure_datatype_declared(&dt.clone());

    // Assert receiver = None.
    let none_term = encoder.solver.datatype_constructor(&dt, "None", &[]);
    let opt_var = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt))
        .expect("declare opt");
    let eq_none = encoder.solver.eq(opt_var, none_term);
    encoder.assert_term(eq_none);

    let result = encoder.encode_datatype_spec_method(&var("opt"), "unwrap_or_default", None);
    assert!(
        result.is_ok(),
        "unwrap_or_default on OptionInt None should encode: {result:?}"
    );

    // unwrap_or_default(None) should be 0.
    let uod_term = result.unwrap();
    let expected = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(uod_term, expected);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_or_default(None) should equal 0 (negation is UNSAT)"
    );
}

/// `unwrap_or_default` on Datatype-sorted ResultIntInt: returns payload
/// for Ok, 0 for Err. Part of #1296.
#[test]
#[timeout(30000)]
fn unwrap_or_default_result_ok_returns_payload() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt.clone());

    // Build Ok(7) and assert receiver = Ok(7).
    let seven = encoder.solver.int_const(7);
    let ok_7 = encoder.solver.datatype_constructor(&dt, "Ok", &[seven]);
    let res_var = encoder
        .get_or_declare_var("res", Sort::Datatype(dt))
        .expect("declare res");
    let eq_ok = encoder.solver.eq(res_var, ok_7);
    encoder.assert_term(eq_ok);

    let result = encoder.encode_datatype_spec_method(&var("res"), "unwrap_or_default", None);
    assert!(
        result.is_ok(),
        "unwrap_or_default on ResultIntInt should encode: {result:?}"
    );

    // unwrap_or_default(Ok(7)) should be 7.
    let uod_term = result.unwrap();
    let expected = encoder.solver.int_const(7);
    let neq = encoder.solver.neq(uod_term, expected);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_or_default(Ok(7)) should equal 7 (negation is UNSAT)"
    );
}

/// `unwrap_or_default` on Int-sorted (UF fallback) receiver works
/// without panic. Part of #1296.
#[test]
#[timeout(30000)]
fn unwrap_or_default_uf_fallback_encodes() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_datatype_spec_method(&var("x"), "unwrap_or_default", None);
    assert!(
        result.is_ok(),
        "unwrap_or_default on Int-sorted receiver should fall back to UF: {result:?}"
    );
}
