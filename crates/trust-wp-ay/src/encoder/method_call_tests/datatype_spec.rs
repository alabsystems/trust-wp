// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Native datatype fast path tests for spec methods (#2211, #994) ---

/// `is_some` on a Datatype-sorted OptionInt receiver uses the native
/// tester path (not UF fallback). Verifies the term is usable in Bool
/// context and semantically correct: `is_some(Some(42))` is true.
#[test]
#[timeout(30000)]
fn is_some_native_tester_on_datatype_sorted_option() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // Declare OptionInt datatype and create a Datatype-sorted variable.
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
    encoder
        .get_or_declare_var("opt", Sort::Datatype(dt.clone()))
        .expect("declare opt");

    // Build Some(42) term for semantic check.
    let forty_two = encoder.solver.int_const(42);
    let some_42 = encoder
        .solver
        .datatype_constructor(&dt, "Some", &[forty_two]);

    // Encode is_some on the Datatype-sorted receiver.
    let result = encoder.encode_datatype_spec_method(&var("opt"), "is_some", None);
    assert!(
        result.is_ok(),
        "is_some on Datatype-sorted OptionInt should encode: {result:?}"
    );

    // No UF `is_some` tester should be declared — native path was used.
    assert!(
        !encoder.decls.has_spec_func("is_some"),
        "native tester path should not declare UF is_some"
    );

    // Semantic check: is_some(Some(42)) must be true.
    let is_some_42 = encoder
        .solver
        .try_datatype_tester("Some", some_42)
        .expect("native tester on Some(42)");
    let negated = encoder.solver.not(is_some_42);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(Some(42)) should be true (negation is UNSAT)"
    );
}

/// `is_none` on a Datatype-sorted OptionInt receiver uses the native
/// tester path and negates it. Semantically: `is_none(None)` is true.
#[test]
#[timeout(30000)]
fn is_none_native_tester_on_datatype_sorted_option() {
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
    let _opt = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt.clone()))
        .expect("declare opt");

    let result = encoder.encode_datatype_spec_method(&var("opt"), "is_none", None);
    assert!(
        result.is_ok(),
        "is_none on Datatype-sorted OptionInt should encode: {result:?}"
    );

    // Semantic check: is_none(None) must be true.
    let none_term = encoder.solver.datatype_constructor(&dt, "None", &[]);
    let is_some_none = encoder
        .solver
        .try_datatype_tester("Some", none_term)
        .expect("native tester on None");
    let is_none_none = encoder.solver.not(is_some_none);
    // is_none(None) = !is_some(None) should be true → negating it is UNSAT.
    let negated = encoder.solver.not(is_none_none);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_none(None) should be true (negation is UNSAT)"
    );
}

/// `is_ok` on a Datatype-sorted ResultIntInt receiver uses the native
/// tester path. Semantically: `is_ok(Ok(7))` is true.
#[test]
#[timeout(30000)]
fn is_ok_native_tester_on_datatype_sorted_result() {
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
    let _res = encoder
        .get_or_declare_var("res", Sort::Datatype(dt.clone()))
        .expect("declare res");

    let result = encoder.encode_datatype_spec_method(&var("res"), "is_ok", None);
    assert!(
        result.is_ok(),
        "is_ok on Datatype-sorted ResultIntInt should encode: {result:?}"
    );

    // Semantic check: is_ok(Ok(7)) must be true.
    let seven = encoder.solver.int_const(7);
    let ok_7 = encoder.solver.datatype_constructor(&dt, "Ok", &[seven]);
    let is_ok_term = encoder
        .solver
        .try_datatype_tester("Ok", ok_7)
        .expect("native tester on Ok(7)");
    let negated = encoder.solver.not(is_ok_term);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(Ok(7)) should be true (negation is UNSAT)"
    );
}

/// `is_err` on a Datatype-sorted ResultIntInt receiver uses the native
/// tester for `Ok` and negates. Semantically: `is_err(Err(99))` is true.
#[test]
#[timeout(30000)]
fn is_err_native_tester_on_datatype_sorted_result() {
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
    let _res = encoder
        .get_or_declare_var("res", Sort::Datatype(dt.clone()))
        .expect("declare res");

    let result = encoder.encode_datatype_spec_method(&var("res"), "is_err", None);
    assert!(
        result.is_ok(),
        "is_err on Datatype-sorted ResultIntInt should encode: {result:?}"
    );

    // Semantic check: is_err(Err(99)) must be true.
    let ninety_nine = encoder.solver.int_const(99);
    let err_99 = encoder
        .solver
        .datatype_constructor(&dt, "Err", &[ninety_nine]);
    let is_ok_term = encoder
        .solver
        .try_datatype_tester("Ok", err_99)
        .expect("native tester on Err(99)");
    let is_err_term = encoder.solver.not(is_ok_term);
    // is_err(Err(99)) should be true → negating it is UNSAT.
    let negated = encoder.solver.not(is_err_term);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_err(Err(99)) should be true (negation is UNSAT)"
    );
}

/// `unwrap` on a Datatype-sorted OptionInt receiver uses the native
/// selector path. Semantically: `unwrap(Some(42)) == 42`.
#[test]
#[timeout(30000)]
fn unwrap_native_selector_on_datatype_sorted_option() {
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
    let _opt = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt.clone()))
        .expect("declare opt");

    let result = encoder.encode_datatype_spec_method(&var("opt"), "unwrap", None);
    assert!(
        result.is_ok(),
        "unwrap on Datatype-sorted OptionInt should encode: {result:?}"
    );
    let _unwrap_term = result.unwrap();

    // No UF `spec_unwrap` accessor should be declared — native path was used.
    assert!(
        !encoder.decls.has_spec_func("spec_unwrap"),
        "native selector path should not declare UF spec_unwrap"
    );

    // Semantic check: unwrap(Some(42)) == 42.
    let forty_two = encoder.solver.int_const(42);
    let some_42 = encoder
        .solver
        .datatype_constructor(&dt, "Some", &[forty_two]);
    let sel_term = encoder
        .solver
        .try_datatype_selector("option_some_value", some_42, Sort::Int)
        .expect("native selector on Some(42)");
    let forty_two_again = encoder.solver.int_const(42);
    let neq = encoder.solver.neq(sel_term, forty_two_again);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap(Some(42)) should equal 42 (negation is UNSAT)"
    );
}

#[test]
#[timeout(30000)]
fn native_option_ground_bridge_connects_spec_unwrap_to_selector() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
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
    let opt = encoder
        .get_or_declare_var("opt_bridge", Sort::Datatype(dt.clone()))
        .expect("declare OptionInt term");

    let is_some = encoder
        .solver
        .try_datatype_tester("Some", opt)
        .expect("native Some tester");
    let native_payload = encoder
        .solver
        .try_datatype_selector("option_some_value", opt, Sort::Int)
        .expect("native payload selector");
    let unwrap_decl =
        encoder.get_or_declare_accessor_for_sorts("spec_unwrap", &Sort::Datatype(dt), &Sort::Int);
    let spec_payload = encoder.solver.apply(&unwrap_decl, &[opt]);

    encoder.assert_term(is_some);
    let payloads_differ = encoder.solver.neq(native_payload, spec_payload);
    encoder.assert_term(payloads_differ);

    let asserted = encoder.assert_native_option_ground_bridges();
    assert!(
        asserted >= 1,
        "observed native OptionInt payload and spec_unwrap terms should receive a finite bridge"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is-Some(opt) should force native selector and spec_unwrap payloads to agree"
    );
}

/// `unwrap_logic` is the stable logical helper on `OptionExt`; in SMT it is the
/// same Option payload projection as `unwrap`.
#[test]
#[timeout(30000)]
fn unwrap_logic_dispatches_to_option_payload_selector() {
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
    let opt = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt.clone()))
        .expect("declare opt");

    let forty_two = encoder.solver.int_const(42);
    let some_42 = encoder
        .solver
        .datatype_constructor(&dt, "Some", &[forty_two]);
    let eq_some = encoder.solver.eq(opt, some_42);
    encoder.assert_term(eq_some);

    let result = encoder.encode_pure(&method_call(var("opt"), "unwrap_logic", vec![]));
    assert!(
        result.is_ok(),
        "unwrap_logic should dispatch through datatype spec encoding: {result:?}"
    );

    assert!(
        !encoder.decls.has_spec_func("spec_unwrap"),
        "native selector path should not declare UF spec_unwrap"
    );

    let unwrapped = result.unwrap();
    let expected = encoder.solver.int_const(42);
    let neq = encoder.solver.neq(unwrapped, expected);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_logic(Some(42)) should equal 42 (negation is UNSAT)"
    );
}

/// `unwrap_err` on a Datatype-sorted ResultIntInt receiver uses the
/// native selector path. Semantically: `unwrap_err(Err(5)) == 5`.
#[test]
#[timeout(30000)]
fn unwrap_err_native_selector_on_datatype_sorted_result() {
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
    let _res = encoder
        .get_or_declare_var("res", Sort::Datatype(dt.clone()))
        .expect("declare res");

    let result = encoder.encode_datatype_spec_method(&var("res"), "unwrap_err", None);
    assert!(
        result.is_ok(),
        "unwrap_err on Datatype-sorted ResultIntInt should encode: {result:?}"
    );

    // Semantic check: unwrap_err(Err(5)) == 5.
    let five = encoder.solver.int_const(5);
    let err_5 = encoder.solver.datatype_constructor(&dt, "Err", &[five]);
    let sel_term = encoder
        .solver
        .try_datatype_selector("result_err_error", err_5, Sort::Int)
        .expect("native selector on Err(5)");
    let five_again = encoder.solver.int_const(5);
    let neq = encoder.solver.neq(sel_term, five_again);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_err(Err(5)) should equal 5 (negation is UNSAT)"
    );
}

/// Bare receivers now preseed the stdlib Option carrier for datatype-spec
/// methods, so `x.is_some()` upgrades to the native OptionInt lane rather
/// than falling through to the legacy Int-domain UF path.
#[test]
#[timeout(30000)]
fn is_some_bare_receiver_seeds_native_option_hint() {
    let mut encoder = AYEncoder::new();

    let result = encoder.encode_datatype_spec_method(&var("x"), "is_some", None);
    assert!(
        result.is_ok(),
        "is_some on a bare receiver should encode through the native Option carrier: {result:?}"
    );

    assert!(
        encoder.decls().has_datatype("OptionInt"),
        "datatype-spec seeding should declare OptionInt for bare receivers"
    );
    assert!(
        !encoder.decls.has_spec_func("__trust_wp_is_option"),
        "native carrier seeding should avoid the legacy Int-domain Option guard"
    );
}

/// Int-sorted receiver falls through to UF path for `unwrap`. Verifies
/// the UF accessor is declared when no native datatype is available.
#[test]
#[timeout(30000)]
fn unwrap_uf_fallback_on_int_sorted_receiver() {
    let mut encoder = AYEncoder::new();

    let result = encoder.encode_datatype_spec_method(&var("x"), "unwrap", None);
    assert!(
        result.is_ok(),
        "unwrap on Int-sorted receiver should fall back to UF: {result:?}"
    );

    // UF fallback declares spec_unwrap accessor.
    assert!(
        encoder.decls.has_spec_func("spec_unwrap"),
        "UF fallback should declare spec_unwrap"
    );
}

/// Direct constructor tester evaluation: `None().is_some()` -> false,
/// `Some(x).is_some()` -> true, without involving the solver. This is
/// critical for postcondition substitution where `self` is replaced by a
/// concrete constructor (e.g., in `ok_or` proofs). (#2670)
#[test]
#[timeout(30000)]
fn is_some_on_concrete_none_returns_false() {
    let mut encoder = AYEncoder::new();
    let result = encoder
        .encode_datatype_spec_method(&logic_fn_call("None", vec![]), "is_some", None)
        .expect("is_some on None() should encode");
    let false_const = encoder.solver.bool_const(false);
    let neq = encoder.solver.neq(result, false_const);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "None().is_some() must be false"
    );
}

/// `Some(42).is_some()` evaluates to true via direct constructor tester. (#2670)
#[test]
#[timeout(30000)]
fn is_some_on_concrete_some_returns_true() {
    let mut encoder = AYEncoder::new();
    let result = encoder
        .encode_datatype_spec_method(&logic_fn_call("Some", vec![int(42)]), "is_some", None)
        .expect("is_some on Some(42) should encode");
    let true_const = encoder.solver.bool_const(true);
    let neq = encoder.solver.neq(result, true_const);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Some(42).is_some() must be true"
    );
}

/// `None().is_none()` evaluates to true via direct constructor tester. (#2670)
#[test]
#[timeout(30000)]
fn is_none_on_concrete_none_returns_true() {
    let mut encoder = AYEncoder::new();
    let result = encoder
        .encode_datatype_spec_method(&logic_fn_call("None", vec![]), "is_none", None)
        .expect("is_none on None() should encode");
    let true_const = encoder.solver.bool_const(true);
    let neq = encoder.solver.neq(result, true_const);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "None().is_none() must be true"
    );
}

/// `Ok(7).is_ok()` evaluates to true via direct constructor tester. (#2670)
#[test]
#[timeout(30000)]
fn is_ok_on_concrete_ok_returns_true() {
    let mut encoder = AYEncoder::new();
    let is_ok = encoder
        .encode_datatype_spec_method(&logic_fn_call("Ok", vec![int(7)]), "is_ok", None)
        .expect("is_ok on Ok(7) should encode");
    let true_const = encoder.solver.bool_const(true);
    let neq = encoder.solver.neq(is_ok, true_const);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Ok(7).is_ok() must be true"
    );
}

/// Deref-wrapped constructors: `(*None()).is_some()` -> false. (#2670)
#[test]
#[timeout(30000)]
fn is_some_on_deref_none_returns_false() {
    use trust_wp_core::formula::PureExpr;
    let mut encoder = AYEncoder::new();
    let deref_none = PureExpr::Deref(std::sync::Arc::new(logic_fn_call("None", vec![])));
    let result = encoder
        .encode_datatype_spec_method(&deref_none, "is_some", None)
        .expect("is_some on *None() should encode");
    let false_const = encoder.solver.bool_const(false);
    let neq = encoder.solver.neq(result, false_const);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "(*None()).is_some() must be false"
    );
}
