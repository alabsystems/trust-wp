// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;
use crate::EncodingError;

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_err_bool_payload_coerces_for_result_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();
    let result_int_int = DatatypeSort {
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
    encoder.ensure_datatype_declared(&result_int_int);

    let err_true = logic_fn_call("Err", vec![bool_expr(true)]);
    let err_one = logic_fn_call("Err", vec![int(1)]);
    let err_true_term = encoder
        .encode_pure(&err_true)
        .expect("Err(true) should encode for ResultIntInt without sort panic");
    let err_one_term = encoder
        .encode_pure(&err_one)
        .expect("Err(1) should encode for ResultIntInt");

    let eq = encoder.solver.eq(err_true_term, err_one_term);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Err(true) should coerce to the Int payload representation (Err(1))"
    );
}

/// Regression test: Err(true) via UF fallback (no ResultIntInt datatype declared).
///
/// Before fix: `apply_logic_fn` inferred the UF parameter sort as `Bool` from
/// the original `PureExpr::Bool(true)`, but the arg term was coerced to `Int`
/// (`ite(true, 1, 0)`). This caused a ay sort mismatch panic:
/// "expected Bool, got Int at argument 0". (#1277)
///
/// Semantic: UF congruence — encoding Err(true) twice should produce equal terms.
/// Part of #1990.
#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_err_bool_payload_coerces_for_uf_fallback() {
    let mut encoder = AYEncoder::new();

    // No ResultIntInt datatype declaration — takes UF fallback path
    let err_true = logic_fn_call("Err", vec![bool_expr(true)]);
    let term1 = encoder
        .encode_pure(&err_true)
        .expect("Err(true) should encode via UF fallback without sort panic");

    // UF congruence: same call encoded twice must be equal.
    let err_true2 = logic_fn_call("Err", vec![bool_expr(true)]);
    let term2 = encoder
        .encode_pure(&err_true2)
        .expect("second Err(true) encode");
    let eq = encoder.solver.eq(term1, term2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Err(true) != Err(true) should be Unsat (UF congruence) (#1990)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_rejects_concrete_float_markers() {
    let mut encoder = AYEncoder::new();
    let marker = logic_fn_call("__trust_wp_concrete_float_f64_3ff0000000000000", vec![]);

    let result = encoder.encode_pure(&marker);

    match result {
        Err(EncodingError::Unsupported { message, .. }) => {
            assert!(
                message.contains("escaped MIR translation folding"),
                "unexpected unsupported message: {message}"
            );
        }
        other => panic!("expected unsupported concrete-float marker error, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_apply_logic_fn_rejects_missing_arg_exprs_for_non_constructor_placeholder() {
    let mut encoder = AYEncoder::new();
    let arg = encoder.solver.int_const(1);

    let result = encoder.apply_logic_fn("unknown_fn", &[arg], None, None);

    match result {
        Err(EncodingError::SortInference {
            context, detail, ..
        }) => {
            assert!(
                context.contains("logic_fn_placeholder:unknown_fn"),
                "sort inference context should identify placeholder call, got: {context}"
            );
            assert!(
                detail.contains("no arg_exprs available"),
                "sort inference detail should explain missing arg expressions, got: {detail}"
            );
        }
        other => panic!("expected SortInference for missing arg_exprs, got: {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_err_unannotated_bool_var_coerces_for_result_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();
    let result_int_int = DatatypeSort {
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
    encoder.ensure_datatype_declared(&result_int_int);
    let _flag = encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("flag should declare as Bool");

    // Use unannotated Var("flag", None) to exercise context-based sort lookup.
    let err_flag = logic_fn_call("Err", vec![var("flag")]);
    let err_one = logic_fn_call("Err", vec![int(1)]);

    let err_flag_term = encoder
        .encode_pure(&err_flag)
        .expect("Err(flag) should coerce Bool var to Int payload");
    let err_one_term = encoder
        .encode_pure(&err_one)
        .expect("Err(1) should encode for ResultIntInt");

    // Semantic: Err(flag) and Err(1) are datatype constructor applications.
    // When flag is true (coerced to 1), they should be equal.
    // Assert flag = true, then Err(flag) != Err(1) → Unsat. Part of #1990.
    let flag_var = encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("get flag");
    let true_term = encoder.solver.bool_const(true);
    let flag_eq = encoder.solver.eq(flag_var, true_term);
    encoder.assert_term(flag_eq);
    let terms_eq = encoder.solver.eq(err_flag_term, err_one_term);
    let terms_neq = encoder.solver.not(terms_eq);
    encoder.assert_term(terms_neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Err(true) != Err(1) should be Unsat after Bool-to-Int coercion, got {result:?}"
    );
}

/// Semantic: UF congruence for Err via fallback — Err(flag) and Err(1) with
/// flag=true (coerced to 1) should be equal. Part of #1990.
#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_err_unannotated_bool_var_coerces_for_uf_fallback() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let _flag = encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("flag should declare as Bool");

    // No ResultIntInt datatype declaration — takes UF fallback path.
    // Regression: this must not declare Err(Bool) from context-only sort
    // and then panic on Err(1); it should coerce to Int consistently.
    let err_flag = logic_fn_call("Err", vec![var("flag")]);
    let err_one = logic_fn_call("Err", vec![int(1)]);
    let err_flag_term = encoder
        .encode_pure(&err_flag)
        .expect("Err(flag) should encode via UF fallback");
    let err_one_term = encoder
        .encode_pure(&err_one)
        .expect("Err(1) should reuse the same UF declaration");

    // Semantic: with flag=true (coerced to 1), Err(flag) == Err(1).
    let flag_var = encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("get flag");
    let true_term = encoder.solver.bool_const(true);
    let flag_eq = encoder.solver.eq(flag_var, true_term);
    encoder.assert_term(flag_eq);
    let terms_eq = encoder.solver.eq(err_flag_term, err_one_term);
    let terms_neq = encoder.solver.not(terms_eq);
    encoder.assert_term(terms_neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Err(true) != Err(1) via UF fallback should be Unsat after Bool-to-Int coercion, got {result:?}"
    );
}

/// Multi-call TypeParam→Int demotion regression for Creusot `clones/03.rs prog2`.
///
/// Models:
/// ```text
/// #[logic] fn omg<T>(_x: T) -> bool { true }
/// #[ensures(omg(x))] fn prog<T>(x: T) {}
/// #[ensures(omg(0))] fn prog2() { prog(0); }
/// ```
///
/// Before fix #2551, the generic `omg<T>` was declared with
/// `Sort::Uninterpreted("T")` domain. Calling `omg(0)` (Int arg) caused a sort
/// mismatch → `__apply_coerce` → `SortFallbackToInt` → demotion. The fix maps
/// `ExprSort::TypeParam → Sort::Int`, so both calls match without coercion.
///
/// This test verifies the multi-call pattern (two separate `omg(0)` invocations
/// from different logical contexts) produces zero demotion increments.
/// Part of #2551.
#[test]
#[timeout(30000)]
fn test_typeparam_multi_call_no_demotion_clones03_pattern() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{LogicFnDef, LogicMode},
    };

    use crate::encoder::unsoundness;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register: #[logic] fn omg<T>(_x: T) -> bool { true }
    let t_id = intern_sort_name("T");
    let omg_def = LogicFnDef::new(
        "omg".to_string(),
        "test::omg".to_string(),
        vec!["_x".to_string()],
        bool_expr(true),
    )
    .with_param_sorts(vec![Some(ExprSort::TypeParam(t_id))])
    .with_mode(LogicMode::Open);

    let before = unsoundness::snapshot();

    encoder
        .register_logic_fn(&omg_def)
        .expect("omg<T> registration should succeed");

    // First call: omg(0) — from prog2's postcondition
    let call1 = logic_fn_call("omg", vec![int(0)]);
    let term1 = encoder.encode_pure(&call1).expect("encode omg(0) #1");

    // Second call: omg(0) — from prog's instantiated postcondition (x=0)
    let call2 = logic_fn_call("omg", vec![int(0)]);
    let term2 = encoder.encode_pure(&call2).expect("encode omg(0) #2");

    // Both calls should produce true (axiom: omg(_x) = true)
    let not_term1 = encoder.solver.not(term1);
    encoder.solver.push();
    encoder.assert_term(not_term1);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "omg(0) should be true from axiom body"
    );
    encoder.solver.pop();

    // UF congruence: both calls with same arg should be equal
    let eq = encoder.solver.eq(term1, term2);
    let neq = encoder.solver.not(eq);
    encoder.solver.push();
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "omg(0) == omg(0) by UF congruence"
    );
    encoder.solver.pop();

    // No SortFallbackToInt should have fired — the TypeParam→Int fix means
    // the function domain is [Int] and the argument sort is Int → no coercion
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        !unsoundness::has_demoting(&delta),
        "multi-call TypeParam→Int pattern should not trigger demotion: delta = {delta:?}"
    );
}

/// Regression for `should_succeed/option.rs::ok_or` — `Var("ok", Datatype(...))
/// == LogicFnCall { "Ok", [Int(1)] }` triggered `sort mismatch in ite: expected
/// Bool, got Int` during `encode_and_assert_requires`. The encoder must not
/// feed an Int-sorted term to `solver.ite()` as the condition during
/// constructor-argument coercion.
#[test]
#[timeout(30000)]
fn test_var_datatype_eq_ok_int_constructor_no_ite_sort_panic() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new();
    let result_int_int = DatatypeSort {
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
    encoder.ensure_datatype_declared(&result_int_int);
    let result_sort = Sort::Datatype(result_int_int.clone());
    let _ok = encoder
        .get_or_declare_var("ok", result_sort.clone())
        .expect("ok should declare as ResultIntInt");

    let result_id = intern_sort_name("ResultIntInt");
    let assertion = eq(
        var_with_sort("ok", ExprSort::Datatype(result_id)),
        logic_fn_call("Ok", vec![int(1)]),
    );

    let _term = encoder
        .encode_pure(&assertion)
        .expect("Var(ok) == Ok(1) should encode without ay sort panic");
}

/// Regression for `should_succeed/option.rs::ok_or` — Option(Some) sibling case.
#[test]
#[timeout(30000)]
fn test_var_datatype_eq_some_int_constructor_no_ite_sort_panic() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new();
    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "optionint_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    let option_sort = Sort::Datatype(option_int.clone());
    let _some_var = encoder
        .get_or_declare_var("some", option_sort.clone())
        .expect("some should declare as OptionInt");

    let option_id = intern_sort_name("OptionInt");
    let assertion = eq(
        var_with_sort("some", ExprSort::Datatype(option_id)),
        logic_fn_call("Some", vec![int(1)]),
    );

    let _term = encoder
        .encode_pure(&assertion)
        .expect("Var(some) == Some(1) should encode without ay sort panic");
}
