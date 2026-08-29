// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_view_constructor_preseed_inherits_declared_datatype_sort() {
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
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let expr = eq(view(var("self")), logic_fn_call("Some", vec![int(42)]));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View(Var) == constructor should encode without error: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "constructor preseed should prevent solver panic: {:?}",
        encoder.solver_panic_reason()
    );
    match encoder.var_sort("self_view") {
        Some(Sort::Datatype(dt_sort)) => assert_eq!(dt_sort.name, "OptionInt"),
        other => panic!("expected self_view to be Datatype(OptionInt), got: {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_var_nullary_user_defined_constructor_preseed_inherits_declared_datatype_sort() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtKind};

    let mut encoder = AYEncoder::new();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "State".to_string(),
        AdtDecl::new(
            "crate::State".to_string(),
            "State".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new("On".to_string(), "On".to_string(), vec![]),
                AdtConstructorDecl::new("Off".to_string(), "Off".to_string(), vec![]),
            ],
        ),
    )]));

    let expr = eq(var("state"), var("On"));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "state == On should encode without error: {result:?}"
    );
    match encoder.var_sort("state") {
        Some(Sort::Datatype(dt_sort)) => assert_eq!(dt_sort.name, "State"),
        other => panic!("expected state to be Datatype(State), got: {other:?}"),
    }
}

// =============================================================================
// extract_base_var_name tests (#P1-325: zero direct coverage)
// =============================================================================

mod extract_base_var_name_tests {
    use super::*;
    use crate::encoder::sort_context::extract_base_var_name;

    #[test]
    #[timeout(30000)]
    fn test_bare_var() {
        assert_eq!(extract_base_var_name(&var("x")), Some("x"));
    }

    #[test]
    #[timeout(30000)]
    fn test_deref_var() {
        assert_eq!(extract_base_var_name(&deref(var("v"))), Some("v"));
    }

    #[test]
    #[timeout(30000)]
    fn test_final_var() {
        assert_eq!(extract_base_var_name(&final_expr(var("v"))), Some("v"));
    }

    #[test]
    #[timeout(30000)]
    fn test_old_var() {
        assert_eq!(extract_base_var_name(&old(var("v"))), Some("v"));
    }

    #[test]
    #[timeout(30000)]
    fn test_view_var() {
        assert_eq!(extract_base_var_name(&view(var("v"))), Some("v"));
    }

    #[test]
    #[timeout(30000)]
    fn test_nested_wrappers() {
        // Final(Deref(Var("v"))) → Some("v")
        assert_eq!(
            extract_base_var_name(&final_expr(deref(var("v")))),
            Some("v")
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_nested_wrappers_with_view() {
        // View(Final(Deref(Var("v")))) → Some("v")
        assert_eq!(
            extract_base_var_name(&view(final_expr(deref(var("v"))))),
            Some("v")
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_non_var_returns_none() {
        assert_eq!(extract_base_var_name(&int(42)), None);
        assert_eq!(extract_base_var_name(&add(var("x"), int(1))), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_deref_of_non_var_returns_none() {
        // Deref(BinOp(...)) → None
        assert_eq!(extract_base_var_name(&deref(add(var("x"), int(1)))), None);
    }
}

// =============================================================================
// extract_constructor_name tests (#1752: broader preseed scanning)
// =============================================================================

mod extract_constructor_name_tests {
    use super::*;
    use crate::encoder::sort_context::extract_constructor_name;

    #[test]
    #[timeout(30000)]
    fn test_direct_logic_fn_call() {
        let expr = logic_fn_call("Some", vec![int(42)]);
        assert_eq!(extract_constructor_name(&expr), Some("Some"));
    }

    #[test]
    #[timeout(30000)]
    fn test_wrapped_in_old() {
        let expr = old(logic_fn_call("Some", vec![int(42)]));
        assert_eq!(extract_constructor_name(&expr), Some("Some"));
    }

    #[test]
    #[timeout(30000)]
    fn test_wrapped_in_view() {
        let expr = view(logic_fn_call("OwnResult::Ok", vec![var("t")]));
        assert_eq!(extract_constructor_name(&expr), Some("OwnResult::Ok"));
    }

    #[test]
    #[timeout(30000)]
    fn test_ite_then_branch() {
        let expr = PureExpr::Ite(
            Arc::new(var("flag")),
            Arc::new(logic_fn_call("Some", vec![int(42)])),
            Arc::new(int(0)),
        );
        assert_eq!(extract_constructor_name(&expr), Some("Some"));
    }

    #[test]
    #[timeout(30000)]
    fn test_ite_else_branch() {
        let expr = PureExpr::Ite(
            Arc::new(var("flag")),
            Arc::new(int(0)),
            Arc::new(logic_fn_call("None", vec![])),
        );
        assert_eq!(extract_constructor_name(&expr), Some("None"));
    }

    #[test]
    #[timeout(30000)]
    fn test_ite_both_branches_prefers_then() {
        let expr = PureExpr::Ite(
            Arc::new(var("flag")),
            Arc::new(logic_fn_call("Some", vec![int(42)])),
            Arc::new(logic_fn_call("None", vec![])),
        );
        assert_eq!(extract_constructor_name(&expr), Some("Some"));
    }

    #[test]
    #[timeout(30000)]
    fn test_non_constructor_returns_none() {
        assert_eq!(extract_constructor_name(&int(42)), None);
        assert_eq!(extract_constructor_name(&var("x")), None);
        assert_eq!(extract_constructor_name(&add(var("x"), int(1))), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_deref_logic_fn_call() {
        let expr = deref(logic_fn_call("Some", vec![int(42)]));
        assert_eq!(extract_constructor_name(&expr), Some("Some"));
    }

    /// Regression for #1805: the contract parser produces `Var("None")` for
    /// bare `None` in postconditions and proof_assert expressions. Without
    /// recognizing `Var("None")` as a constructor, `preseed_constructor_var_sort`
    /// skips the preseeding and the variable defaults to `Sort::Int`.
    #[test]
    #[timeout(30000)]
    fn test_var_none_recognized_as_constructor() {
        assert_eq!(extract_constructor_name(&var("None")), Some("None"));
    }

    /// Regular variables must NOT be confused with constructors.
    #[test]
    #[timeout(30000)]
    fn test_var_some_not_recognized_as_constructor() {
        // "Some" is not nullary (it takes an argument), so Var("Some") is not
        // recognized. The contract parser emits Some(v) as LogicFnCall, not Var.
        assert_eq!(extract_constructor_name(&var("Some")), None);
    }
}

// =============================================================================
// Ite-wrapped constructor preseed tests (#1752)
// =============================================================================

/// Regression for #1752: `x == if cond { Some(v) } else { None }` should
/// pre-seed `x` with the datatype sort even though the constructor is inside
/// an `Ite`. Without `extract_constructor_name` looking through `Ite` branches,
/// `x` defaults to `Sort::Int` and `mk_eq(Int, OptionInt)` panics.
#[test]
#[timeout(30000)]
fn test_ite_wrapped_constructor_preseed_no_sort_mismatch() {
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
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Pattern: x == if flag { Some(42) } else { None }
    let ite_ctor = PureExpr::Ite(
        Arc::new(var("flag")),
        Arc::new(logic_fn_call("Some", vec![int(42)])),
        Arc::new(logic_fn_call("None", vec![])),
    );
    let expr = eq(var("x"), ite_ctor);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Var == Ite(_, Ctor, Ctor) should encode without error: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Ite-wrapped constructor preseed should prevent sort mismatch panic: {:?}",
        encoder.solver_panic_reason()
    );
    match encoder.var_sort("x") {
        Some(Sort::Datatype(dt_sort)) => assert_eq!(dt_sort.name, "OptionInt"),
        other => panic!("expected x to be Datatype(OptionInt), got: {other:?}"),
    }
}

// =============================================================================
// Var("None") constructor preseed tests (#1805)
// =============================================================================

/// Regression for #1805: `inserted_none == None` where `None` is parsed as
/// `Var("None")` by the contract parser. When OptionInt is already declared
/// (from a prior match), `encode_logic_fn_call_impl("None")` produces an
/// OptionInt-sorted constructor term. Without recognizing `Var("None")` in
/// `extract_constructor_name`, `preseed_constructor_var_sort` skips the
/// preseeding, leaving `inserted_none` as `Sort::Int`. The resulting
/// `mk_eq(Int, OptionInt)` panics.
#[test]
#[timeout(30000)]
fn test_var_none_preseed_prevents_sort_mismatch() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort as AYDatatypeSort};

    let mut encoder = AYEncoder::new();
    let dt = AYDatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Pattern: inserted_none == None (contract parser produces Var("None"))
    let expr = eq(var("inserted_none"), var("None"));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Var == Var('None') with declared OptionInt should encode without error: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Var('None') preseed should prevent mk_eq(Int, OptionInt) panic: {:?}",
        encoder.solver_panic_reason()
    );
    // Verify the variable was pre-seeded with the OptionInt datatype sort.
    match encoder.var_sort("inserted_none") {
        Some(Sort::Datatype(dt_sort)) => assert_eq!(dt_sort.name, "OptionInt"),
        other => panic!("expected inserted_none to be Datatype(OptionInt), got: {other:?}"),
    }
}

/// Regression for #994: tuple carriers must preseed through `x == tupleN(...)`
/// before later tuple projections are encoded, otherwise `x` stays Int and
/// `tuple_get_i(x)` reuses the wrong domain sort.
#[test]
#[timeout(30000)]
fn test_tuple_constructor_preseed_upgrades_var_to_tuple_sort() {
    let mut encoder = AYEncoder::new();
    let tuple2 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);

    let expr = eq(var("pair"), logic_fn_call(&tuple2, vec![int(1), int(2)]));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Var == tuple2(...) should encode without error: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "tuple constructor preseed should prevent downstream sort mismatch: {:?}",
        encoder.solver_panic_reason()
    );
    match encoder.var_sort("pair") {
        Some(Sort::Uninterpreted(name)) => assert_eq!(name, "Tuple2"),
        other => panic!("expected pair to be Tuple2, got: {other:?}"),
    }
}
