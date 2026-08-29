// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Verify that type invariant registration populates the ground pool (#1965, Lane 5).
///
/// When `register_type_invariant` is called, the defining axiom should be
/// registered with the ground pool so that ground applications of `inv(x)`
/// can be instantiated with the invariant body.
#[test]
#[timeout(30000)]
fn test_type_invariant_registers_with_ground_pool() {
    let mut encoder = AYEncoder::new();

    // Register a non-trivial type invariant: inv(self) = self > 0
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("NonZero", "self", ay_dpll::api::Sort::Int, &body)
        .expect("registration should succeed");

    // The ground pool should have 1 axiom (the type invariant)
    assert_eq!(
        encoder.ground_pool.axiom_count(),
        1,
        "type invariant should register an axiom in ground pool"
    );

    // Verify axiom content
    let axiom = &encoder.ground_pool.axioms()[0];
    assert_eq!(axiom.params, vec!["self"]);
    assert_eq!(axiom.return_sort, ay_dpll::api::Sort::Bool);
    assert!(axiom.requires.is_empty());
}

/// Verify that trivial type invariants (body = true) do NOT register with
/// the ground pool since they are handled by inline optimization (#1296).
#[test]
#[timeout(30000)]
fn test_trivial_type_invariant_skips_ground_pool() {
    let mut encoder = AYEncoder::new();

    // Register a trivial type invariant: inv(self) = true
    let body = PureExpr::Bool(true);
    encoder
        .register_type_invariant("TrivialType", "self", ay_dpll::api::Sort::Int, &body)
        .expect("registration should succeed");

    // Trivial invariants short-circuit before the ground pool registration
    assert_eq!(
        encoder.ground_pool.axiom_count(),
        0,
        "trivial type invariant should NOT register in ground pool"
    );
}

/// Verify type invariant axiom produces UNSAT when ground-instantiated
/// with a concrete value that satisfies the invariant (#1965, Lane 5).
///
/// Strengthens `test_type_invariant_registers_with_ground_pool` by
/// actually instantiating the axiom and checking solver UNSAT.
#[test]
#[timeout(30000)]
fn test_type_invariant_ground_instantiation_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register type invariant: inv(self) = (self > 0)
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("NonZero", "self", ay_dpll::api::Sort::Int, &body)
        .expect("registration should succeed");

    assert_eq!(encoder.ground_pool.axiom_count(), 1);

    // Register a ground application: inv(42) with SMT term
    let inv_decl = encoder.ground_pool.axioms()[0].func_decl.clone();
    let forty_two = encoder.solver.int_const(42);
    let inv_42 = encoder.solver.apply(&inv_decl, &[forty_two]);
    encoder.ground_pool.register(
        &encoder.ground_pool.axioms()[0].fn_symbol.clone(),
        inv_42,
        vec![forty_two],
        vec![PureExpr::Int(42)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "should instantiate 1 type invariant ground instance"
    );

    // Ground instance: inv(42) = (42 > 0) = true.
    // Assert inv(42) is false and check for UNSAT.
    let not_inv_42 = encoder.solver.not(inv_42);
    encoder.solver.assert_term(not_inv_42);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "should be UNSAT: inv(42) = (42 > 0) = true contradicts !inv(42), got {result:?}"
    );
}

/// Same-name datatype carriers can drift across encoder paths (#2189). When a
/// call site encodes `inv(x)` against the drifted carrier, ground
/// instantiation must reuse that concrete application term instead of trying
/// to re-apply the original axiom declaration.
#[test]
#[timeout(30000)]
fn test_type_invariant_ground_instantiation_reuses_same_name_datatype_application() {
    use trust_wp_core::{
        formula::{intern_sort_name, BinOp, ExprSort},
        logic::{type_invariant_method_name, AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult, Sort};

    let mut encoder = AYEncoder::new_all();
    let zero_sort_expr = ExprSort::Datatype(intern_sort_name("Zero"));
    let adt_decls = std::collections::HashMap::from([(
        "Zero".to_string(),
        AdtDecl::new(
            "Zero".to_string(),
            "Zero".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Zero".to_string(),
                "Zero".to_string(),
                vec![
                    AdtFieldDecl::new("0".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("1".to_string(), ExprSort::Int),
                ],
            )],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let registered_zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());
    let Sort::Datatype(registered_zero_dt) = registered_zero_sort.clone() else {
        panic!("registered Zero sort should be a native datatype");
    };
    let (field0_selector, field0_sort) = encoder
        .native_positional_field_selector(&registered_zero_sort, 0)
        .expect("Zero field 0 selector should resolve");
    let (field1_selector, _) = encoder
        .native_positional_field_selector(&registered_zero_sort, 1)
        .expect("Zero field 1 selector should resolve");

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var(
                "self".to_string(),
                Some(zero_sort_expr.clone()),
            )],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("Zero", "self", Sort::Datatype(registered_zero_dt), &body)
        .expect("type invariant registration should succeed");

    let drifted_zero_dt = DatatypeSort {
        name: "Zero".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Zero".to_string(),
            fields: vec![
                DatatypeField {
                    name: field0_selector.clone(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: field1_selector,
                    sort: Sort::Bool,
                },
            ],
        }],
    };
    let x = encoder
        .solver
        .declare_const("x_same_name_dt", Sort::Datatype(drifted_zero_dt.clone()));
    encoder.rebind_var("x", x, Sort::Datatype(drifted_zero_dt));

    let inv_x_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), Some(zero_sort_expr))),
        method: type_invariant_method_name("Zero"),
        args: vec![],
    };
    let inv_x = encoder
        .encode_pure(&inv_x_expr)
        .expect("same-name datatype invariant call should encode");

    let count = encoder
        .assert_ground_pool_instances()
        .expect("ground instantiation should succeed");
    assert_eq!(
        count, 1,
        "same-name datatype drift should still instantiate the invariant body"
    );

    encoder.assert_term(inv_x);
    let field0_term = encoder
        .solver
        .try_datatype_selector(&field0_selector, x, field0_sort)
        .expect("field 0 selector should apply to drifted Zero term");
    let zero = encoder.solver.int_const(0);
    let field0_is_zero = encoder.solver.eq(field0_term, zero);
    let field0_is_nonzero = encoder.solver.not(field0_is_zero);
    encoder.solver.assert_term(field0_is_nonzero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ground instantiation should connect inv(x) to x.0 == 0 across same-name datatype drift, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_type_invariant_body_binding_uses_native_selector_across_same_name_datatype_drift() {
    use trust_wp_core::{
        formula::{intern_sort_name, BinOp, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult, Sort};

    let mut encoder = AYEncoder::new_all();
    let zero_sort_expr = ExprSort::Datatype(intern_sort_name("Zero"));
    let adt_decls = std::collections::HashMap::from([(
        "Zero".to_string(),
        AdtDecl::new(
            "Zero".to_string(),
            "Zero".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Zero".to_string(),
                "Zero".to_string(),
                vec![
                    AdtFieldDecl::new("0".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("1".to_string(), ExprSort::Int),
                ],
            )],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let registered_zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());
    let Sort::Datatype(registered_zero_dt) = registered_zero_sort.clone() else {
        panic!("registered Zero sort should be a native datatype");
    };
    let (field0_selector, field0_sort) = encoder
        .native_positional_field_selector(&registered_zero_sort, 0)
        .expect("Zero field 0 selector should resolve");
    let (field1_selector, _) = encoder
        .native_positional_field_selector(&registered_zero_sort, 1)
        .expect("Zero field 1 selector should resolve");

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var(
                "self".to_string(),
                Some(zero_sort_expr.clone()),
            )],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("Zero", "self", Sort::Datatype(registered_zero_dt), &body)
        .expect("type invariant registration should succeed");

    let drifted_zero_dt = DatatypeSort {
        name: "Zero".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Zero".to_string(),
            fields: vec![
                DatatypeField {
                    name: field0_selector.clone(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: field1_selector,
                    sort: Sort::Bool,
                },
            ],
        }],
    };
    let x = encoder
        .solver
        .declare_const("x_same_name_dt", Sort::Datatype(drifted_zero_dt.clone()));
    encoder.rebind_var("x", x, Sort::Datatype(drifted_zero_dt));

    let old_self = encoder.insert_var("self".to_string(), x);
    let body_term = encoder
        .encode_pure(&body)
        .expect("invariant body should encode against rebound self");
    encoder.restore_var("self", old_self);

    let field0_term = encoder
        .solver
        .try_datatype_selector(&field0_selector, x, field0_sort)
        .expect("field 0 selector should apply to drifted Zero term");
    let zero = encoder.solver.int_const(0);
    let field0_is_zero = encoder.solver.eq(field0_term, zero);
    let field0_is_nonzero = encoder.solver.not(field0_is_zero);
    let body_and_not_selector = encoder.solver.and(body_term, field0_is_nonzero);
    encoder.solver.assert_term(body_and_not_selector);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "bound invariant body should reduce to the native field selector across same-name datatype drift, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_type_invariant_registration_binds_unannotated_self_sort_for_native_selector_encoding() {
    use trust_wp_core::{
        formula::{intern_sort_name, BinOp, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_all();
    let zero_sort_expr = ExprSort::Datatype(intern_sort_name("Zero"));
    let adt_decls = std::collections::HashMap::from([(
        "Zero".to_string(),
        AdtDecl::new(
            "Zero".to_string(),
            "Zero".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Zero".to_string(),
                "Zero".to_string(),
                vec![
                    AdtFieldDecl::new("0".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("1".to_string(), ExprSort::Int),
                ],
            )],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let registered_zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());
    let Sort::Datatype(registered_zero_dt) = registered_zero_sort.clone() else {
        panic!("registered Zero sort should be a native datatype");
    };

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("Zero", "self", Sort::Datatype(registered_zero_dt), &body)
        .expect("type invariant registration should succeed");
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "type invariant registration should use the native selector path for unannotated self instead of declaring a tuple-get UF"
    );
}
