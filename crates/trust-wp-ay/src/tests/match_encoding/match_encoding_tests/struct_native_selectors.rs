// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use super::*;

fn sample_struct_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([
        (
            "Point".to_string(),
            AdtDecl::new(
                "crate::Point".to_string(),
                "Point".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "Point".to_string(),
                    "Point".to_string(),
                    vec![
                        AdtFieldDecl::new("x".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("y".to_string(), ExprSort::Int),
                    ],
                )],
            ),
        ),
        (
            "Range".to_string(),
            AdtDecl::new(
                "crate::Range".to_string(),
                "Range".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "Range".to_string(),
                    "Range".to_string(),
                    vec![
                        AdtFieldDecl::new("start".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("end".to_string(), ExprSort::Int),
                    ],
                )],
            ),
        ),
    ])
}

#[test]
#[timeout(30000)]
fn test_verification_request_adt_decls_thread_native_struct_field_selector() {
    // The placed spelling: the driver's placement pass (contract_rewrite::
    // placement) turns `Point{x,y}` into `Point` with its arguments at their
    // declared indices, and the encoder's one door refuses the unplaced form
    // (verify::placement_gate).
    let body = PureExpr::LogicFnCall {
        name: "Point".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Int(7)],
    };
    let ensures = eq(named_field("x", var("result")), int(5));

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_struct_adt_decls())),
    )
    .unwrap();

    assert!(
            matches!(result, crate::VerificationResult::Verified(_)),
            "registered struct ADT metadata should route constructor + named field access natively: {result:?}"
        );
}

#[test]
#[timeout(30000)]
fn test_tuple_lowered_body_binds_declared_struct_result_datatype() {
    let body = logic_fn_call(
        "__trust_wp_tuple2",
        vec![PureExpr::Int(5), PureExpr::Int(7)],
    );
    let result = var_with_sort(
        "result",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("crate::Point")),
    );
    let ensures = eq(named_field("x", result), int(5));

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_struct_adt_decls())),
    )
    .unwrap();

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "tuple-lowered struct return body should materialize the declared result datatype: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_same_layout_structs_use_distinct_datatype_sorts() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_struct_adt_decls());

    let point_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("crate::Point"),
    ));
    let range_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("crate::Range"),
    ));

    assert!(
        matches!(point_sort, Sort::Datatype(_)),
        "Point should resolve to a native datatype sort: {point_sort:?}"
    );
    assert!(
        matches!(range_sort, Sort::Datatype(_)),
        "Range should resolve to a native datatype sort: {range_sort:?}"
    );
    assert_ne!(
        point_sort, range_sort,
        "same-layout structs must keep distinct ay carrier sorts"
    );
}

/// Encoder-level smoke test: selector on a Datatype-sorted variable returns
/// the correct Int value. (#1982 debugging)
#[test]
#[timeout(30000)]
fn test_native_selector_on_datatype_var_encoder_level() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let foo_decls = std::collections::HashMap::from([(
        "Foo".to_string(),
        AdtDecl::new(
            "crate::Foo".to_string(),
            "Foo".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Foo".to_string(),
                "Foo".to_string(),
                vec![AdtFieldDecl::new("val".to_string(), ExprSort::Int)],
            )],
        ),
    )]);

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&foo_decls);

    // Resolve Foo sort
    let foo_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("crate::Foo"),
    ));
    assert!(
        matches!(foo_sort, Sort::Datatype(_)),
        "Foo should be a native datatype sort: {foo_sort:?}"
    );

    // Declare variable x of sort Foo
    let x = encoder
        .get_or_declare_var("x", foo_sort)
        .expect("x should declare");

    // Look up native selector for field "val"
    let x_sort = encoder.solver.get_sort(x);
    let selector_info = encoder.native_named_field_selector(&x_sort, "val");
    assert!(
        selector_info.is_some(),
        "native_named_field_selector should find 'val' on Foo"
    );
    let (sel_name, sel_sort) = selector_info.unwrap();
    assert_eq!(sel_sort, Sort::Int, "val field should be Int");

    // Apply the selector
    let val_term = encoder
        .solver
        .try_datatype_selector(&sel_name, x, sel_sort)
        .expect("selector application should succeed");

    // Assert val_term > 0
    let zero = encoder.solver.int_const(0);
    let val_gt_zero = encoder.solver.gt(val_term, zero);
    encoder.solver.assert_term(val_gt_zero);

    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, ay_dpll::api::SolveResult::Sat),
        "val(x) > 0 should be satisfiable: {sat_result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_native_positional_field_selector_matches_named_selector() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_struct_adt_decls());

    let point_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("crate::Point"),
    ));
    let point = encoder
        .get_or_declare_var("point", point_sort)
        .expect("point should declare");

    let receiver_sort = encoder.solver.get_sort(point);
    let named = encoder
        .native_named_field_selector(&receiver_sort, "x")
        .expect("named selector should resolve x on Point");
    let positional = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("positional selector should resolve field 0 on Point");

    assert_eq!(
        positional, named,
        "tuple_get_0 on a registered struct should resolve to the same native selector as field x"
    );
    assert!(
        encoder
            .native_positional_field_selector(&receiver_sort, 2)
            .is_none(),
        "out-of-bounds positional selectors should not resolve"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_struct_tuple_get_skips_bare_tuple_getter_uf() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_struct_adt_decls());

    let point_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("crate::Point"),
    ));
    encoder
        .var_sorts_mut_for_test()
        .insert("p".to_string(), point_sort);

    let tuple_get_expr = logic_fn_call("__trust_wp_tuple_get_0", vec![var("p")]);
    let tuple_get_term = encoder
        .encode_pure(&tuple_get_expr)
        .expect("tuple_get_0 on Point should encode through a native selector");

    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "registered struct tuple getter should not declare the bare tuple-get UF"
    );

    let p = *encoder
        .vars_for_test()
        .get("p")
        .expect("p should be declared");
    let receiver_sort = encoder.solver.get_sort(p);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on Point should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, p, selector_sort)
        .expect("native selector application should succeed");

    let eq = encoder.solver.eq(tuple_get_term, selector_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "tuple_get_0(Point) should encode to the same term as the native selector"
    );
}

#[test]
#[timeout(30000)]
fn test_inline_registered_struct_tuple_get_skips_bare_tuple_getter_uf() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_struct_adt_decls());

    let inline_point = PureExpr::LogicFnCall {
        name: "Point{x,y}".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Int(7)],
    };
    let tuple_get_expr = logic_fn_call("__trust_wp_tuple_get_0", vec![inline_point.clone()]);
    let tuple_get_term = encoder
        .encode_pure(&tuple_get_expr)
        .expect("tuple_get_0 on inline Point should encode through a native selector");

    assert!(
            !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
            "registered struct tuple getter should not declare the bare tuple-get UF for inline constructors"
        );

    let point_term = encoder
        .encode_pure(&inline_point)
        .expect("Point constructor should encode natively");
    let receiver_sort = encoder.solver.get_sort(point_term);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on Point should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, point_term, selector_sort)
        .expect("native selector application should succeed");

    let eq = encoder.solver.eq(tuple_get_term, selector_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "tuple_get_0(Point{{x,y}}) should encode to the same term as the native selector"
    );
}

#[test]
#[timeout(30000)]
fn test_inline_registered_struct_tuple_get_falls_back_for_non_native_constructor_payloads() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_struct_adt_decls());

    let non_native_point = PureExpr::LogicFnCall {
        name: "Point{x,y}".to_string(),
        args: vec![logic_fn_call("seq", vec![int(5)]), PureExpr::Int(7)],
    };
    let tuple_get_expr = logic_fn_call("__trust_wp_tuple_get_0", vec![non_native_point]);

    encoder
            .encode_pure(&tuple_get_expr)
            .expect("tuple_get_0 should fall back to the bare UF when the constructor payload sorts are not native-compatible");

    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    assert!(
            encoder
                .decls()
                .logic_func_names()
                .any(|name| name.starts_with(&format!("{getter_smt_name}__placeholder_"))),
            "non-native inline constructor payloads should keep tuple_get_0 on the placeholder fallback path"
        );
}

/// Positional tuple getter (`__trust_wp_tuple_get_N`) routes through native
/// datatype selectors when the receiver has a registered struct ADT (#1982).
///
/// The driver rewrites `__trust_wp_field_x(p)` → `__trust_wp_tuple_get_0(p)`.
/// Without the native selector upgrade, the tuple getter path uses
/// quantified UF axioms which are less reliable for ay-dpll. With the
/// upgrade, positional access on a registered struct datatype uses the
/// same native selector as `__trust_wp_field_x`.
#[test]
#[timeout(30000)]
fn test_tuple_get_uses_native_selector_on_registered_struct() {
    // Construct: Point(5, 7), ensures: __trust_wp_tuple_get_0(result) == 5
    // The placed spelling: the driver's placement pass (contract_rewrite::
    // placement) turns `Point{x,y}` into `Point` with its arguments at their
    // declared indices, and the encoder's one door refuses the unplaced form
    // (verify::placement_gate).
    let body = PureExpr::LogicFnCall {
        name: "Point".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Int(7)],
    };
    let ensures = eq(get_field(0, var("result")), int(5));

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_struct_adt_decls())),
    )
    .unwrap();

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "positional tuple getter should use native selector on registered struct: {result:?}"
    );
}

/// Verify both positional fields route through native selectors: field 0 (x)
/// and field 1 (y) both return correct values from a constructor.
#[test]
#[timeout(30000)]
fn test_tuple_get_both_fields_native_selector() {
    // The placed spelling: the driver's placement pass (contract_rewrite::
    // placement) turns `Point{x,y}` into `Point` with its arguments at their
    // declared indices, and the encoder's one door refuses the unplaced form
    // (verify::placement_gate).
    let body = PureExpr::LogicFnCall {
        name: "Point".to_string(),
        args: vec![PureExpr::Int(3), PureExpr::Int(9)],
    };
    // ensures: __trust_wp_tuple_get_0(result) + __trust_wp_tuple_get_1(result) == 12
    let sum = add(get_field(0, var("result")), get_field(1, var("result")));
    let ensures = eq(sum, int(12));

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_struct_adt_decls())),
    )
    .unwrap();

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "both positional fields should route through native selectors: {result:?}"
    );
}
