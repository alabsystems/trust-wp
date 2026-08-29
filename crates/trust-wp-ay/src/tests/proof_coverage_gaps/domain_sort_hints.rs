// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// propagate_domain_sort_hints coverage (#2002, #1572)
// =============================================================================

/// Test that propagate_domain_sort_hints propagates Seq sort hints from a
/// declared function's domain to call-site arguments.
///
/// Coverage target: `call_encoding.rs:propagate_domain_sort_hints` Seq branch
/// (lines 368-374). Zero direct tests before this.
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_propagate_domain_sort_hints_seq_branch() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a function with Seq-sorted parameter: f(s: Seq) -> Int
    let logic_fn = LogicFnDef::new(
        "f".to_string(),
        "crate::specs::f".to_string(),
        vec!["s".to_string()],
        method_call(var("s"), "len", vec![]),
    )
    .with_param_sorts(vec![Some(trust_wp_core::formula::ExprSort::Seq)])
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register f(s: Seq)");

    // Now encode f(v@) — the view of v should get a Seq sort hint
    // propagated by propagate_domain_sort_hints
    let call_expr = logic_fn_call("f", vec![view(var("v"))]);
    let result = encoder.encode_pure(&call_expr);
    assert!(
        result.is_ok(),
        "f(v@) should encode successfully with Seq propagation: {:?}",
        result.err()
    );

    // The sort hint should have been propagated to v@
    assert!(
        encoder
            .sort_resolver_for_test()
            .any_sort_hint_value(|h| matches!(h, trust_wp_core::formula::ExprSort::Seq)),
        "v@ should have received a Seq sort hint via propagate_domain_sort_hints"
    );
}

/// Test that propagate_domain_sort_hints propagates Datatype sort hints
/// from a declared function's domain to call-site argument var_sorts.
///
/// Coverage target: `call_encoding.rs:propagate_domain_sort_hints` Datatype
/// branch (lines 375-383). Zero direct tests before this.
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_propagate_domain_sort_hints_datatype_branch() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a UserDefined datatype
    let list_dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "head".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "tail".to_string(),
                        sort: Sort::Uninterpreted("List".to_string()),
                    },
                ],
            },
        ],
    };
    encoder.ensure_datatype_declared(&list_dt);

    // Manually declare a function with Datatype-sorted parameter
    let dt_sort = Sort::Datatype(list_dt.clone());
    let func_decl = encoder
        .solver
        .declare_fun("logic_list__len", &[dt_sort], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("logic_list__len".to_string(), func_decl);

    // Encode list_len(x) — x should get a Datatype var_sort via propagation
    let call_expr = logic_fn_call("list_len", vec![var("x")]);
    let result = encoder.encode_pure(&call_expr);
    assert!(
        result.is_ok(),
        "list_len(x) should encode: {:?}",
        result.err()
    );

    // Check that x got a Datatype sort in var_sorts
    assert!(
        encoder.var_sorts_for_test().contains_key("x"),
        "x should have received a Datatype var_sort via propagate_domain_sort_hints"
    );
    assert!(
        encoder.var_sorts_for_test()["x"].is_datatype(),
        "x's var_sort should be Datatype, got {:?}",
        encoder.var_sorts_for_test()["x"]
    );
}

/// Test that propagate_domain_sort_hints propagates FMap sort hints from a
/// declared function's domain to call-site arguments.
///
/// Coverage target: `call_encoding.rs:propagate_domain_sort_hints` FMap branch
/// (new in #994). Previously only Seq and Datatype branches existed.
///
/// Part of #994.
#[test]
#[timeout(30000)]
fn test_propagate_domain_sort_hints_fmap_branch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Manually declare a function with FMap-sorted parameter: g(m: FMap) -> Int
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let func_decl = encoder
        .solver
        .declare_fun("logic_fmap__size", &[fmap], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("logic_fmap__size".to_string(), func_decl);

    // Encode fmap_size(m@) — the view of m should get an FMap sort hint
    let call_expr = logic_fn_call("fmap_size", vec![view(var("m"))]);
    let result = encoder.encode_pure(&call_expr);
    assert!(
        result.is_ok(),
        "fmap_size(m@) should encode successfully with FMap propagation: {:?}",
        result.err()
    );

    // The FMap sort hint should have been propagated to m_view or m
    assert!(
        encoder
            .sort_resolver_for_test()
            .any_sort_hint_value(|h| matches!(h, trust_wp_core::formula::ExprSort::FMap)),
        "m@ should have received an FMap sort hint via propagate_domain_sort_hints"
    );
}

/// Test that collect_declared_fn_domain_sorts_batch records Seq sort plans
/// for variables that appear as logic function arguments before encoding.
///
/// This tests the pre-scan counterpart to the runtime propagate_domain_sort_hints.
/// The collector runs after logic function signatures are declared but before
/// variable pre-declaration, so bootstrap can route the result through
/// `SortPlan` instead of mutating encoder state directly. (#2155, #2020)
///
/// Part of #2155.
#[test]
#[timeout(30000)]
fn test_collect_declared_fn_domain_sorts_batch_seq() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a function with Seq-sorted parameter: f(s: Seq) -> Int
    let logic_fn = LogicFnDef::new(
        "f".to_string(),
        "crate::specs::f".to_string(),
        vec!["s".to_string()],
        method_call(var("s"), "len", vec![]),
    )
    .with_param_sorts(vec![Some(trust_wp_core::formula::ExprSort::Seq)])
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register f(s: Seq)");

    // Before encoding, collect the planned domain sorts for an expression
    // containing f(v@).
    let call_expr = logic_fn_call("f", vec![view(var("v"))]);
    let planned = crate::encoder::sort_context::preseed::collect_declared_fn_domain_sorts_batch(
        encoder.decls(),
        &[&call_expr],
    );

    assert_eq!(
        planned.get("v_view"),
        Some(&Sort::seq(Sort::Int)),
        "v_view should have a planned Seq declaration from domain propagation"
    );
}

/// Test that collect_declared_fn_domain_sorts_batch skips functions not yet
/// declared (no-op for unknown functions). (#2155)
///
/// Part of #2155.
#[test]
#[timeout(30000)]
fn test_collect_declared_fn_domain_sorts_batch_unknown_fn_noop() {
    let encoder = AYEncoder::new_with_quantifiers();

    // Don't register any function — collecting planned sorts for an unknown
    // function should be a no-op.
    let call_expr = logic_fn_call("unknown_fn", vec![view(var("v"))]);
    let planned = crate::encoder::sort_context::preseed::collect_declared_fn_domain_sorts_batch(
        encoder.decls(),
        &[&call_expr],
    );

    assert!(
        planned.is_empty(),
        "unknown function should not produce any planned domain sorts"
    );
}
