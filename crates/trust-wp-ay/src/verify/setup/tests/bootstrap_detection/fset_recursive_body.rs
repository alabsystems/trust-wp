// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::tests::helpers::{ite, method_call};

/// Reproduction test for bug/vcgen set_max body structure.
/// The body contains Let, MethodCall(is_empty), MethodCall(peek),
/// MethodCall(remove), recursive LogicFnCall, and Ite — all of which
/// must encode without error.
#[test]
#[timeout(30000)]
fn test_fset_set_max_body_encodes_without_error() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Build set_max body:
    //   let x = s.peek();
    //   let s = s.remove(x);
    //   if s.is_empty() { x } else {
    //     let rec = set_max(s);
    //     if x >= rec { x } else { rec }
    //   }
    let inner_ite = ite(
        PureExpr::BinOp(Arc::new(var("x")), BinOp::Ge, Arc::new(var("rec"))),
        var("x"),
        var("rec"),
    );
    let rec_let = PureExpr::Let {
        var: "rec".to_string(),
        value: Arc::new(PureExpr::LogicFnCall {
            name: "set_max".to_string(),
            args: vec![var("s")],
        }),
        body: Arc::new(inner_ite),
    };
    let outer_ite = ite(method_call(var("s"), "is_empty", vec![]), var("x"), rec_let);
    let inner_let = PureExpr::Let {
        var: "s".to_string(),
        value: Arc::new(method_call(var("s"), "remove", vec![var("x")])),
        body: Arc::new(outer_ite),
    };
    let body = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(method_call(var("s"), "peek", vec![])),
        body: Arc::new(inner_let),
    };

    let mut logic_fn = LogicFnDef::new(
        "set_max".to_string(),
        "crate::set_max".to_string(),
        vec!["s".to_string()],
        body.clone(),
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    // requires: !s.is_empty()
    logic_fn.set_requires(vec![PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    )]);

    // ensures: s.contains(result)
    logic_fn.set_ensures(vec![method_call(var("s"), "contains", vec![var("result")])]);

    let expr_slices = [
        ExprSlice::formula(logic_fn.requires()),
        ExprSlice::formula(logic_fn.ensures()),
        ExprSlice::value(std::slice::from_ref(logic_fn.body())),
    ];
    let mut encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: Some(logic_fn.ensures()),
        result_expr: Some(logic_fn.body()),
        logic_fns: Some(LogicFnInput::Prefiltered(std::slice::from_ref(&logic_fn))),
        mode_overrides: None,
        type_invariants: None,
        track: trust_wp_core::TrackLevel::Auto,
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("production bootstrap must register the recursive FSet signature");
    assert!(encoder
        .decls()
        .has_logic_func(&trust_wp_core::logic::logic_fn_smt_name("set_max")));
    let encoded = encoder
        .encode_pure(logic_fn.body())
        .expect("the complete recursive FSet body must encode");
    assert_eq!(encoder.solver.get_sort(encoded), ay_dpll::api::Sort::Int);
    for clause in logic_fn.requires().iter().chain(logic_fn.ensures()) {
        encoder
            .encode_pure(clause)
            .expect("FSet contract must encode");
    }
    for name in ["fset_peek", "fset_remove", "fset_is_empty", "fset_contains"] {
        assert!(encoder.decls().has_spec_func(name), "missing {name}");
    }
}
