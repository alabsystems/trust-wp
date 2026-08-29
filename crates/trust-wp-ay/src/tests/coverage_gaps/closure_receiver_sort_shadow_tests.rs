// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focused regressions for `find_postcondition_mut_receiver_sort` wrapper
//! recursion, binder shadowing, and depth limiting.

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{Pattern, PureExpr};

use super::*;

fn sort_name(sort: &Sort) -> &str {
    match sort {
        Sort::Uninterpreted(name) => name.as_str(),
        Sort::Datatype(dt) => dt.name.as_str(),
        Sort::Int => "Int",
        Sort::Bool => "Bool",
        _ => "other",
    }
}

fn register_closure_sort(encoder: &mut AYEncoder, def_id: &str) -> Sort {
    encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: def_id.to_string(),
                captures: vec![],
            },
        )
        .expect("closure sort registration should succeed")
}

/// `LetAssume` wrappers should recurse through the assumption expression, not
/// silently drop nested `postcondition_mut` calls.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_nested_in_let_assume_assumption() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_let_assume#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let body = let_assume(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("st1"), var("r")],
        ),
        PureExpr::Bool(true),
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert_eq!(
        sort_name(&result.expect("LetAssume assumption should recurse")),
        sort_name(&closure_sort)
    );
}

/// `LetObligation` wrappers should recurse through the obligation expression.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_nested_in_let_obligation_obligation() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_let_obligation#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let body = let_obligation(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("st1"), var("r")],
        ),
        PureExpr::Bool(true),
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert_eq!(
        sort_name(&result.expect("LetObligation obligation should recurse")),
        sort_name(&closure_sort)
    );
}

/// Match arms should recurse when the pattern does not bind the target name.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_nested_in_match_arm() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_match#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let body = match_expr(
        PureExpr::Bool(true),
        vec![(
            Pattern::Wildcard,
            method_call(
                var("f"),
                "postcondition_mut",
                vec![var("x"), var("st1"), var("r")],
            ),
        )],
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert_eq!(
        sort_name(&result.expect("match arms should recurse")),
        sort_name(&closure_sort)
    );
}

/// Pattern-bound names shadow outer existentials and must not drive sort
/// inference from the shadowed arm body.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_match_binding_shadow_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_match_shadow#0");
    encoder
        .get_or_declare_var("f", closure_sort)
        .expect("declare f with closure sort");

    let body = match_expr(
        PureExpr::Bool(true),
        vec![(
            Pattern::Binding("st1".to_string()),
            method_call(
                var("f"),
                "postcondition_mut",
                vec![var("x"), var("st1"), var("r")],
            ),
        )],
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_none(),
        "shadowed match bindings must not leak receiver sorts to the outer var"
    );
}

/// Let-bound names shadow the outer target variable in the let body.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_let_binding_shadow_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_let_shadow#0");
    encoder
        .get_or_declare_var("f", closure_sort)
        .expect("declare f with closure sort");

    let body = let_bind(
        "st1",
        PureExpr::Int(0),
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("st1"), var("r")],
        ),
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_none(),
        "let-bound shadowing must not leak the inner receiver sort"
    );
}

/// Nested quantifiers with the same bound name shadow the outer target variable.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_exists_binding_shadow_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_exists_shadow#0");
    encoder
        .get_or_declare_var("f", closure_sort)
        .expect("declare f with closure sort");

    let body = exists(
        "st1",
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("st1"), var("r")],
        ),
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_none(),
        "shadowed existential bindings must not leak the inner receiver sort"
    );
}

/// Closure params shadow outer names and must not influence receiver-sort
/// inference for the outer existential.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_closure_param_shadow_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::closure_param_shadow#0");
    encoder
        .get_or_declare_var("f", closure_sort)
        .expect("declare f with closure sort");

    let body = PureExpr::Closure {
        params: vec![("st1".to_string(), None)],
        body: Arc::new(method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("st1"), var("r")],
        )),
    };

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_none(),
        "closure params must shadow outer target vars during receiver-sort inference"
    );
}

/// Expressions deeper than `MAX_ENCODING_DEPTH` should stop recursing instead
/// of walking arbitrarily deep trees.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_depth_limit_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::depth_limit#0");
    encoder
        .get_or_declare_var("f", closure_sort)
        .expect("declare f with closure sort");

    let mut expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("st"), var("r")],
    );
    for _ in 0..=crate::encoder::MAX_ENCODING_DEPTH {
        expr = PureExpr::BinOp(Arc::new(PureExpr::Bool(true)), BinOp::And, Arc::new(expr));
    }

    let result = encoder.find_postcondition_mut_receiver_sort("st", &expr);
    assert!(
        result.is_none(),
        "receiver-sort walker should stop at MAX_ENCODING_DEPTH"
    );
}
