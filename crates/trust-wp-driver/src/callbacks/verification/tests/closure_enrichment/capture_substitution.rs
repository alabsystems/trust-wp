// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::closure_enrichment::substitute_captures_inline;

// ── substitute_captures_inline tests ──────────────────────────────────

#[test]
fn substitute_captures_inline_replaces_capture_with_tuple_field_projection() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string()), (1, "y".to_string())];
    let pre_state = PureExpr::Var("pre".to_string(), None);
    let post_state = PureExpr::Var("post".to_string(), None);
    let result_expr = PureExpr::Int(42);

    // Input: x + y (both are captured variables)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("y".to_string(), None)),
    );

    let result = substitute_captures_inline(
        &expr,
        &capture_bindings,
        &pre_state,
        &post_state,
        &result_expr,
        false, // not inside old
    );

    // Outside old(): captures project from post_state
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![post_state.clone()],
        }),
        BinOp::Add,
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![post_state.clone()],
        }),
    );
    assert_eq!(
        result, expected,
        "captures outside old() should project from post_state"
    );
}

#[test]
fn substitute_captures_inline_old_projects_from_pre_state() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string())];
    let pre_state = PureExpr::Var("pre".to_string(), None);
    let post_state = PureExpr::Var("post".to_string(), None);
    let result_expr = PureExpr::Int(0);

    // Input: old(x) — capture "x" inside Old wrapper
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));

    let result = substitute_captures_inline(
        &expr,
        &capture_bindings,
        &pre_state,
        &post_state,
        &result_expr,
        false,
    );

    // old(capture) should strip the Old wrapper and project from pre_state
    let expected = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![pre_state.clone()],
    };
    assert_eq!(
        result, expected,
        "old(capture) should project from pre_state and strip Old wrapper"
    );
}

#[test]
fn substitute_captures_inline_replaces_result_and_leaves_unbound_vars() {
    let capture_bindings = vec![(0, "x".to_string())];
    let pre_state = PureExpr::Var("pre".to_string(), None);
    let post_state = PureExpr::Var("post".to_string(), None);
    let result_expr = PureExpr::Var("ret_val".to_string(), None);

    // Input: result == z (result is keyword, z is unbound)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("z".to_string(), None)),
    );

    let result = substitute_captures_inline(
        &expr,
        &capture_bindings,
        &pre_state,
        &post_state,
        &result_expr,
        false,
    );

    // "result" → result_expr, "z" unchanged (not a capture)
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("ret_val".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("z".to_string(), None)),
    );
    assert_eq!(
        result, expected,
        "result keyword should be replaced; unbound vars should pass through"
    );
}

#[test]
fn substitute_captures_inline_normalizes_result_replacement_views() {
    let capture_bindings: Vec<(usize, String)> = vec![];
    let pre_state = PureExpr::Var("pre".to_string(), None);
    let post_state = PureExpr::Var("post".to_string(), None);
    let result_expr = PureExpr::View(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "xs".to_string(),
        None,
    )))));

    let expr = PureExpr::Var("result".to_string(), None);

    let result = substitute_captures_inline(
        &expr,
        &capture_bindings,
        &pre_state,
        &post_state,
        &result_expr,
        false,
    );

    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::Var("xs".to_string(), None))),
        "result substitution should collapse redundant nested views before downstream sort inference"
    );
}

#[test]
fn substitute_captures_inline_collapses_nested_views_around_result() {
    let capture_bindings: Vec<(usize, String)> = vec![];
    let pre_state = PureExpr::Var("pre".to_string(), None);
    let post_state = PureExpr::Var("post".to_string(), None);
    let result_expr = PureExpr::View(Arc::new(PureExpr::Var("xs".to_string(), None)));

    let expr = PureExpr::View(Arc::new(PureExpr::Var("result".to_string(), None)));

    let result = substitute_captures_inline(
        &expr,
        &capture_bindings,
        &pre_state,
        &post_state,
        &result_expr,
        false,
    );

    assert_eq!(
        result, result_expr,
        "view(result) should not grow a nested view when result is already view-shaped"
    );
}

// ── substitute_captures_inline edge case tests ─────────────────────────

#[test]
fn substitute_captures_inline_empty_captures_passes_through() {
    let capture_bindings: Vec<(usize, String)> = vec![];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::Var("x".to_string(), None);
    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);
    assert_eq!(
        result, expr,
        "non-captured var with empty bindings should pass through"
    );
}

#[test]
fn substitute_captures_inline_literal_passthrough() {
    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let bool_expr = PureExpr::Bool(true);
    let int_expr = PureExpr::Int(42);

    assert_eq!(
        substitute_captures_inline(&bool_expr, &capture_bindings, &pre, &post, &res, false),
        bool_expr,
        "Bool literals should pass through unchanged"
    );
    assert_eq!(
        substitute_captures_inline(&int_expr, &capture_bindings, &pre, &post, &res, false),
        int_expr,
        "Int literals should pass through unchanged"
    );
}

#[test]
fn substitute_captures_inline_ite_traverses_all_branches() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        Arc::new(PureExpr::Var("x".to_string(), None)),
        Arc::new(PureExpr::Int(0)),
    );

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let proj = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![post.clone()],
    };
    let expected = PureExpr::Ite(
        Arc::new(proj.clone()),
        Arc::new(proj),
        Arc::new(PureExpr::Int(0)),
    );
    assert_eq!(
        result, expected,
        "Ite should substitute in condition, then, and else branches"
    );
}

#[test]
fn substitute_captures_inline_unop_traverses_operand() {
    use trust_wp_core::formula::{internal::tuple_lowering::tuple_field_logic_fn_name, UnOp};

    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Var("x".to_string(), None)));

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);
    let expected = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![post.clone()],
        }),
    );
    assert_eq!(result, expected, "UnOp should substitute in operand");
}

#[test]
fn substitute_captures_inline_method_call_substitutes_receiver_and_args() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string()), (1, "y".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "foo".to_string(),
        args: vec![PureExpr::Var("y".to_string(), None)],
    };

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let expected = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![post.clone()],
        }),
        method: "foo".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![post.clone()],
        }],
    };
    assert_eq!(
        result, expected,
        "MethodCall should substitute in receiver and args"
    );
}

#[test]
fn substitute_captures_inline_forall_substitutes_body_and_triggers() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![vec![PureExpr::Var("x".to_string(), None)]],
    };

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let proj = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![post.clone()],
    };
    let expected = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(proj.clone()),
        triggers: vec![vec![proj]],
    };
    assert_eq!(
        result, expected,
        "Forall should substitute in body and trigger expressions"
    );
}

#[test]
fn substitute_captures_inline_let_substitutes_value_and_body() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(PureExpr::Var("x".to_string(), None)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let proj = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![post.clone()],
    };
    let expected = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(proj.clone()),
        body: Arc::new(proj),
    };
    assert_eq!(
        result, expected,
        "Let should substitute in both value and body"
    );
}

#[test]
fn substitute_captures_inline_nested_old_propagates_inside_old() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string()), (1, "y".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    // old(x + y): both captures inside old should project from pre_state
    let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("y".to_string(), None)),
    )));

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![pre.clone()],
        }),
        BinOp::Add,
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![pre.clone()],
        }),
    );
    assert_eq!(
        result, expected,
        "old(x + y) should strip Old wrapper and project both captures from pre_state"
    );
}

#[test]
fn substitute_captures_inline_old_without_captures_preserves_old() {
    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    // old(z) where z is NOT a capture — should preserve Old wrapper
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("z".to_string(), None)));

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let expected = PureExpr::Old(Arc::new(PureExpr::Var("z".to_string(), None)));
    assert_eq!(
        result, expected,
        "old(non_capture) should preserve the Old wrapper"
    );
}

#[test]
fn substitute_captures_inline_closure_body_substitutes() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let capture_bindings = vec![(0, "x".to_string())];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Int(0);

    let expr = PureExpr::Closure {
        params: vec![("a".to_string(), None)],
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };

    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, false);

    let expected = PureExpr::Closure {
        params: vec![("a".to_string(), None)],
        body: Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![post.clone()],
        }),
    };
    assert_eq!(
        result, expected,
        "Closure body should have captures substituted"
    );
}

#[test]
fn substitute_captures_inline_result_replaced_even_inside_old() {
    let capture_bindings: Vec<(usize, String)> = vec![];
    let pre = PureExpr::Var("pre".to_string(), None);
    let post = PureExpr::Var("post".to_string(), None);
    let res = PureExpr::Var("ret".to_string(), None);

    // "result" should be replaced regardless of inside_old flag
    let expr = PureExpr::Var("result".to_string(), None);
    let result = substitute_captures_inline(&expr, &capture_bindings, &pre, &post, &res, true);
    assert_eq!(
        result, res,
        "result keyword should be replaced even when inside_old=true"
    );
}
