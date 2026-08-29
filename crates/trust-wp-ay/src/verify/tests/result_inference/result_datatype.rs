// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;

use crate::{
    encoder::match_enc::MatchDatatypeKind,
    tests::helpers::{
        binop, bool_expr, deref, eq, exists, forall, int, let_assume, let_bind, logic_fn_call,
        match_expr, method_call, old, var, var_with_sort, view,
    },
    verify::{
        expr_match_datatype_for_result, option_datatype_from_constructor_expr,
        result_match_datatype_from_postcondition,
    },
    BinOp, ExprSort, Pattern, PureExpr,
};

fn some_pattern(inner: Pattern) -> Pattern {
    Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(inner)),
    }
}

fn none_pattern() -> Pattern {
    Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    }
}

fn ok_pattern(inner: Pattern) -> Pattern {
    Pattern::Constructor {
        name: "Ok".to_string(),
        inner: Some(Box::new(inner)),
    }
}

fn err_pattern(inner: Pattern) -> Pattern {
    Pattern::Constructor {
        name: "Err".to_string(),
        inner: Some(Box::new(inner)),
    }
}

#[test]
#[timeout(30000)]
fn result_var_in_option_match_returns_option_int() {
    let expr = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("x".to_string())), var("x")),
            (none_pattern(), int(0)),
        ],
    );
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_var_in_result_match_returns_result_int_int() {
    let expr = match_expr(
        var("result"),
        vec![
            (ok_pattern(Pattern::Binding("x".to_string())), var("x")),
            (err_pattern(Pattern::Binding("e".to_string())), int(0)),
        ],
    );
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::ResultIntInt)
    );
}

#[test]
#[timeout(30000)]
fn option_match_on_non_result_returns_none() {
    let expr = match_expr(
        var("x"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        None,
        "match on non-result var should not detect datatype"
    );
}

#[test]
#[timeout(30000)]
fn option_and_result_mixed_returns_none() {
    let expr = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("x".to_string())), var("x")),
            (err_pattern(Pattern::Binding("e".to_string())), int(0)),
        ],
    );
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        None,
        "mixed Option/Result arms should not match"
    );
}

#[test]
#[timeout(30000)]
fn nested_option_match_in_binop() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = binop(m, BinOp::Gt, int(0));
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
        "match nested in BinOp should still be detected"
    );
}

#[test]
#[timeout(30000)]
fn option_match_in_ite_condition() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = PureExpr::Ite(Arc::new(bool_expr(true)), Arc::new(m), Arc::new(int(0)));
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
        "match in Ite branch should still be detected"
    );
}

#[test]
#[timeout(30000)]
fn result_match_in_unop() {
    let m = match_expr(
        var("result"),
        vec![
            (ok_pattern(Pattern::Binding("v".to_string())), var("v")),
            (err_pattern(Pattern::Wildcard), int(0)),
        ],
    );
    let expr = PureExpr::UnOp(crate::UnOp::Not, Arc::new(binop(m, BinOp::Eq, int(0))));
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::ResultIntInt),
        "match inside UnOp should be detected"
    );
}

#[test]
#[timeout(30000)]
fn option_match_with_literal_pattern_returns_none() {
    let expr = match_expr(
        var("result"),
        vec![
            (
                some_pattern(Pattern::Literal(bool_expr(true))),
                bool_expr(true),
            ),
            (none_pattern(), bool_expr(false)),
        ],
    );
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
    );
}

#[test]
#[timeout(30000)]
fn option_match_inside_old_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = old(m);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
        "match inside old() should be detected"
    );
}

#[test]
#[timeout(30000)]
fn result_match_inside_exists_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (ok_pattern(Pattern::Binding("v".to_string())), var("v")),
            (err_pattern(Pattern::Wildcard), int(-1)),
        ],
    );
    let expr = exists("w", m);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::ResultIntInt),
        "match inside exists should be detected"
    );
}

#[test]
#[timeout(30000)]
fn option_match_inside_deref_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = deref(m);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
        "match inside deref should be detected"
    );
}

#[test]
#[timeout(30000)]
fn option_match_inside_view_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = view(m);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
        "match inside view should be detected"
    );
}

#[test]
#[timeout(30000)]
fn no_match_on_bare_result_returns_none() {
    assert_eq!(expr_match_datatype_for_result(&var("result")), None);
}

#[test]
#[timeout(30000)]
fn int_literal_returns_none() {
    assert_eq!(expr_match_datatype_for_result(&int(42)), None);
}

#[test]
#[timeout(30000)]
fn empty_ensures_no_match_datatype() {
    assert_eq!(result_match_datatype_from_postcondition(&[]), None);
}

#[test]
#[timeout(30000)]
fn ensures_with_option_match() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    assert_eq!(
        result_match_datatype_from_postcondition(&[m]),
        Some(MatchDatatypeKind::OptionInt),
    );
}

#[test]
#[timeout(30000)]
fn ensures_second_clause_has_match() {
    let plain = binop(var("x"), BinOp::Gt, int(0));
    let m = match_expr(
        var("result"),
        vec![
            (ok_pattern(Pattern::Binding("v".to_string())), var("v")),
            (err_pattern(Pattern::Wildcard), int(0)),
        ],
    );
    assert_eq!(
        result_match_datatype_from_postcondition(&[plain, m]),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

#[test]
#[timeout(30000)]
fn ensures_no_match_at_all() {
    let ensures = vec![
        binop(var("result"), BinOp::Gt, int(0)),
        binop(var("x"), BinOp::Eq, int(1)),
    ];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

#[test]
#[timeout(30000)]
fn ensures_with_result_eq_option_constructors() {
    let ensures = vec![binop(
        eq(var("result"), logic_fn_call("Some", vec![int(1)])),
        BinOp::Or,
        eq(var("result"), logic_fn_call("None", vec![])),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

#[test]
#[timeout(30000)]
fn ensures_with_result_eq_some_user_constructor_payload() {
    let ensures = vec![
        eq(var("result"), logic_fn_call("None", vec![])),
        eq(
            var("result"),
            logic_fn_call(
                "Some",
                vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
            ),
        ),
    ];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionPayload(Sort::Uninterpreted(
            "OwnResult".to_string()
        ))),
    );
}

#[test]
#[timeout(30000)]
fn tuple_body_with_nested_option_field_does_not_force_option_result() {
    let tuple_body = logic_fn_call(
        "__trust_wp_tuple2",
        vec![
            var_with_sort("s", ExprSort::Seq),
            logic_fn_call("Some", vec![var_with_sort("s", ExprSort::Seq)]),
        ],
    );
    assert_eq!(option_datatype_from_constructor_expr(&tuple_body), None);
}

#[test]
#[timeout(30000)]
fn ensures_with_result_eq_result_constructors() {
    let ensures = vec![binop(
        eq(var("result"), logic_fn_call("Ok", vec![int(1)])),
        BinOp::Or,
        eq(var("result"), logic_fn_call("Err", vec![int(0)])),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

#[test]
#[timeout(30000)]
fn ensures_with_conflicting_constructor_families_returns_none() {
    let ensures = vec![binop(
        eq(var("result"), logic_fn_call("Some", vec![int(1)])),
        BinOp::And,
        eq(var("result"), logic_fn_call("Ok", vec![int(1)])),
    )];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

#[test]
#[timeout(30000)]
fn result_match_inside_forall_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (
                some_pattern(Pattern::Binding("v".to_string())),
                binop(var("v"), BinOp::Gt, var("x")),
            ),
            (none_pattern(), bool_expr(true)),
        ],
    );
    let expr = forall("x", m);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_inside_let_assume_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = let_assume(bool_expr(true), m);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_inside_closure_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (
                some_pattern(Pattern::Binding("v".to_string())),
                binop(var("v"), BinOp::Gt, var("x")),
            ),
            (none_pattern(), bool_expr(true)),
        ],
    );
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), Some(ExprSort::Int))],
        body: Arc::new(m),
    };
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_inside_let_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = let_bind("tmp", m, binop(var("tmp"), BinOp::Gt, int(0)));
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_inside_method_call_detected() {
    let m = match_expr(
        var("result"),
        vec![
            (some_pattern(Pattern::Binding("v".to_string())), var("v")),
            (none_pattern(), int(0)),
        ],
    );
    let expr = method_call(var("receiver"), "some_method", vec![m]);
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt)
    );
}
