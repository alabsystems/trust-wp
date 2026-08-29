// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use crate::{
    tests::helpers::{
        binop, bool_expr, forall, int, let_assume, method_call, named_field, old, var,
    },
    verify::expr_requires_result_bool,
    BinOp, PureExpr, UnOp,
};

// --- expr_requires_result_bool ---

#[test]
#[timeout(30000)]
fn bare_result_requires_bool() {
    // `result` as a bare postcondition means the function returns bool
    assert!(
        expr_requires_result_bool(&var("result")),
        "bare `result` var should require bool return type"
    );
}

#[test]
#[timeout(30000)]
fn bare_non_result_does_not_require_bool() {
    assert!(
        !expr_requires_result_bool(&var("x")),
        "non-result var `x` should not require bool"
    );
}

#[test]
#[timeout(30000)]
fn not_result_requires_bool() {
    // `!result` — result must be bool
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(var("result")));
    assert!(
        expr_requires_result_bool(&expr),
        "`!result` should require bool return type"
    );
}

#[test]
#[timeout(30000)]
fn not_non_result_does_not_require_bool() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(var("x")));
    assert!(
        !expr_requires_result_bool(&expr),
        "`!x` (no result var) should not require bool"
    );
}

#[test]
#[timeout(30000)]
fn result_eq_true_requires_bool() {
    // `result == true`
    let expr = binop(var("result"), BinOp::Eq, bool_expr(true));
    assert!(
        expr_requires_result_bool(&expr),
        "`result == true` should require bool return type"
    );
}

#[test]
#[timeout(30000)]
fn result_ne_false_requires_bool() {
    // `result != false`
    let expr = binop(var("result"), BinOp::Ne, bool_expr(false));
    assert!(
        expr_requires_result_bool(&expr),
        "`result != false` should require bool return type"
    );
}

#[test]
#[timeout(30000)]
fn result_eq_int_does_not_require_bool() {
    // `result == 42` — RHS is Int, so result is Int, not Bool
    let expr = binop(var("result"), BinOp::Eq, int(42));
    assert!(
        !expr_requires_result_bool(&expr),
        "`result == 42` should not require bool (Int comparison)"
    );
}

#[test]
#[timeout(30000)]
fn field_accessor_result_eq_true_does_not_require_bool() {
    let expr = binop(
        named_field("flag", var("result")),
        BinOp::Eq,
        bool_expr(true),
    );
    assert!(
        !expr_requires_result_bool(&expr),
        "field accessor equality should constrain the accessor return sort, not `result`"
    );
}

#[test]
#[timeout(30000)]
fn result_gt_does_not_require_bool() {
    // `result > 0` — comparison, not Bool sort evidence
    let expr = binop(var("result"), BinOp::Gt, int(0));
    assert!(
        !expr_requires_result_bool(&expr),
        "`result > 0` is a comparison, not Bool sort evidence"
    );
}

#[test]
#[timeout(30000)]
fn and_connector_recurses() {
    // `result && x` — And is a logical connector, recurse into both sides
    let expr = binop(var("result"), BinOp::And, var("x"));
    assert!(
        expr_requires_result_bool(&expr),
        "`result && x` should recurse through And and find result"
    );
}

#[test]
#[timeout(30000)]
fn or_with_no_result_does_not_require_bool() {
    let expr = binop(var("x"), BinOp::Or, var("y"));
    assert!(
        !expr_requires_result_bool(&expr),
        "`x || y` has no result var, should not require bool"
    );
}

#[test]
#[timeout(30000)]
fn implies_with_result_in_rhs_requires_bool() {
    // `x ==> result`
    let expr = binop(var("x"), BinOp::Implies, var("result"));
    assert!(
        expr_requires_result_bool(&expr),
        "`x ==> result` should require bool for result in RHS"
    );
}

#[test]
#[timeout(30000)]
fn ite_result_in_condition_requires_bool() {
    // `if result then 1 else 0` — result is the condition, so must be Bool
    let expr = PureExpr::Ite(Arc::new(var("result")), Arc::new(int(1)), Arc::new(int(0)));
    assert!(
        expr_requires_result_bool(&expr),
        "`if result then 1 else 0` — result as condition requires bool"
    );
}

#[test]
#[timeout(30000)]
fn ite_result_only_in_branch_does_not_require_bool() {
    // `if true then result else 0` — result is in a branch, not condition
    let expr = PureExpr::Ite(
        Arc::new(bool_expr(true)),
        Arc::new(var("result")),
        Arc::new(int(0)),
    );
    assert!(
        !expr_requires_result_bool(&expr),
        "result in branch (not condition) should not require bool"
    );
}

#[test]
#[timeout(30000)]
fn nested_and_with_result_eq_true() {
    // `x && (result == true)` — And recurses, finds result == true in RHS
    let inner = binop(var("result"), BinOp::Eq, bool_expr(true));
    let expr = binop(var("x"), BinOp::And, inner);
    assert!(
        expr_requires_result_bool(&expr),
        "nested And should recurse and find `result == true` in RHS"
    );
}

#[test]
#[timeout(30000)]
fn forall_result_eq_bool_expr_requires_bool() {
    let expr = forall(
        "x",
        binop(var("result"), BinOp::Eq, binop(var("x"), BinOp::Gt, int(0))),
    );
    assert!(
        expr_requires_result_bool(&expr),
        "Bool equality inside a quantifier body should force `result` to Bool"
    );
}

#[test]
#[timeout(30000)]
fn old_wrapper_preserves_result_bool_context() {
    let expr = old(binop(var("result"), BinOp::Eq, bool_expr(true)));
    assert!(
        expr_requires_result_bool(&expr),
        "sort-preserving wrappers should recurse into Bool result evidence"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_body_preserves_contains_bool_context() {
    let expr = let_assume(
        bool_expr(true),
        binop(
            var("result"),
            BinOp::Eq,
            method_call(var("xs"), "contains", vec![int(1)]),
        ),
    );
    assert!(
        expr_requires_result_bool(&expr),
        "Bool-returning method calls inside LetAssume bodies should force `result` to Bool"
    );
}

mod result_bool;
mod result_contains;
mod result_datatype;
