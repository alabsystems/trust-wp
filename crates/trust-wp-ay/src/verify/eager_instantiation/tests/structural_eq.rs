// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(5000)]
fn structural_eq_vars_same_name_no_sort() {
    assert!(exprs_structurally_equal(&var("x"), &var("x")));
}

#[test]
#[timeout(5000)]
fn structural_eq_vars_different_name() {
    assert!(!exprs_structurally_equal(&var("x"), &var("y")));
}

#[test]
#[timeout(5000)]
fn structural_eq_vars_ignores_sort_annotation() {
    // Core invariant: Var("x", Some(Int)) == Var("x", None)
    let a = var_with_sort("x", ExprSort::Int);
    let b = var("x");
    assert!(exprs_structurally_equal(&a, &b));
    assert!(exprs_structurally_equal(&b, &a));
}

#[test]
#[timeout(5000)]
fn structural_eq_vars_different_sorts_same_name() {
    let a = var_with_sort("x", ExprSort::Int);
    let b = var_with_sort("x", ExprSort::Bool);
    assert!(exprs_structurally_equal(&a, &b));
}

#[test]
#[timeout(5000)]
fn structural_eq_int_literals() {
    assert!(exprs_structurally_equal(&int(42), &int(42)));
    assert!(!exprs_structurally_equal(&int(42), &int(43)));
}

#[test]
#[timeout(5000)]
fn structural_eq_bool_literals() {
    assert!(exprs_structurally_equal(&bool_expr(true), &bool_expr(true)));
    assert!(!exprs_structurally_equal(
        &bool_expr(true),
        &bool_expr(false)
    ));
}

#[test]
#[timeout(5000)]
fn structural_eq_different_variants() {
    assert!(!exprs_structurally_equal(&int(1), &var("x")));
    assert!(!exprs_structurally_equal(&bool_expr(true), &int(1)));
}

#[test]
#[timeout(5000)]
fn structural_eq_binop() {
    let a = add(var("x"), int(1));
    let b = add(var("x"), int(1));
    assert!(exprs_structurally_equal(&a, &b));

    // Different operand
    let c = add(var("y"), int(1));
    assert!(!exprs_structurally_equal(&a, &c));

    // Different operator
    let d = sub(var("x"), int(1));
    assert!(!exprs_structurally_equal(&a, &d));
}

#[test]
#[timeout(5000)]
fn structural_eq_binop_ignores_var_sorts_in_operands() {
    let a = add(var_with_sort("x", ExprSort::Int), int(1));
    let b = add(var("x"), int(1));
    assert!(exprs_structurally_equal(&a, &b));
}

#[test]
#[timeout(5000)]
fn structural_eq_unop() {
    let a = not(var("x"));
    let b = not(var("x"));
    assert!(exprs_structurally_equal(&a, &b));

    let c = neg(var("x"));
    assert!(!exprs_structurally_equal(&a, &c));
}

#[test]
#[timeout(5000)]
fn structural_eq_method_call() {
    let a = method_call(var("v"), "len", vec![]);
    let b = method_call(var("v"), "len", vec![]);
    assert!(exprs_structurally_equal(&a, &b));

    let c = method_call(var("v"), "push", vec![int(1)]);
    assert!(!exprs_structurally_equal(&a, &c));
}

#[test]
#[timeout(5000)]
fn structural_eq_logic_fn_call() {
    let a = logic_fn_call("resolve", vec![var("x")]);
    let b = logic_fn_call("resolve", vec![var("x")]);
    assert!(exprs_structurally_equal(&a, &b));

    let c = logic_fn_call("resolve", vec![var("y")]);
    assert!(!exprs_structurally_equal(&a, &c));
}

#[test]
#[timeout(5000)]
fn structural_eq_ite() {
    let a = ite(bool_expr(true), int(1), int(2));
    let b = ite(bool_expr(true), int(1), int(2));
    assert!(exprs_structurally_equal(&a, &b));

    let c = ite(bool_expr(false), int(1), int(2));
    assert!(!exprs_structurally_equal(&a, &c));
}

#[test]
#[timeout(5000)]
fn structural_eq_wrappers() {
    assert!(exprs_structurally_equal(&old(var("x")), &old(var("x"))));
    assert!(!exprs_structurally_equal(&old(var("x")), &old(var("y"))));
    assert!(exprs_structurally_equal(&deref(var("x")), &deref(var("x"))));
    assert!(exprs_structurally_equal(
        &final_expr(var("x")),
        &final_expr(var("x"))
    ));
    assert!(exprs_structurally_equal(&view(var("x")), &view(var("x"))));
}

#[test]
#[timeout(5000)]
fn structural_eq_forall() {
    let a = forall("x", gt(var("x"), int(0)));
    let b = forall("x", gt(var("x"), int(0)));
    assert!(exprs_structurally_equal(&a, &b));

    let c = forall("y", gt(var("y"), int(0)));
    assert!(!exprs_structurally_equal(&a, &c));
}

#[test]
#[timeout(5000)]
fn structural_eq_exists() {
    let a = exists("x", gt(var("x"), int(0)));
    let b = exists("x", gt(var("x"), int(0)));
    assert!(exprs_structurally_equal(&a, &b));
}

#[test]
#[timeout(5000)]
fn structural_eq_let() {
    let a = let_bind("x", int(1), add(var("x"), int(2)));
    let b = let_bind("x", int(1), add(var("x"), int(2)));
    assert!(exprs_structurally_equal(&a, &b));
}

#[test]
#[timeout(5000)]
fn structural_eq_let_assume() {
    let a = let_assume(bool_expr(true), var("x"));
    let b = let_assume(bool_expr(true), var("x"));
    assert!(exprs_structurally_equal(&a, &b));
}

#[test]
#[timeout(5000)]
fn structural_eq_let_obligation() {
    let a = let_obligation(bool_expr(true), var("x"));
    let b = let_obligation(bool_expr(true), var("x"));
    assert!(exprs_structurally_equal(&a, &b));
}

#[test]
#[timeout(5000)]
fn structural_eq_closure() {
    let a = PureExpr::Closure {
        params: vec![("a".to_string(), None)],
        body: Arc::new(var("a")),
    };
    let b = PureExpr::Closure {
        params: vec![("a".to_string(), None)],
        body: Arc::new(var("a")),
    };
    assert!(exprs_structurally_equal(&a, &b));
}
