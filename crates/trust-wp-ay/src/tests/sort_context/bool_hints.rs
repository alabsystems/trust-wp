// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Helper: collect only Bool var names (ignoring fn names) for backwards
/// compatibility with existing tests. (#564)
pub(crate) fn collect_bool_var_names(expr: &PureExpr, names: &mut HashSet<String>) {
    let mut fn_names = HashSet::new();
    collect_bool_hints(expr, names, &mut fn_names);
}

// collect_bool_var_names tests
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_not_operand() {
    // !x => x is Bool
    let expr = not(var("x"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Not operand should be Bool");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_and_operands() {
    // x && y => both are Bool
    let expr = and(var("x"), var("y"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"));
    assert!(names.contains("y"));
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_or_operands() {
    // x || y => both are Bool
    let expr = or(var("x"), var("y"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"));
    assert!(names.contains("y"));
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_implies_operands() {
    // x ==> y => both are Bool
    let expr = implies(var("x"), var("y"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"));
    assert!(names.contains("y"));
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_eq_with_bool_literal() {
    // x == true => x is Bool
    let expr = eq(var("x"), bool_expr(true));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Eq with Bool literal should propagate");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_ne_with_bool_literal() {
    // x != false => x is Bool
    let expr = ne(var("x"), bool_expr(false));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Ne with Bool literal should propagate");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_ite_condition() {
    // if x then 1 else 2 => x is Bool (condition always Bool)
    let expr = ite(var("x"), int(1), int(2));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Ite condition should be Bool");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_ite_branch_propagation() {
    // if true then x else false => x is Bool (branch propagation from Bool literal)
    let expr = ite(bool_expr(true), var("x"), bool_expr(false));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Ite branch opposite Bool literal should propagate"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_arithmetic_no_propagation() {
    // x + y => neither is Bool
    let expr = add(var("x"), var("y"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.is_empty(), "Arithmetic operands should not be Bool");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_old() {
    // !(old(x)) => recurses through Old to find x in Not context
    let expr = not(old(var("x")));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Not(Old(Var)) should find x as Bool");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_deref() {
    // !(*x) => recurses through Deref to find x in Not context
    let expr = not(deref(var("x")));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Not(Deref(Var)) should find x as Bool");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_final() {
    // !(^x) => recurses through Final to find x in Not context
    let expr = not(final_expr(var("x")));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"), "Not(Final(Var)) should find x as Bool");
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_forall() {
    // forall i. !(x) => x is Bool inside quantifier body
    let body = not(var("x"));
    let expr = forall("i", body);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside forall body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_exists() {
    // exists i. x && y => both Bool inside quantifier body
    let body = and(var("x"), var("y"));
    let expr = exists("i", body);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(names.contains("x"));
    assert!(names.contains("y"));
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_method_call() {
    // receiver.method(!x) => x is Bool (inside method call args)
    let expr = method_call(var("r"), "some_method", vec![not(var("x"))]);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside method call arg should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_logic_fn_call() {
    // my_fn(!x) => x is Bool (inside logic fn args)
    let expr = logic_fn_call("my_fn", vec![not(var("x"))]);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside logic fn arg should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_let_value() {
    // let b = !x in b => x is Bool (inside Let value)
    let expr = let_bind("b", not(var("x")), var("b"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside Let value should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_let_body() {
    // let b = 0 in !x => x is Bool (inside Let body)
    let expr = let_bind("b", int(0), not(var("x")));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside Let body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_leaf_exprs_empty() {
    // Leaf expressions (Var, Int, Bool) produce no Bool names from themselves
    // (Var only becomes Bool when in a Bool-requiring context)
    for expr in [var("x"), int(42), bool_expr(true)] {
        let mut names = HashSet::new();
        collect_bool_var_names(&expr, &mut names);
        assert!(
            names.is_empty(),
            "Bare leaf expr should not self-identify as Bool"
        );
    }
}

// =============================================================================
