// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use super::*;
use crate::encoder::quantifier_ctor_elim::arg_is_any_qvar_reference;

/// `arg_is_any_qvar_reference` with nested wrappers: Deref(Old(View(Var("k")))).
#[test]
#[timeout(30000)]
fn test_any_qvar_ref_nested_deep_wrappers() {
    let qvars: HashSet<&str> = ["k", "v"].into_iter().collect();
    let expr = deref(old(view(var("k"))));
    assert_eq!(
        arg_is_any_qvar_reference(&expr, &qvars),
        Some("k"),
        "deeply nested wrappers should unwrap to find qvar"
    );
}

/// `arg_is_any_qvar_reference` with Final(Var).
#[test]
#[timeout(30000)]
fn test_any_qvar_ref_through_final() {
    let qvars: HashSet<&str> = ["v"].into_iter().collect();
    let expr = final_expr(var("v"));
    assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), Some("v"),);
}

/// `arg_is_any_qvar_reference` with LogicFnCall returns None (not a variable).
#[test]
#[timeout(30000)]
fn test_any_qvar_ref_logic_fn_call_returns_none() {
    let qvars: HashSet<&str> = ["v"].into_iter().collect();
    let expr = logic_fn_call("Some", vec![var("v")]);
    assert_eq!(
        arg_is_any_qvar_reference(&expr, &qvars),
        None,
        "LogicFnCall is not a variable reference"
    );
}

/// `arg_is_any_qvar_reference` with BinOp returns None.
#[test]
#[timeout(30000)]
fn test_any_qvar_ref_binop_returns_none() {
    let qvars: HashSet<&str> = ["v"].into_iter().collect();
    let expr = add(var("v"), int(1));
    assert_eq!(
        arg_is_any_qvar_reference(&expr, &qvars),
        None,
        "BinOp is not a variable reference"
    );
}
