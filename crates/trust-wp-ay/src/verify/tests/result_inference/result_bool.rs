// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;

use crate::{
    tests::helpers::{bool_expr, eq, int, logic_fn_call, var},
    verify::{result_is_bool_by_postcondition, result_is_bool_by_postcondition_with_context},
    AYEncoder, BinOp,
};

#[test]
#[timeout(30000)]
fn empty_ensures_does_not_require_bool() {
    assert!(
        !result_is_bool_by_postcondition(&[]),
        "empty ensures should not require bool return type"
    );
}

#[test]
#[timeout(30000)]
fn single_bare_result_ensures() {
    assert!(
        result_is_bool_by_postcondition(&[crate::tests::helpers::var("result")]),
        "single bare `result` postcondition should require bool"
    );
}

#[test]
#[timeout(30000)]
fn mixed_ensures_one_requires_bool() {
    let ensures = vec![
        crate::tests::helpers::binop(crate::tests::helpers::var("result"), BinOp::Gt, int(0)),
        crate::tests::helpers::binop(
            crate::tests::helpers::var("result"),
            BinOp::Eq,
            bool_expr(true),
        ),
    ];
    assert!(
        result_is_bool_by_postcondition(&ensures),
        "mixed ensures with one bool-requiring clause should return true"
    );
}

#[test]
#[timeout(30000)]
fn no_result_mentions_does_not_require_bool() {
    let ensures = vec![
        crate::tests::helpers::binop(crate::tests::helpers::var("x"), BinOp::Gt, int(0)),
        crate::tests::helpers::binop(crate::tests::helpers::var("y"), BinOp::Eq, int(1)),
    ];
    assert!(
        !result_is_bool_by_postcondition(&ensures),
        "ensures with no result mentions should not require bool"
    );
}

#[test]
#[timeout(30000)]
fn context_aware_bool_postcondition_uses_declared_logic_fn_range() {
    let mut encoder = AYEncoder::new();
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_pred");
    let func_decl = encoder
        .solver
        .declare_fun(&smt_name, &[Sort::Int], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, func_decl);

    let ensures = vec![eq(var("result"), logic_fn_call("my_pred", vec![int(1)]))];
    assert!(
        !result_is_bool_by_postcondition(&ensures),
        "context-free helper should stay conservative when the Bool range is only available via encoder state"
    );
    assert!(
        result_is_bool_by_postcondition_with_context(&mut encoder, &ensures),
        "context-aware helper should use declared Bool logic-fn ranges"
    );
}
