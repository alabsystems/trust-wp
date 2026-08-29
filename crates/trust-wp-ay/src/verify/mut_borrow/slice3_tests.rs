// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::verify_mut_borrow_function_with_modes;
use crate::{
    tests::helpers::{
        add, bool_expr, eq, forall, get_field, gt, int, ite, method_call, var, var_with_sort, view,
    },
    verify::types::MutBorrowRequest,
    VerificationResult,
};

/// Gap 5 regression (#2365): mut_borrow must propagate SeqValue from the body
/// view chain to `result_view` for Seq-valued return expressions.
#[test]
#[timeout(15000)]
fn test_mut_borrow_seq_push_back_chain_len_via_result_view() {
    let final_values = HashMap::new();
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let push1 = method_call(empty, "push_back", vec![int(0)]);
    let push2 = method_call(push1, "push_back", vec![int(1)]);
    let ensures = vec![eq(method_call(view(var("result")), "len", vec![]), int(2))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&push2)),
    )
    .expect("push-back chain verification should not error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "push-back chain len via result@ should verify in mut_borrow: {result:?}"
    );
}

/// Gap 4 regression (#2365): non-variable mut_borrow result bodies must rebind
/// `result` so postconditions can match aliased ITE terms directly.
#[test]
#[timeout(30000)]
fn test_mut_borrow_ite_result_rebinds_for_alias_postcondition() {
    let final_values = HashMap::new();
    let cond = var_with_sort("cond", ExprSort::Bool);
    let body = ite(cond, int(1), int(0));
    let ghost = vec![eq(var("expected"), body.clone())];
    let ensures = vec![eq(var("result"), var("expected"))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .ghost_context(Some(&ghost))
            .return_expr(Some(&body)),
    )
    .expect("ITE alias verification should not error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ITE result alias postcondition should verify after rebind: {result:?}"
    );
}

/// Gap 3 regression (#2365): mut_borrow must assert container element
/// invariants when the preconditions mention a container invariant receiver.
#[test]
#[timeout(30000)]
fn test_mut_borrow_vec_element_invariant_propagation() {
    let final_values = HashMap::new();
    let sumto10_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");
    let vec_method = trust_wp_core::logic::type_invariant_method_name("Vec");

    let sumto10_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: eq(
            add(get_field(0, var("self")), get_field(1, var("self"))),
            int(10),
        ),
        is_newtype: false,
        element_invariant_method: None,
    };

    let vec_def = trust_wp_core::type_invariant_def! {
        type_name: "Vec".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: Some(sumto10_method.clone()),
    };

    let requires = vec![
        gt(method_call(view(var("x")), "len", vec![]), int(0)),
        method_call(var("x"), &vec_method, vec![]),
    ];
    let elem_0 = method_call(view(var("x")), "index_logic", vec![int(0)]);
    let ensures = vec![eq(
        add(get_field(0, elem_0.clone()), get_field(1, elem_0)),
        int(10),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .type_invariants(Some(&[sumto10_def, vec_def])),
    )
    .expect("Vec element invariant encoding should not error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Vec<SumTo10> element invariant propagation should verify in mut_borrow: {result:?}"
    );
}

/// Gap 6 regression (#2365): axiom-only mut_borrow contracts should short-cut
/// to `Assumed` instead of reaching quantifier handling and returning Unknown.
#[test]
#[timeout(30000)]
fn test_mut_borrow_axiom_only_forall_none_body_assumed() {
    let final_values = HashMap::new();
    let ensures = vec![forall("x", gt(method_call(var("x"), "f", vec![]), int(0)))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("axiom-only mut_borrow encoding should not error");

    assert!(
        matches!(result, VerificationResult::Assumed(_)),
        "axiom-only mut_borrow contract should be Assumed: {result:?}"
    );
}
