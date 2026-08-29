// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

use super::verify_mut_borrow_function_with_modes;
use crate::{
    tests::helpers::{
        and, deref, eq, final_expr, forall_with_sort, implies, logic_fn_call, method_call, var,
        var_with_sort, view,
    },
    verify::types::MutBorrowRequest,
    VerificationResult,
};

/// Generic TypeParam regression for `vector/07_read_write.rs` (#2062).
///
/// The synthesized Phase 5 `.set(i, x)` final-state expression and the
/// synthesized point-write precondition both write `x: T` into the monomorphic
/// Seq backing array. They must bridge `T` through the Seq element coercion
/// layer instead of panicking in `store`.
#[test]
#[timeout(30000)]
fn test_index_mut_intermediate_state_type_param_encodes_without_store_mismatch() {
    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let x_expr = var_with_sort("x", t_sort.clone());
    let i_view = view(var("i"));

    let intermediate_state = method_call(
        view(deref(var("a"))),
        "set",
        vec![i_view.clone(), x_expr.clone()],
    );

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), intermediate_state);

    let a_ref = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let final_view = view(final_expr(a_ref.clone()));
    let current_view = view(deref(a_ref));
    let final_at_i = method_call(final_view.clone(), "index_logic", vec![i_view.clone()]);

    let requires = vec![
        PureExpr::BinOp(
            Arc::new(i_view.clone()),
            BinOp::Lt,
            Arc::new(method_call(current_view.clone(), "len", vec![])),
        ),
        eq(final_at_i.clone(), x_expr.clone()),
        eq(
            method_call(final_view.clone(), "len", vec![]),
            method_call(current_view, "len", vec![]),
        ),
    ];
    let ensures = vec![eq(final_at_i, x_expr)];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ));

    assert!(
        result.is_ok(),
        "generic IndexMut intermediate state should not panic on TypeParam store: {result:?}"
    );
    let result = result.unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "generic IndexMut read-after-write should verify: {result:?}"
    );
}

/// Regression test for `deref_mut_wrap<T: DerefMut>(x: &mut T) -> &mut T::Target` (#2670).
///
/// Models the Creusot compat test `generic_deref::deref_mut_wrap`:
///
/// ```text
/// #[ensures(T::deref_mut.postcondition((x,), result))]
/// pub fn deref_mut_wrap<T: DerefMut>(x: &mut T) -> &mut T::Target { &mut *x }
/// ```
///
/// The driver generates:
///   requires: T::deref_mut.postcondition((x,), call_3)  // call assumption from inner &mut *x
///   ensures:  T::deref_mut.postcondition((x,), result)  // user postcondition
///   return_expr: var("call_3")                           // body returns the call result
///   final_values: {"x": deref(var("x"))}                // identity final value
///
/// The verification should succeed because:
///   1. call_3 == result (from return_expr binding)
///   2. The requires UF symbol == ensures UF symbol (same closure_spec symbol for both)
///   3. T::deref_mut.postcondition((x,), call_3) is true (assumed)
///      T::deref_mut.postcondition((x,), result) is true (follows from call_3 == result)
///
/// The bug (#2670): the call assumption's `x` may encode with a different sort signature
/// than the postcondition's `x`, causing the encoder to use two different UF symbols.
/// The solver can then set the postcondition UF to always-false (counterexample).
#[test]
#[timeout(30000)]
fn test_deref_mut_wrap_generic_dispatch_verifies() {
    let t_id = intern_sort_name("T");
    let mutref_typaram = ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)));

    // x: &mut T (annotated with MutRef(TypeParam(T)))
    let x_annotated = var_with_sort("x", mutref_typaram.clone());
    // x without annotation (as it may appear in user postconditions)
    let x_bare = var("x");

    // T::deref_mut receiver (the trait method itself)
    let receiver = var("T_deref_mut");

    // call_3: the intermediate result of the inner &mut *x call
    let call_3 = var("call_3");

    // requires: T::deref_mut.postcondition((x_annotated,), call_3)
    // The call assumption uses x with MutRef annotation (from driver extraction)
    let call_assumption = method_call(
        receiver.clone(),
        "postcondition",
        vec![x_annotated.clone(), call_3.clone()],
    );

    // ensures: T::deref_mut.postcondition((x_bare,), result)
    // The user postcondition may have x without annotation
    let user_postcondition = method_call(
        receiver.clone(),
        "postcondition",
        vec![x_bare.clone(), var("result")],
    );

    // final_values: x's final state is identity (deref of current x)
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // return_expr: the body returns call_3
    let return_expr = call_3.clone();

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[call_assumption], &[user_postcondition], &final_values)
            .return_expr(Some(&return_expr)),
    );

    assert!(
        result.is_ok(),
        "deref_mut_wrap encoding should not panic: {result:?}"
    );
    let result = result.unwrap();
    // The proof should verify: call_3 == result, and the postcondition UF
    // must use the same symbol in both requires and ensures.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "deref_mut_wrap should verify: {result:?}"
    );
}

/// Regression for the exact `generic_deref.rs` precondition shape:
/// `forall<y: &mut T> inv(y) && *y == *x ==> T::deref_mut.precondition(y)`.
///
/// This exercises the quantified precondition path that the compat harness
/// uses for `deref_mut_wrap`. There is deliberately no call-postcondition
/// assumption connecting `call_3` to the requested user postcondition, so a
/// model falsifying that postcondition is the sound result. The companion test
/// below adds that missing assumption and verifies. (#717)
#[test]
#[timeout(30000)]
fn test_deref_mut_wrap_without_call_postcondition_fails() {
    let t_id = intern_sort_name("T");
    let mutref_typaram = ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)));

    let x_annotated = var_with_sort("x", mutref_typaram.clone());
    let y_annotated = var_with_sort("y", mutref_typaram.clone());
    let receiver = var("T_deref_mut");
    let call_3 = var("call_3");

    let quantified_precondition = forall_with_sort(
        "y",
        mutref_typaram.clone(),
        implies(
            and(
                logic_fn_call("inv", vec![y_annotated.clone()]),
                eq(deref(y_annotated.clone()), deref(x_annotated.clone())),
            ),
            method_call(receiver.clone(), "precondition", vec![y_annotated.clone()]),
        ),
    );

    let user_postcondition = method_call(
        receiver,
        "postcondition",
        vec![x_annotated.clone(), var("result")],
    );

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(
            &[quantified_precondition],
            &[user_postcondition],
            &final_values,
        )
        .return_expr(Some(&call_3)),
    );

    assert!(
        result.is_ok(),
        "deref_mut_wrap quantified precondition should encode: {result:?}"
    );
    let result = result.unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "a quantified precondition alone must not prove an unrelated call postcondition: {result:?}"
    );
}

/// Same as above but with consistent annotations on both requires and ensures `x`.
/// This variant confirms the test passes when annotation mismatch is removed.
#[test]
#[timeout(30000)]
fn test_deref_mut_wrap_consistent_annotations_verifies() {
    let t_id = intern_sort_name("T");
    let mutref_typaram = ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)));

    let x_annotated = var_with_sort("x", mutref_typaram.clone());
    let receiver = var("T_deref_mut");
    let call_3 = var("call_3");

    // Both requires and ensures use the SAME annotated x
    let call_assumption = method_call(
        receiver.clone(),
        "postcondition",
        vec![x_annotated.clone(), call_3.clone()],
    );
    let user_postcondition = method_call(
        receiver.clone(),
        "postcondition",
        vec![x_annotated.clone(), var("result")],
    );

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let return_expr = call_3.clone();

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[call_assumption], &[user_postcondition], &final_values)
            .return_expr(Some(&return_expr)),
    );

    assert!(
        result.is_ok(),
        "deref_mut_wrap (consistent annotations) encoding should not panic: {result:?}"
    );
    let result = result.unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "deref_mut_wrap with consistent annotations should verify: {result:?}"
    );
}
