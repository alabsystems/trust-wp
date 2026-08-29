// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;
use crate::PureExpr;

// =============================================================================
// 1. propagate_body_view_seq_value_to_result
// =============================================================================

/// Verify that `propagate_body_view_seq_value_to_result` copies SeqValue from
/// the body result's View form to `result_view`.
///
/// Setup: encode a Seq `push_back` to create a SeqValue, then encode
/// `View(Var("s"))` to give the view form a SeqValue. Then call
/// `propagate_body_view_seq_value_to_result` with `Var("s")` and
/// verify `result_view` gets a SeqValue.
///
/// Re: #901 — zero-coverage function
#[test]
#[timeout(30000)]
fn test_propagate_body_view_bridges_seq_value_to_result_view() {
    let mut encoder = AYEncoder::new();

    // Register sort hints so s_view is declared with Seq sort.
    // Without this, encode_view_expr defaults s_view to Int sort and
    // assert_view_identity does not propagate SeqValues.
    let push = method_call(var("s"), "push_back", vec![int(1)]);
    encoder.register_sort_hints(std::slice::from_ref(&push));

    // Encode push_back to create a SeqValue in seq_state.
    let _ = encoder.encode_pure(&push);

    // Declare s_view with Seq sort and manually insert a SeqValue for it.
    // In the production pipeline, the verifier pre-declares view variables
    // with Seq sort and propagates SeqValues through view identity assertions.
    // Here we simulate that by directly inserting the SeqValue that the
    // propagation function expects to find.
    let seq_sort = Sort::seq(Sort::Int);
    let s_view_term = encoder
        .get_or_declare_var("s_view", seq_sort)
        .expect("should declare s_view");
    let sentinel_arr = encoder
        .solver
        .declare_const("test_arr", Sort::array(Sort::Int, Sort::Int));
    let sentinel_len = encoder.solver.int_const(5);
    let sentinel_offset = encoder.solver.int_const(0);
    encoder.seq_state_mut_for_test().insert_seq_value(
        s_view_term,
        crate::encoder::SeqValue {
            arr: sentinel_arr,
            len: sentinel_len,
            offset: sentinel_offset,
            known_len: None,
        },
    );

    // Verify the premise: s_view has a SeqValue
    let has_view_sv = encoder
        .vars_for_test()
        .get("s_view")
        .and_then(|term| encoder.seq_state_for_test().get_seq_value(term))
        .is_some();
    assert!(
        has_view_sv,
        "Test premise failed: s_view should have a manually inserted SeqValue"
    );

    // Verify result_view does NOT exist yet
    assert!(
        !encoder.vars_for_test().contains_key("result_view"),
        "result_view should not exist before propagation"
    );

    // Call the function under test
    encoder.propagate_body_view_seq_value_to_result(&PureExpr::Var("s".to_string(), None));

    // Verify result_view now has a SeqValue
    let result_view_has_sv = encoder
        .vars_for_test()
        .get("result_view")
        .and_then(|term| encoder.seq_state_for_test().get_seq_value(term))
        .is_some();
    assert!(
        result_view_has_sv,
        "result_view should have a SeqValue after propagation"
    );

    // Verify the propagated SeqValue matches the source
    let result_view_term = *encoder.vars_for_test().get("result_view").unwrap();
    let result_sv = encoder
        .seq_state_for_test()
        .get_seq_value(&result_view_term)
        .expect("result_view should have SeqValue");
    assert_eq!(
        result_sv.len, sentinel_len,
        "propagated SeqValue should have the same len as the source"
    );
}

/// Verify that `propagate_body_view_seq_value_to_result` is a no-op when
/// the body result's view form has no SeqValue.
///
/// This tests the early-return paths in the function.
///
/// Re: #901 — zero-coverage function, early-return paths
#[test]
#[timeout(30000)]
fn test_propagate_body_view_noop_when_no_seq_value() {
    let mut encoder = AYEncoder::new();

    // Encode a non-Seq variable to populate vars but not seq_values
    let _ = encoder.encode_pure(&gt(var("x"), int(0)));

    let vars_before = encoder.vars_for_test().len();

    // Call with a variable that has no view SeqValue
    encoder.propagate_body_view_seq_value_to_result(&PureExpr::Var("x".to_string(), None));

    // result_view should not be created (early return from no body_view_name
    // or no SeqValue lookup)
    assert!(
        !encoder.vars_for_test().contains_key("result_view"),
        "result_view should not be created when body has no SeqValue"
    );

    // vars count should not change (no new declarations)
    let vars_after = encoder.vars_for_test().len();
    assert_eq!(
        vars_before, vars_after,
        "no new vars should be declared when propagation is a no-op"
    );
}

/// Verify that `propagate_body_view_seq_value_to_result` does not overwrite
/// an existing `result_view` SeqValue (uses `or_insert`, not `insert`).
///
/// Re: #901 — or_insert semantics verification
#[test]
#[timeout(30000)]
fn test_propagate_body_view_does_not_overwrite_existing_result_view() {
    let mut encoder = AYEncoder::new();

    // Pre-declare result_view as a Seq-sorted variable
    let seq_sort = Sort::seq(Sort::Int);
    let result_view_term = encoder
        .get_or_declare_var("result_view", seq_sort)
        .expect("should declare result_view");

    // Manually insert a SeqValue for result_view
    let sentinel_arr = encoder.solver.declare_const("sentinel_arr", Sort::Int);
    let sentinel_len = encoder.solver.int_const(42);
    let sentinel_offset = encoder.solver.int_const(0);
    encoder.seq_state_mut_for_test().insert_seq_value(
        result_view_term,
        crate::encoder::SeqValue {
            arr: sentinel_arr,
            len: sentinel_len,
            offset: sentinel_offset,
            known_len: None,
        },
    );

    // Create a Seq push_back + view to provide a different SeqValue source
    let push = method_call(var("src"), "push_back", vec![int(99)]);
    let _ = encoder.encode_pure(&push);
    let _ = encoder.encode_pure(&view(var("src")));

    // Propagate — should NOT overwrite because of or_insert
    encoder.propagate_body_view_seq_value_to_result(&PureExpr::Var("src".to_string(), None));

    // Verify the original sentinel is preserved
    let sv = encoder
        .seq_state_for_test()
        .get_seq_value(&result_view_term)
        .expect("result_view should still have SeqValue");
    assert_eq!(
        sv.len, sentinel_len,
        "existing result_view SeqValue should not be overwritten (or_insert semantics)"
    );
}
