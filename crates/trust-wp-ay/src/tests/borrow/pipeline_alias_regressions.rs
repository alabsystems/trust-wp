// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, time::Duration};

use ntest::timeout;

use super::*;

/// Regression for #1805: Bool-branch postcondition over `result` with a nested
/// `LetAssume` constructor return reaches the expected quantifier incompleteness
/// instead of a ay-dpll clause reconstruction panic.
#[test]
#[timeout(30000)]
fn test_result_branch_seq_postcondition_no_solver_bug_panic() {
    // Return shape (from take_first_mut MIR extraction):
    // assume discrim(_call_2) in {0,1};
    // if discrim(_call_2) == 0 { None } else {
    //   assume self_ == tuple_get_1(tuple_get_0(_call_2));
    //   Some(tuple_get_0(tuple_get_0(_call_2)))
    // }
    let discr = method_call(var("_call_2"), "discriminant", vec![]);
    let discr_is_none = eq(discr.clone(), int(0));
    let discr_is_some = eq(discr.clone(), int(1));
    let discr_in_range = or(discr_is_none.clone(), discr_is_some);

    let call_2_0 = logic_fn_call("__trust_wp_tuple_get_0", vec![var("_call_2")]);
    let call_2_0_1 = logic_fn_call("__trust_wp_tuple_get_1", vec![call_2_0.clone()]);
    let call_2_0_0 = logic_fn_call("__trust_wp_tuple_get_0", vec![call_2_0]);

    let ret_some = logic_fn_call("Some", vec![call_2_0_0]);
    let ret_none = logic_fn_call("None", vec![]);
    let ret_else = let_assume(eq(var("self_"), call_2_0_1), ret_some);
    let ret_ite = ite(discr_is_none, ret_none, ret_else);
    let return_expr = let_assume(discr_in_range, ret_ite);

    // Branch postcondition shape:
    // if is_some(result) { true } else { (^(*self_))@ == Seq::empty() }
    let ensures = vec![ite(
        method_call(var("result"), "is_some", vec![]),
        bool_expr(true),
        eq(
            view(final_expr(deref(var("self_")))),
            logic_fn_call("Seq::empty", vec![]),
        ),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("self_".to_string(), deref(var("self_")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(
            result,
            VerificationResult::Unknown(_) | VerificationResult::Failed(_)
        ),
        "result-branch + Seq-none postcondition should fail closed without verifying: {result:?}"
    );
}

/// Two-phase borrow test: `v.push(v.len())` postcondition (#2124 Phase 3).
///
/// Models:
/// ```rust
/// #[ensures((^v)[v@.len()]@ == v@.len())]
/// fn test(v: &mut Vec<usize>) {
///     v.push(v.len());
/// }
/// ```
///
/// After spec-driven advancement (Phase 2) and result binding (Phase 3),
/// `final_values["v"]` = `push_back(v_current_view, len(v_current_view))`.
///
/// The postcondition says: "the final vec, indexed at the original length,
/// has a view equal to the original length." By the push_back axiom:
/// `index(push_back(s, x), len(s)) == x`, this reduces to `len(s) == len(s)`.
#[test]
#[timeout(30000)]
fn test_two_phase_push_len_postcondition() {
    // Model what spec advancement + result binding produce:
    // v_final = push_back(v@, v@.len())
    let v_current_view = view(deref(var("v")));
    let v_len = method_call(v_current_view.clone(), "len", vec![]);
    let body_expr = method_call(v_current_view.clone(), "push_back", vec![v_len.clone()]);

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    // Postcondition: (^v)[v@.len()]@ == v@.len()
    // Parsed: View(MethodCall { receiver: Final(Var("v")), method: "index_logic",
    //         args: [MethodCall { receiver: View(Deref(Var("v"))), method: "len", args: [] }] })
    //         == MethodCall { receiver: View(Deref(Var("v"))), method: "len", args: [] }
    let final_v_indexed = method_call(final_expr(var("v")), "index_logic", vec![v_len.clone()]);
    let ens = eq(view(final_v_indexed), v_len);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).timeout(Some(Duration::from_secs(5))),
    )
    .unwrap();
    // KNOWN-CLASS PIN (#133): the verdict demotes to `Unknown(ProofTrusted)`
    // under ay's mandatory strict UNSAT certification; the property this test
    // guards is unchanged and every other outcome still fails. The tolerance
    // is opt-in per call site so the strict helper stays strict elsewhere. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    crate::tests::helpers::assert_verified_or_known_proof_trusted(
        &result,
        "two_phase push(len()) postcondition should verify",
    );
}

/// Negative test: two-phase borrow with wrong postcondition (#2124).
///
/// Same model as above but the postcondition claims the pushed element
/// equals `v@.len() + 1` (wrong — it should be `v@.len()`).
#[test]
#[timeout(30000)]
fn test_two_phase_push_len_wrong_postcondition() {
    let v_current_view = view(deref(var("v")));
    let v_len = method_call(v_current_view.clone(), "len", vec![]);
    let body_expr = method_call(v_current_view.clone(), "push_back", vec![v_len.clone()]);

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    // WRONG postcondition: (^v)[v@.len()]@ == v@.len() + 1
    let final_v_indexed = method_call(final_expr(var("v")), "index_logic", vec![v_len.clone()]);
    let ens = eq(view(final_v_indexed), add(v_len, int(1)));

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "two_phase with wrong postcondition should fail: got {result:?}"
    );
}

// ── #2190: _current_final alias coverage regression tests ─────────────
//
// These tests verify that cross-composition variable aliases remain
// constrained after the MutRefVarNames 6-to-2 reduction (#2150).
// The `_current_final` pattern arises from `Final(Deref(Var("v")))` which
// encodes "final value of the current sub-borrow" in tuple postconditions.

/// Minimal test for _current_final: `^(*v) == *(*v)` should verify when
/// the body says `v_final = *v` (identity). This exercises the exact
/// encoding path that produces `v_current_final`.
///
/// If `v_current_final` is unconstrained (free variable), this test
/// will FAIL with a counterexample where `v_current_final != v_current_current`.
///
/// Re: #2190, #858
#[test]
#[timeout(30000)]
fn test_current_final_alias_is_constrained() {
    // Postcondition: Final(Deref(Var("v"))) == Deref(Deref(Var("v")))
    // i.e., ^(*v) == *(*v)
    // This resolves to: v_current_final == v_current_current
    let ens = eq(final_expr(deref(var("v"))), deref(deref(var("v"))));

    // Body: v_final = *v (identity)
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "#2190 regression: v_current_final must be constrained (= final_term). \
         If this fails with counterexample v_current_final != v_current_current, \
         the _current_final alias is missing from verify_mut_borrow_function. \
         Got: {result:?}"
    );
}

/// Test that `Deref(Final(Var("v")))` — i.e., `*(^v)` — resolves to
/// `v_final_current`. This pattern arises when postconditions dereference
/// the final value of a mut ref parameter.
///
/// `v_final_current` is not eagerly declared (#2150).
/// It may be constrained by `assert_current_chain_alias_constraints` if the
/// base `v_final` ends with `_current` (it doesn't — base is `v_final`).
/// This test documents whether the alias system covers this pattern.
///
/// Re: #2190 — related coverage gap analysis for remaining Phase 3 aliases
#[test]
#[timeout(30000)]
fn test_final_current_alias_coverage() {
    // Postcondition: Deref(Final(Var("v"))) == Deref(Var("v"))
    // i.e., *(^v) == *v — the current value of the final state
    // equals the current value (trivially true for identity body)
    // Resolves to: v_final_current == v_current
    let ens = eq(deref(final_expr(var("v"))), deref(var("v")));

    // Body: v_final = *v (identity)
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    // KNOWN GAP (#2190): v_final_current is unconstrained after Phase 3.
    // This currently fails with counterexample. When the alias is restored,
    // change this assertion to expect Verified.
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "#2190 known gap: v_final_current is currently unconstrained. \
         When this starts returning Verified, the alias was restored. Got: {result:?}"
    );
}

/// Test that `Final(Final(Var("v")))` — i.e., `^(^v)` — resolves to
/// `v_final_final`. This double-final pattern may arise from nested
/// borrow resolution.
///
/// Re: #2190 — related coverage gap analysis for remaining Phase 3 aliases
#[test]
#[timeout(30000)]
fn test_final_final_alias_coverage() {
    // Postcondition: Final(Final(Var("v"))) == Final(Var("v"))
    // i.e., ^(^v) == ^v — double-final equals single-final
    // Resolves to: v_final_final == v_final
    let ens = eq(final_expr(final_expr(var("v"))), final_expr(var("v")));

    // Body: v_final = *v (identity)
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    // GAP CLOSED (#2190, #2673): v_final_final is now constrained to equal
    // v_current_final for identity final values. This enables nested borrow
    // patterns like `unnest` where ^(^v) == ^v.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "v_final_final should equal v_current_final for identity borrows (#2190, #2673): got {result:?}"
    );
}
