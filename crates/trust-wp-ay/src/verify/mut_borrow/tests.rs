// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
        ExprSort, PureExpr,
    },
    TrackLevel,
};

use super::{
    super::setup::{setup_verification_encoder, VerificationSetup},
    bind_result_expr, is_type_invariant_obligation_expr, verify_mut_borrow_function_with_modes,
    verify_mut_borrow_function_with_modes_outcome,
};
use crate::{
    encoder::AYEncoder,
    error::EncodingError,
    tests::helpers::{
        add, and, deref, eq, final_expr, forall, ge, gt, implies, int, ite, le, logic_fn_call, lt,
        method_call, mul, ne, sub, var, var_with_sort, view,
    },
    verify::types::MutBorrowRequest,
    VerificationResult,
};

#[test]
#[timeout(30000)]
fn verify_mut_borrow_with_modes_empty_obligation_has_accepted_evidence() {
    let requires = vec![ge(var("x"), int(0))];
    let final_values = HashMap::new();
    let request = MutBorrowRequest::new(&requires, &[], &final_values);

    let outcome = verify_mut_borrow_function_with_modes_outcome(request.clone())
        .expect("empty mut-borrow outcome should encode");
    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "outcome API should keep the verified result: {:?}",
        outcome.result
    );
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("empty mut-borrow outcome should carry solver evidence");
    assert!(
        evidence.accepted_for_consumer,
        "empty mut-borrow solver evidence should be accepted for consumers: {evidence:?}"
    );
    assert!(
        evidence.result.eq_ignore_ascii_case("unsat") || evidence.result.starts_with("Unsat"),
        "empty mut-borrow evidence should be UNSAT, got {}",
        evidence.result
    );

    let legacy = verify_mut_borrow_function_with_modes(request)
        .expect("legacy mut-borrow wrapper should encode");
    assert!(
        matches!(legacy, VerificationResult::Verified(_)),
        "legacy mut-borrow wrapper should preserve verified result with accepted evidence: {legacy:?}"
    );
}

#[test]
fn test_mut_borrow_detects_type_invariant_obligation_expr() {
    let inv = PureExpr::MethodCall {
        receiver: Arc::new(var("self")),
        method: "__trust_wp_invariant_NonZero".to_string(),
        args: vec![],
    };

    assert!(is_type_invariant_obligation_expr(&inv));
    assert!(!is_type_invariant_obligation_expr(&eq(var("x"), var("y"))));
}

#[test]
#[timeout(30000)]
fn mut_borrow_projection_only_whole_mutref_ite_binds_current_component() {
    let mut encoder = AYEncoder::new_all();
    let mut_ref_int = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));

    encoder
        .get_or_declare_var("take_first", Sort::Bool)
        .expect("take_first should declare");
    encoder
        .get_or_declare_var("a_ref", mut_ref_int.clone())
        .expect("a_ref should declare");
    encoder
        .get_or_declare_var("b_ref", mut_ref_int)
        .expect("b_ref should declare");

    let a_current = encoder
        .get_or_declare_var("a_ref_current", Sort::Int)
        .expect("a_ref_current should declare");
    let b_current = encoder
        .get_or_declare_var("b_ref_current", Sort::Int)
        .expect("b_ref_current should declare");
    let take_first = encoder.var_term("take_first").expect("take_first term");
    let seven = encoder.encode_pure(&int(7)).expect("7 should encode");
    let three = encoder.encode_pure(&int(3)).expect("3 should encode");
    encoder.assert_term(take_first);
    encoder.assert_eq(a_current, seven);
    encoder.assert_eq(b_current, three);

    let return_expr = ite(var("take_first"), var("a_ref"), var("b_ref"));
    let ensures = vec![eq(view(deref(var("result"))), int(7))];
    let final_values = HashMap::from([
        ("a_ref".to_string(), deref(var("a_ref"))),
        ("b_ref".to_string(), deref(var("b_ref"))),
    ]);
    bind_result_expr(&mut encoder, &return_expr, &ensures, &final_values)
        .expect("projection-only mut-ref result binding should encode");

    let ensure_term = encoder
        .encode_pure(&ensures[0])
        .expect("ensures should encode");
    let negated_ensure = encoder.solver_mut().not(ensure_term);
    encoder.assert_term(negated_ensure);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "projection-only *result should follow the selected whole-mutref branch"
    );
}

/// Regression for Int/Seq sort mismatch when asserting
/// `old_{param}_current_view = {param}_current_view`.
#[test]
#[timeout(30000)]
fn test_mut_borrow_old_current_view_alias_uses_matching_seq_sort() {
    let mut final_values = HashMap::new();
    final_values.insert("addr".to_string(), deref(var("addr")));

    let addr_view = PureExpr::View(Arc::new(deref(var("addr"))));
    let ensures = vec![eq(addr_view.clone(), addr_view)];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "old/current view alias should verify without Int/Seq sort panic: {result:?}"
    );
}

/// Regression: mut-ref contracts mix `v@` and `(*v)@` in different phases.
#[test]
#[timeout(30000)]
fn test_mut_borrow_base_view_aliases_current_view() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let ensures = vec![eq(view(var("v")), view(deref(var("v"))))];
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "v@ and (*v)@ should alias for mut-ref params: got {result:?}"
    );
}

/// Whole `&mut` return contracts must bind `result` to the returned borrow
/// carrier, not to the carrier's current referent.
#[test]
#[timeout(30000)]
fn test_mut_borrow_whole_mut_ref_return_preserves_carrier() {
    let mut_ref_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let r = var_with_sort("r", mut_ref_int);
    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(r.clone()));

    let ensures = vec![eq(var("result"), r.clone())];
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&r)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "whole mut-ref return should prove result == r: got {result:?}"
    );
}

/// Driver extraction can lose the `MutRef` sort on simple returned-borrow
/// expressions. A direct `result == r` postcondition should still keep the
/// returned borrow as `r`, not canonicalize it to `*r`.
#[test]
#[timeout(30000)]
fn test_mut_borrow_unannotated_direct_return_equality_preserves_var() {
    let r = var("r");
    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(r.clone()));

    let ensures = vec![eq(var("result"), r.clone())];
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&r)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "direct returned-borrow equality should prove result == r: got {result:?}"
    );
}

/// `final_borrows::reborrow_id` returns a reborrow expression, while its
/// postcondition relates the whole returned borrow back to the input carrier.
#[test]
#[timeout(30000)]
fn test_mut_borrow_reborrow_return_uses_direct_whole_result_equality() {
    let mut_ref_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let r = var_with_sort("r", mut_ref_int.clone());
    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(r.clone()));

    let return_expr = deref(deref(r.clone()));
    let ensures = vec![eq(var_with_sort("result", mut_ref_int), r)];
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "whole reborrow equality should prove result == r: got {result:?}"
    );
}

/// Projection-only `result` contracts bind the returned referent, not the
/// whole-borrow carrier. This is the minimal shape behind `NonZero::inner_mut`.
#[test]
#[timeout(30000)]
fn test_mut_borrow_projection_only_result_uses_body_referent_sort() {
    let mut_ref_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let self_ref = var_with_sort("self", mut_ref_int.clone());
    let result_ref = var_with_sort("result", mut_ref_int);

    let mut final_values = HashMap::new();
    final_values.insert("self".to_string(), deref(self_ref.clone()));

    let ensures = vec![
        eq(
            final_expr(self_ref.clone()),
            view(final_expr(result_ref.clone())),
        ),
        eq(final_expr(self_ref.clone()), view(deref(result_ref))),
    ];
    let return_expr = deref(self_ref);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("projection-only result binding should encode");

    // SOUNDNESS PIN (borrows lent into the return value): `*self` is returned;
    // the second clause equates `^self` with `*result`, false once the caller writes.
    // Encoding must still succeed at the referent sort (the `.expect` above).
    // The identity `final_values` entry below is a driver shape ay must not
    // trust: the lent param is mutation-continued, and ay must not equate
    // `^result` with `*result`, so the prophecy clause is unprovable.
    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "a lent borrow's identity final must not prove a prophecy clause: got {result:?}"
    );
}

/// Literal false mut-borrow obligations should be classified from an
/// axiom-light fresh base instead of spending the full solver budget on
/// type-invariant ground context.
#[test]
#[timeout(30000)]
fn test_mut_borrow_literal_false_first_slice_uses_axiom_light_base() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let requires = vec![method_call(deref(var("x")), &inv_method, vec![])];
    let ensures = vec![
        PureExpr::Bool(false),
        method_call(final_expr(var("x")), &inv_method, vec![]),
    ];
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).type_invariants(Some(&[inv_def])),
    )
    .expect("encoding should succeed");

    assert!(
        crate::tests::rejected(&result),
        "literal false obligation on satisfiable base should fail: got {result:?}"
    );
}

/// Regression for nested mutable-borrow returns (`bug/922` shape).
#[test]
#[timeout(30000)]
fn test_bug_922_nested_mut_ref_return_aliases() {
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let x0_field1_current = deref(PureExpr::LogicFnCall {
        name: tuple_get_1.clone(),
        args: vec![deref(var("x0"))],
    });
    let x0_field1_from_x0_final = deref(PureExpr::LogicFnCall {
        name: tuple_get_1,
        args: vec![final_expr(var("x0"))],
    });

    let ens_result_current = eq(deref(var("result")), x0_field1_current.clone());
    let ens_result_final = eq(final_expr(var("result")), x0_field1_from_x0_final);

    let mut final_values = HashMap::new();
    final_values.insert("x0".to_string(), deref(var("x0")));
    final_values.insert("x0.1".to_string(), x0_field1_current.clone());

    let return_expr = x0_field1_current;

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens_result_current, ens_result_final], &final_values)
            .return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    // SOUNDNESS PIN (borrows lent into the return value): `&mut *x0.1` is returned, so
    // `^result == *(^x0).1` is the caller's to decide, not `*x0`'s.
    // The identity `final_values` entry below is a driver shape ay must not
    // trust: the lent param is mutation-continued, and ay must not equate
    // `^result` with `*result`, so the prophecy clause is unprovable.
    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "a lent borrow's identity final must not prove a prophecy clause: got {result:?}"
    );
}

/// The full `bug/922` mut-borrow shape includes a non-result field-finality
/// postcondition: `^(*x).1 == ^(^x).1`. That obligation is already implied by
/// the reconstructed tuple final value and should not enter solver search.
#[test]
#[timeout(30000)]
fn test_bug_922_reconstructed_tuple_field_finality_verifies() {
    let tuple2 = tuple_logic_fn_name(2);
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let x0 = var_with_sort("x0", ExprSort::MutRef(Box::new(ExprSort::Tuple(2))));
    let x0_untyped = var("x0");
    let x0_field0_current = PureExpr::LogicFnCall {
        name: tuple_get_0,
        args: vec![deref(x0.clone())],
    };
    let x0_field1_current_ref = PureExpr::LogicFnCall {
        name: tuple_get_1.clone(),
        args: vec![deref(x0.clone())],
    };
    let x0_field1_current = deref(x0_field1_current_ref.clone());
    let x0_field1_from_x0_final = deref(PureExpr::LogicFnCall {
        name: tuple_get_1.clone(),
        args: vec![final_expr(x0.clone())],
    });

    let ensures = vec![
        eq(
            final_expr(PureExpr::LogicFnCall {
                name: tuple_get_1.clone(),
                args: vec![deref(x0_untyped.clone())],
            }),
            final_expr(PureExpr::LogicFnCall {
                name: tuple_get_1,
                args: vec![final_expr(x0_untyped.clone())],
            }),
        ),
        eq(final_expr(var("result")), x0_field1_from_x0_final),
        eq(deref(var("result")), x0_field1_current.clone()),
    ];

    let mut final_values = HashMap::new();
    final_values.insert(
        "x0".to_string(),
        PureExpr::LogicFnCall {
            name: tuple2,
            args: vec![x0_field0_current, x0_field1_current.clone()],
        },
    );
    final_values.insert("x0.1".to_string(), x0_field1_current.clone());

    let result = match verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&x0_field1_current_ref))
            .timeout(Some(std::time::Duration::from_secs(5))),
    ) {
        Ok(result) => result,
        // `^(^x0).1` is the final value of the borrow `x0`'s final value
        // holds in its second field, which the caller decides: refused, not
        // read as the field of `x0`'s final value (D-129).
        Err(EncodingError::Unsupported { message, .. }) => {
            assert!(
                message.contains("final value refused"),
                "unexpected refusal: {message}"
            );
            return;
        }
        Err(other) => panic!("unexpected encoding error: {other:?}"),
    };

    // SOUNDNESS PIN (returned reborrow of an inner borrow): the returned value
    // reborrows the inner borrow stored in `x0.1`, so `^result` is the
    // caller's prophecy. Matching `Final(result)` syntactically against the
    // reconstructed final of `x0` (a field of `x0`'s entry value) would
    // discharge it without a caller link; without that link the clause is
    // not provable.
    assert!(
        !matches!(result, super::VerificationResult::Verified(_)),
        "a returned inner-borrow reborrow's ^result must not follow from x0's reconstructed final: got {result:?}"
    );
}

/// Negative companion: returning the wrong field should fail.
/// Re: #863
#[test]
#[timeout(30000)]
fn test_bug_922_nested_mut_ref_wrong_field_fails() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let x0_field1_current = deref(PureExpr::LogicFnCall {
        name: tuple_get_1.clone(),
        args: vec![deref(var("x0"))],
    });
    let x0_field0_current = deref(PureExpr::LogicFnCall {
        name: tuple_get_0,
        args: vec![deref(var("x0"))],
    });

    let mut final_values = HashMap::new();
    final_values.insert("x0".to_string(), deref(var("x0")));
    final_values.insert("x0.0".to_string(), x0_field0_current.clone());

    let return_expr = x0_field0_current;
    let requires = vec![ne(return_expr.clone(), x0_field1_current.clone())];
    let ensures = vec![eq(return_expr.clone(), x0_field1_current)];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        crate::tests::rejected(&result),
        "returning wrong field should fail: got {:?}",
        result
    );
}

/// Regression for #1372: Seq-typed result in mut_borrow verification.
#[test]
#[timeout(30000)]
fn test_mut_borrow_seq_typed_result_no_sort_conflict() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let return_expr = var_with_sort("ret_seq", ExprSort::Seq);

    let ensures = vec![eq(
        var_with_sort("result", ExprSort::Seq),
        var_with_sort("ret_seq", ExprSort::Seq),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed without sort mismatch");

    // KNOWN-CLASS PIN (strict UNSAT certification gap): the verdict may demote
    // to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "Seq-typed result should verify without Int/Seq sort mismatch: {result:?}"
    );
}

// ── ghost_context proof coverage (0→N, #1603) ──────────────────────

/// Ghost context asserting a simple equality should make an otherwise-
/// unprovable postcondition verifiable.
#[test]
#[timeout(30000)]
fn test_ghost_context_simple_equality_enables_verification() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    let ensures = vec![eq(final_expr(var("v")), int(42))];

    let ghost = vec![eq(add(deref(var("v")), int(1)), int(42))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost context equality should enable postcondition proof: got {result:?}"
    );
}

/// Without ghost context, the same postcondition should fail or be unknown.
#[test]
#[timeout(30000)]
fn test_ghost_context_absent_postcondition_fails() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    let ensures = vec![eq(final_expr(var("v")), int(42))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values);

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without ghost context, ^v == 42 should not be provable: got {:?}",
        result
    );
}

/// Ghost context with implications.
#[test]
#[timeout(30000)]
fn test_ghost_context_implication_flattening_in_mut_borrow() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let ensures = vec![gt(final_expr(var("v")), int(0))];

    let ghost = vec![
        var("flag"),
        implies(var("flag"), gt(deref(var("v")), int(0))),
    ];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost implication with true antecedent should flatten and prove postcondition: \
         got {result:?}"
    );
}

/// Ghost context with multiple mut-ref parameters.
#[test]
#[timeout(60000)]
fn test_ghost_context_multiple_mut_ref_params() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("b")));
    final_values.insert("b".to_string(), deref(var("a")));

    let ensures = vec![eq(add(final_expr(var("a")), final_expr(var("b"))), int(10))];

    let ghost = vec![eq(add(deref(var("a")), deref(var("b"))), int(10))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost context with multiple mut-ref params should verify sum preservation: \
         got {result:?}"
    );
}

/// Ghost context with conjunction: multiple constraints asserted individually.
#[test]
#[timeout(60000)]
fn test_ghost_context_multiple_facts_asserted_individually() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), var("w")));

    let ensures = vec![eq(final_expr(var("v")), int(15))];

    let ghost = vec![eq(deref(var("v")), int(5)), eq(var("w"), int(10))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "multiple ghost facts should be individually asserted and prove postcondition: \
         got {result:?}"
    );
}

/// Empty ghost_context (`Some(&[])`) should not interfere.
#[test]
#[timeout(60000)]
fn test_ghost_context_empty_vec_with_preconditions() {
    let requires = vec![gt(deref(var("v")), int(0))];

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), deref(var("v"))));

    let ensures = vec![and(
        gt(final_expr(var("v")), int(0)),
        eq(final_expr(var("v")), add(deref(var("v")), deref(var("v")))),
    )];

    let ghost: Vec<PureExpr> = vec![];

    let request =
        MutBorrowRequest::new(&requires, &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "empty ghost context with preconditions should still verify: got {result:?}"
    );
}

/// Ghost context combined with a return expression.
#[test]
#[timeout(30000)]
fn test_ghost_context_with_return_expr() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    let ensures = vec![eq(var("result"), int(10))];

    let return_expr = deref(var("v"));

    let ghost = vec![eq(deref(var("v")), int(10))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values)
        .ghost_context(Some(&ghost))
        .return_expr(Some(&return_expr));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost context should constrain return expression value: got {result:?}"
    );
}

/// Negative companion: without ghost context, result is unconstrained.
#[test]
#[timeout(30000)]
fn test_ghost_context_absent_return_expr_fails() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    let ensures = vec![eq(var("result"), int(10))];
    let return_expr = deref(var("v"));

    let request =
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without ghost context, result == 10 should not be provable: got {:?}",
        result
    );
}

/// Regression for #2364: return_expr=None with result-referencing ensures must
/// trigger the unsoundness counter and demote to Unknown (not false Verified).
///
/// The postcondition `result >= result` is a tautology — without the guard it
/// would verify trivially. With the guard, `demote_if_unsound` converts
/// Verified → Unknown because `result` is an unconstrained free variable.
#[test]
#[timeout(30000)]
fn test_no_return_expr_with_result_ensures_demotes_to_unknown() {
    use trust_wp_core::formula::BinOp;

    let final_values = HashMap::new();

    // Tautological postcondition: result >= result is always true.
    // Without the #2364 guard this would produce false Verified.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(var("result")),
        BinOp::Ge,
        Arc::new(var("result")),
    )];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values);
    // No .return_expr() call — defaults to None.

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Unknown(_)),
        "return_expr=None with result-referencing ensures should demote to Unknown, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn mut_borrow_hashmap_list_resize_positive_size_shape_false_postcondition_is_not_verified() {
    let final_values = HashMap::new();
    let ensures = vec![lt(int(0), mul(int(-1), int(2)))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values);
    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "retired hashmap/list positive-size shortcut shape must not verify false arithmetic: {result:?}"
    );
}

/// Ghost context with multiple ensures (obligation slicing).
#[test]
#[timeout(60000)]
fn test_ghost_context_persists_across_obligation_slices() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), mul(deref(var("v")), int(2)));

    let ensures = vec![
        eq(final_expr(var("v")), int(10)),
        gt(final_expr(var("v")), int(0)),
    ];

    let ghost = vec![eq(deref(var("v")), int(5))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost context should persist across obligation slices: got {result:?}"
    );
}

/// Ghost context + return_expr + multiple postconditions.
#[test]
#[timeout(30000)]
fn test_ghost_context_return_expr_and_multiple_ensures() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    let ensures = vec![eq(var("result"), int(7)), eq(final_expr(var("v")), int(8))];

    let return_expr = deref(var("v"));
    let ghost = vec![eq(deref(var("v")), int(7))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values)
        .ghost_context(Some(&ghost))
        .return_expr(Some(&return_expr));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost + return_expr + multiple ensures should verify: got {result:?}"
    );
}

/// Regression test for ghost_let double-deref write extraction (#2691).
///
/// Models the `bar` function from `ghost/ghost_let.rs`:
///   ```text
///   #[ensures((^*g2) == 1i32)]
///   fn bar(mut g2: Ghost<&mut i32>) {
///       ghost! { **g2 = 1; };
///   }
///   ```
/// The ghost context extraction pipeline derives `^*g2 == 1` from the
/// double-deref write `**g2 = 1` inside the ghost block:
///   1. MIR walk sees `*g2 = 1` (carrier write) → records `*g2 → Int(1)`
///   2. `derive_final_deref_ghost_substitutions` transforms
///      `*g2 → concrete` into `^*g2 → concrete`
///   3. This ghost fact `Final(Deref(Var("g2"))) == Int(1)` is asserted
///      in the verification context
/// The postcondition `(^*g2) == 1` then verifies because the ghost
/// assertion constrains `g2_current_final` to 1.
#[test]
#[timeout(30000)]
fn test_ghost_let_double_deref_write_final_deref_verifies() {
    // g2: Ghost<&mut i32> is encoded as MutRef(Int) — ghost wrapper erased.
    // final_values: the mutation writes 1 to *g2.
    let mut final_values = HashMap::new();
    final_values.insert("g2".to_string(), int(1));

    // Postcondition: (^*g2) == 1 → Final(Deref(Var("g2"))) == Int(1)
    let ensures = vec![eq(final_expr(deref(var("g2"))), int(1))];

    // Ghost context fact derived from the double-deref write:
    // ^*g2 == 1 → Final(Deref(Var("g2"))) == Int(1)
    let ghost = vec![eq(final_expr(deref(var("g2"))), int(1))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost_let double-deref write (^*g2 == 1) should verify via ghost context: got {result:?}"
    );
}

/// Negative companion for #2691: without the ghost context fact,
/// a postcondition requiring a specific final-deref value that differs
/// from the final_values binding should fail.
///
/// Here final_values says `^g2 == *g2 + 1` (an increment), but the
/// postcondition asks for `^*g2 == 42`. Only with a ghost context fact
/// `^*g2 == 42` would this verify. Without it, the solver cannot
/// constrain `g2_current_final` to 42.
#[test]
#[timeout(30000)]
fn test_ghost_let_double_deref_write_without_ghost_fails() {
    let mut final_values = HashMap::new();
    // ^g2 is some expression of *g2 — the solver cannot determine its value
    final_values.insert("g2".to_string(), add(deref(var("g2")), int(1)));

    let ensures = vec![eq(final_expr(deref(var("g2"))), int(42))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values);

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without ghost context, ^*g2 == 42 should not be provable: got {result:?}"
    );
}

/// Positive companion: same setup as above but WITH ghost context —
/// the ghost fact `^*g2 == 42` makes the postcondition provable.
#[test]
#[timeout(30000)]
fn test_ghost_let_double_deref_write_with_ghost_enables_proof() {
    let mut final_values = HashMap::new();
    final_values.insert("g2".to_string(), add(deref(var("g2")), int(1)));

    let ensures = vec![eq(final_expr(deref(var("g2"))), int(42))];

    let ghost = vec![eq(final_expr(deref(var("g2"))), int(42))];

    let request = MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost));

    let result = verify_mut_borrow_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, super::VerificationResult::Verified(_)),
        "ghost_let double-deref write with ghost fact ^*g2 == 42 should verify: got {result:?}"
    );
}

/// Phase 6 (#2124): IndexMut intermediate state encoding.
///
/// After Phase 5, `final_values["a"]` contains
/// `View(Deref(Var("a"))).set(View(Var("i")), Var("x"))` — the Seq-model
/// representation of a pointwise update. The mut-borrow verification pipeline
/// must be able to encode this expression without sort mismatches.
///
/// This test reproduces the `vector/07_read_write.rs` pattern:
///   #[requires(i@ < a@.len())]
///   fn read_write(a: &mut Vec<T>, i: usize, x: T) {
///       a[i] = x;
///       assert!(a[i] == x);
///   }
#[test]
#[timeout(30000)]
fn test_index_mut_intermediate_state_encodes_without_sort_mismatch() {
    use trust_wp_core::formula::ExprSort;

    // Build the Phase 5 intermediate state expression:
    //   View(Deref(Var("a"))).set(View(Var("i")), Var("x"))
    let intermediate_state =
        method_call(view(deref(var("a"))), "set", vec![view(var("i")), var("x")]);

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), intermediate_state);

    // Synthesized IndexMut postconditions (from indexed_write_synthesis.rs):
    // These go into effective_requires, providing sort context.
    let a_ref = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let final_view = view(final_expr(a_ref.clone()));
    let current_view = view(deref(a_ref));

    // Point-write: (^a)@.index_logic(i@) == x
    let point_write = eq(
        method_call(final_view.clone(), "index_logic", vec![view(var("i"))]),
        var("x"),
    );
    // Length preservation: (^a)@.len() == (*a)@.len()
    let len_preservation = eq(
        method_call(final_view.clone(), "len", vec![]),
        method_call(current_view.clone(), "len", vec![]),
    );

    // Requires: i@ < (*a)@.len()
    let requires = vec![
        PureExpr::BinOp(
            Arc::new(view(var("i"))),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(method_call(current_view, "len", vec![])),
        ),
        point_write,
        len_preservation,
    ];

    // Ensures: (^a)@.index_logic(i@) == x (the in-body assertion as postcondition)
    let ensures = vec![eq(
        method_call(final_view, "index_logic", vec![view(var("i"))]),
        var("x"),
    )];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ));

    // Should not panic or produce sort mismatch errors
    assert!(
        result.is_ok(),
        "IndexMut intermediate state encoding should not produce sort mismatch: {result:?}"
    );
    let result = result.unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "IndexMut read-after-write postcondition should verify: {result:?}"
    );
}

/// Phase 6 (#2124): Read-after-write through Pipeline A call assumptions.
///
/// Pipeline A generates call assumptions for `Index::index(a, i)` that
/// reference `View(Var("a"))` (mapping to `a_view`). After an IndexMut
/// write, this should see the POST-write state. Phase 6 advances `a_view`
/// to equal `final_a_view` (the post-write Seq), enabling the solver to
/// prove `a_view.index_logic(i) == x` via the synthesized point-write
/// postcondition.
///
/// This test simulates the full vector/07_read_write.rs flow:
/// 1. final_values has the Phase 5 .set() intermediate state
/// 2. ghost_context contains Pipeline A's call assumption:
///    *call_5 == a@.index_logic(i@)   (Index::index post-condition)
/// 3. return_expr is: LetAssume { call_5 == x, body: () }
/// 4. ensures: the assertion holds (postcondition-lifted)
///
/// The test verifies that the view advancement enables the proof path:
///   call_5 == a_view.index_logic(i_view)    [ghost call assumption]
///   a_view == final_a_view                   [Phase 6 view advancement]
///   final_a_view.index_logic(i_view) == x    [synthesized point-write]
///   ⊢ call_5 == x                            [chain]
#[test]
#[timeout(30000)]
fn test_index_mut_read_after_write_with_pipeline_a_assumptions() {
    use trust_wp_core::formula::{BinOp, ExprSort};

    // Phase 5 intermediate state: View(Deref(Var("a"))).set(i@, x)
    let intermediate_state =
        method_call(view(deref(var("a"))), "set", vec![view(var("i")), var("x")]);

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), intermediate_state);

    // Synthesized IndexMut postconditions (effective_requires)
    let a_ref = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let final_view = view(final_expr(a_ref.clone()));
    let current_view = view(deref(a_ref));

    let requires = vec![
        // i@ < (*a)@.len()
        PureExpr::BinOp(
            Arc::new(view(var("i"))),
            BinOp::Lt,
            Arc::new(method_call(current_view.clone(), "len", vec![])),
        ),
        // Point-write: (^a)@.index_logic(i@) == x
        eq(
            method_call(final_view.clone(), "index_logic", vec![view(var("i"))]),
            var("x"),
        ),
        // Length preservation: (^a)@.len() == (*a)@.len()
        eq(
            method_call(final_view, "len", vec![]),
            method_call(current_view, "len", vec![]),
        ),
    ];

    // Pipeline A call assumption (from Index::index extern spec):
    // *call_5 == View(Var("a")).index_logic(View(Var("i")))
    // Note: Pipeline A uses View(Var("a")) which maps to `a_view`.
    let index_call_assumption = eq(
        deref(var("call_5")),
        method_call(view(var("a")), "index_logic", vec![view(var("i"))]),
    );

    // The ghost context carries Pipeline A's call assumptions
    let ghost_context = vec![index_call_assumption];

    // return_expr: LetAssume { assumption: call_5 == x, body: () }
    // This represents the in-body assertion `assert!(a[i] == x)`.
    let return_expr = PureExpr::LetAssume {
        assumption: Arc::new(eq(var("call_5"), var("x"))),
        body: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        }),
    };

    // Ensures: call_5 == x (the assertion must hold)
    let ensures = vec![eq(var("call_5"), var("x"))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .ghost_context(Some(&ghost_context))
            .return_expr(Some(&return_expr)),
    );

    let result = result.expect("encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Pipeline A read-after-write should verify: {result:?}"
    );
}

/// `ghost_context = None` and `ghost_context = Some(&[])` should behave identically.
#[test]
#[timeout(60000)]
fn test_ghost_context_none_vs_empty_equivalence() {
    let requires = vec![gt(deref(var("v")), int(0))];
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let ensures = vec![gt(final_expr(var("v")), int(0))];

    let request_none = MutBorrowRequest::new(&requires, &ensures, &final_values);
    let result_none = verify_mut_borrow_function_with_modes(request_none).expect("None encoding");

    let empty: Vec<PureExpr> = vec![];
    let request_empty =
        MutBorrowRequest::new(&requires, &ensures, &final_values).ghost_context(Some(&empty));
    let result_empty =
        verify_mut_borrow_function_with_modes(request_empty).expect("empty encoding");

    assert!(
        matches!(result_none, super::VerificationResult::Verified(_)),
        "None ghost_context should verify: got {result_none:?}"
    );
    assert!(
        matches!(result_empty, super::VerificationResult::Verified(_)),
        "empty ghost_context should verify: got {result_empty:?}"
    );
}

/// Vec-sorted variable bridge coercion (#2124).
///
/// When the driver annotates a Vec parameter with `ExprSort::Datatype("std::vec::Vec")`
/// instead of `ExprSort::Seq`, the ay encoder produces `Uninterpreted("std::vec::Vec")`
/// for the base variable. Seq projectors (seq_len, seq_array) expect `Sort::Seq(Int)`. (#2080)
///
/// The `coerce_to_seq` bridge UF in `seq/mod.rs` transparently wraps the Vec-sorted
/// term in a `__vec_to_seq_*` application, producing a Seq-sorted term for projector
/// application. This test verifies that the bridge prevents sort mismatch panics.
#[test]
#[timeout(30000)]
fn test_vec_datatype_sort_coercion_does_not_panic() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let vec_id = intern_sort_name("std::vec::Vec");
    let a_vec = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Datatype(vec_id))));

    // final_values: a -> View(Deref(Var("a"))).push_back(Var("x"))
    // This mimics v.push(x) where v has Datatype("std::vec::Vec") sort.
    let final_state = method_call(view(deref(a_vec.clone())), "push_back", vec![var("x")]);
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), final_state);

    // requires: (*a)@.len() >= 0
    let requires = vec![PureExpr::BinOp(
        Arc::new(method_call(view(deref(a_vec)), "len", vec![])),
        trust_wp_core::formula::BinOp::Ge,
        Arc::new(int(0)),
    )];

    // ensures: (^a)@.len() > 0  (push_back adds one element)
    let ensures = vec![PureExpr::BinOp(
        Arc::new(method_call(view(final_expr(var("a"))), "len", vec![])),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(int(0)),
    )];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ));

    let result = result.expect("Vec Datatype sort should not produce sort mismatch");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Vec coercion should verify: {result:?}"
    );
}

/// Direct ay-level reproducer for the current `#2616` proof_assert ghost Seq lane.
///
/// This mirrors the proof_assert driver request after assertion rewriting:
/// - keeps the ghost-helper post-state fact in the preconditions
/// - rewrites the ensure onto `call_4.push_back(30).index_logic(0)`
/// - uses identity final-values plus `mutation_continued={"call_4"}`
#[test]
#[timeout(120000)]
fn test_proof_assert_ghost_seq_push_back_single_bare_carrier_2616() {
    let _proof_assert_guard = crate::ProofAssertModeGuard::enter();
    let call_4 = var_with_sort("call_4", ExprSort::Seq);
    let v = var_with_sort("v", ExprSort::Seq);
    let mutation_continued = HashSet::from(["call_4".to_string()]);
    let mut final_values = HashMap::new();
    final_values.insert("call_4".to_string(), var("call_4"));

    let ghost_alias = eq(v, final_expr(call_4.clone()));
    let requires = vec![
        ghost_alias.clone(),
        eq(call_4.clone(), logic_fn_call("seq_empty", vec![])),
        eq(method_call(call_4.clone(), "len", vec![]), int(0)),
        eq(
            final_expr(call_4.clone()),
            method_call(call_4.clone(), "push_back", vec![int(30)]),
        ),
    ];
    let ensures = vec![eq(
        method_call(
            method_call(call_4, "push_back", vec![int(30)]),
            "index_logic",
            vec![int(0)],
        ),
        int(30),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .ghost_context(Some(std::slice::from_ref(&ghost_alias)))
            .mutation_continued_params(Some(mutation_continued)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "direct proof_assert-style bare Seq carrier should verify once #2616 is fixed: got {result:?}"
    );
}

#[test]
fn proof_assert_seq_push_back_index_matcher_has_exact_negative_controls() {
    let base = var_with_sort("s", ExprSort::Seq);
    let len_zero = eq(method_call(base.clone(), "len", vec![]), int(0));
    let theorem = |index, pushed, expected| {
        eq(
            method_call(
                method_call(base.clone(), "push_back", vec![int(pushed)]),
                "index_logic",
                vec![int(index)],
            ),
            int(expected),
        )
    };

    assert!(matches!(
        super::obligation::seq_push_back_index_matches_requirements(
            std::slice::from_ref(&len_zero),
            &theorem(0, 30, 30),
        ),
        Some(VerificationResult::Verified(_))
    ));
    assert!(
        super::obligation::seq_push_back_index_matches_requirements(&[], &theorem(0, 30, 30))
            .is_none(),
        "a missing base-length fact must not authorize the reduction"
    );
    assert!(
        super::obligation::seq_push_back_index_matches_requirements(
            &[ne(method_call(base.clone(), "len", vec![]), int(0))],
            &theorem(0, 30, 30),
        )
        .is_none(),
        "a negated length fact must not authorize the reduction"
    );
    assert!(
        super::obligation::seq_push_back_index_matches_requirements(
            &[eq(
                method_call(var_with_sort("other", ExprSort::Seq), "len", vec![]),
                int(0),
            )],
            &theorem(0, 30, 30),
        )
        .is_none(),
        "a foreign carrier's length must not authorize the reduction"
    );
    assert!(matches!(
        super::obligation::seq_push_back_index_matches_requirements(
            std::slice::from_ref(&len_zero),
            &theorem(0, 30, 31),
        ),
        Some(VerificationResult::Failed(_))
    ));
    assert!(
        super::obligation::seq_push_back_index_matches_requirements(
            &[len_zero],
            &theorem(1, 30, 30),
        )
        .is_none(),
        "reading a different index must not authorize the write-index theorem"
    );
}

#[test]
#[timeout(120000)]
fn test_proof_assert_ghost_seq_push_back_single_bare_carrier_binding_stage_sat_2616() {
    let call_4 = var_with_sort("call_4", ExprSort::Seq);
    let v = var_with_sort("v", ExprSort::Seq);
    let mutation_continued = HashSet::from(["call_4".to_string()]);
    let ghost_alias = eq(v, final_expr(call_4.clone()));
    let empty_req = eq(call_4.clone(), logic_fn_call("seq_empty", vec![]));
    let len_req = eq(method_call(call_4.clone(), "len", vec![]), int(0));
    let push_req = eq(
        final_expr(call_4.clone()),
        method_call(call_4.clone(), "push_back", vec![int(30)]),
    );
    let requires = [
        ghost_alias.clone(),
        empty_req.clone(),
        len_req.clone(),
        push_req.clone(),
    ];
    let ensures = [eq(
        method_call(
            method_call(call_4.clone(), "push_back", vec![int(30)]),
            "index_logic",
            vec![int(0)],
        ),
        int(30),
    )];
    let temporal_params = HashSet::from(["call_4".to_string()]);
    let ghost_alias =
        super::preserve_temporal_wrappers_for_mut_borrow(&ghost_alias, &temporal_params);
    let requires: Vec<PureExpr> = requires
        .iter()
        .map(|req| super::preserve_temporal_wrappers_for_mut_borrow(req, &temporal_params))
        .collect();
    let ensures: Vec<PureExpr> = ensures
        .iter()
        .map(|ens| super::preserve_temporal_wrappers_for_mut_borrow(ens, &temporal_params))
        .collect();
    let final_value = var("call_4");
    let context_exprs = vec![&final_value];

    let base_sat_after_binding = || {
        let setup_result = setup_verification_encoder(&VerificationSetup {
            requires: &requires,
            ensures: &ensures,
            context_exprs: &context_exprs,
            result_expr: None,
            ghost_context: Some(std::slice::from_ref(&ghost_alias)),
            logic_fns: None,
            mode_overrides: None,
            type_invariants: None,
            track: TrackLevel::Auto,
            timeout: Some(Duration::from_secs(2)),
            type_constants: None,
            closure_captures: None,
            adt_decls: None,
            adt_field_ranges: None,
        })
        .expect("setup should succeed");
        let mut encoder = setup_result.encoder;

        let ghost_term = encoder
            .encode_pure(&ghost_alias)
            .expect("ghost alias encodes");
        encoder.assert_term(ghost_term);
        crate::verify::shared_constraints::flatten_ghost_implications(
            &mut encoder,
            std::slice::from_ref(&ghost_alias),
        )
        .expect("ghost flatten succeeds");

        let mut final_values = HashMap::new();
        final_values.insert("call_4".to_string(), final_value.clone());
        super::bindings::bind_final_values(&mut encoder, &final_values, Some(&mutation_continued))
            .expect("binding final values should succeed");

        crate::verify::shared_constraints::assert_current_chain_alias_constraints(&mut encoder)
            .expect("alias constraints should succeed");
        super::super::solver_tail::assert_standard_axioms(&mut encoder, &requires, &[])
            .expect("standard axioms should succeed");

        encoder.set_timeout(Some(Duration::from_secs(2)));
        encoder.check_sat()
    };

    // The function-only base-SAT matrix exercises each intermediate stage.
    // This mut-borrow regression keeps the strongest combined stage plus the
    // goal-labelled core check below.  Re-solving every prefix here duplicated
    // six expensive quantified Seq queries without covering another path.
    let bind_alias_axioms_sat = base_sat_after_binding();
    assert!(
        !matches!(bind_alias_axioms_sat, SolveResult::Unsat(_)),
        "#2616 mut-borrow alias+axioms stage should not become structurally UNSAT"
    );

    let setup_result = setup_verification_encoder(&VerificationSetup {
        requires: &requires,
        ensures: &ensures,
        context_exprs: &context_exprs,
        result_expr: None,
        ghost_context: Some(std::slice::from_ref(&ghost_alias)),
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        track: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(2)),
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("setup should succeed");
    let mut encoder = setup_result.encoder;
    let ghost_term = encoder
        .encode_pure(&ghost_alias)
        .expect("ghost alias encodes");
    encoder.assert_term(ghost_term);
    crate::verify::shared_constraints::flatten_ghost_implications(
        &mut encoder,
        std::slice::from_ref(&ghost_alias),
    )
    .expect("ghost flatten succeeds");
    let mut final_values = HashMap::new();
    final_values.insert("call_4".to_string(), final_value.clone());
    super::bindings::bind_final_values(&mut encoder, &final_values, Some(&mutation_continued))
        .expect("binding final values should succeed");
    crate::verify::shared_constraints::assert_current_chain_alias_constraints(&mut encoder)
        .expect("alias constraints should succeed");
    super::super::solver_tail::assert_standard_axioms(&mut encoder, &requires, &[])
        .expect("standard axioms should succeed");

    encoder.push_scope().expect("push scope succeeds");
    let (unsat_result, core, vacuity) =
        encoder.with_negated_goal_label_prefix("__trust_wp_test_goal".to_string(), |encoder| {
            encoder.with_assertion_phase(
                crate::encoder::AssertionPhase::NegatedPostcondition,
                |encoder| {
                    let negated = super::super::encode_negated_postcondition(
                        encoder,
                        &ensures[0],
                        None,
                        None,
                    )
                    .expect("negated goal encodes");
                    encoder.assert_term(negated);
                },
            );
            (
                encoder.check_sat(),
                encoder.solver().try_get_unsat_core(),
                encoder.is_vacuous_unsat(),
            )
        });
    encoder.pop_scope().expect("pop scope succeeds");

    assert!(
        matches!(unsat_result, SolveResult::Unsat(_)),
        "#2616 unsat-core probe should stay UNSAT once the negated goal is asserted: got {unsat_result:?}"
    );
    let core = core.expect("#2616 unsat-core probe should expose the participating labels");
    assert!(
        core.iter()
            .any(|label| label.starts_with("__trust_wp_test_goal_")),
        "#2616 unsat core should include the negated-goal label, got {core:?}"
    );
    let vacuity =
        vacuity.expect("#2616 unsat-core probe should report whether the proof is vacuous");
    assert!(
        !vacuity,
        "#2616 unsat-core probe should remain non-vacuous once the goal label participates"
    );
}

fn seq_len_expr(seq: PureExpr) -> PureExpr {
    method_call(seq, "len", vec![])
}

fn seq_index_expr(seq: PureExpr, index: PureExpr) -> PureExpr {
    method_call(seq, "index_logic", vec![index])
}

fn seq_reverse_expr(seq: PureExpr) -> PureExpr {
    method_call(seq, "reverse", vec![])
}

fn seq_tail_reverse_push_front_expr(seq: PureExpr) -> PureExpr {
    let tail = method_call(
        seq.clone(),
        "subsequence",
        vec![int(1), seq_len_expr(seq.clone())],
    );
    method_call(
        seq_reverse_expr(tail),
        "push_front",
        vec![seq_index_expr(seq, int(0))],
    )
}

fn sequence_lasso_bare_forall_expr(seq: PureExpr) -> PureExpr {
    sequence_lasso_bare_forall_expr_with_reverse_index(seq, true)
}

fn sequence_lasso_bare_forall_expr_with_reverse_index(
    seq: PureExpr,
    use_previous_reverse_index: bool,
) -> PureExpr {
    let i = var("i");
    let reverse_index = if use_previous_reverse_index {
        sub(i.clone(), int(1))
    } else {
        i.clone()
    };
    forall(
        "i",
        implies(
            and(
                le(int(0), i.clone()),
                lt(i.clone(), seq_len_expr(seq.clone())),
            ),
            eq(
                seq_index_expr(seq_tail_reverse_push_front_expr(seq.clone()), i.clone()),
                ite(
                    eq(i.clone(), int(0)),
                    seq_index_expr(seq.clone(), int(0)),
                    seq_index_expr(seq_reverse_expr(seq), reverse_index),
                ),
            ),
        ),
    )
}

fn false_len_guard_reverse_index_assertion(seq: PureExpr) -> PureExpr {
    implies(
        eq(int(0), seq_len_expr(seq.clone())),
        eq(
            var("l"),
            seq_index_expr(
                seq_reverse_expr(seq.clone()),
                sub(seq_len_expr(seq), int(1)),
            ),
        ),
    )
}

#[test]
#[timeout(30000)]
fn test_proof_assert_false_len_guard_uses_solver_evidence() {
    let seq = var_with_sort("s_view", ExprSort::Seq);
    let requires = vec![gt(seq_len_expr(seq.clone()), int(0))];
    let ensures = vec![false_len_guard_reverse_index_assertion(seq)];
    let final_values = HashMap::new();

    let outcome = verify_mut_borrow_function_with_modes_outcome(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "false-guard proof_assert should verify: got {:?}",
        outcome.result
    );
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("false-guard proof should carry solver evidence");
    assert!(
        evidence.accepted_for_consumer,
        "false-guard proof must be backed by accepted solver evidence: {evidence:?}"
    );
    assert!(
        evidence.result.to_ascii_lowercase().contains("unsat"),
        "false-guard proof should record UNSAT evidence: {evidence:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_false_len_guard_rejects_missing_bound_fact() {
    let seq = var_with_sort("s_view", ExprSort::Seq);
    let ensure = false_len_guard_reverse_index_assertion(seq);

    assert!(
        super::super::function::obligation::implication_false_guard_candidate(&ensure, &[])
            .is_none(),
        "false-guard proof must require an explicit contradictory length fact"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_missing_guard() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(seq);

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &[]),
        "bare sequence-lasso forall must not take the structural path without s.len() > 0"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_wrong_guard_sequence() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let other = var_with_sort("t", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(seq);
    let requires = vec![gt(seq_len_expr(other), int(0))];

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path must require the guard for the same sequence"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_altered_body() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr_with_reverse_index(seq.clone(), false);
    let requires = vec![gt(seq_len_expr(seq), int(0))];

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path must reject an altered reverse index"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_shadowed_sequence_var() {
    let seq = var_with_sort("i", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(seq.clone());
    let requires = vec![gt(seq_len_expr(seq), int(0))];

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path must reject a bound index that shadows the sequence"
    );
}

#[test]
#[timeout(120000)]
fn test_proof_assert_sequence_lasso_bare_forall_uses_mut_borrow_structural_matcher() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let requires = vec![gt(seq_len_expr(seq.clone()), int(0))];
    let ensures = vec![sequence_lasso_bare_forall_expr(seq)];
    let final_values = HashMap::from([("unused".to_string(), var("unused"))]);

    let outcome = verify_mut_borrow_function_with_modes_outcome(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN (strict UNSAT certification gap): the verdict may demote
    // to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&outcome.result),
        "proof_assert-style sequence lasso forall should verify through mut_borrow: got {:?}",
        outcome.result
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_accepts_explicit_alias() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let alias = var_with_sort("s_view", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(alias.clone());
    let requires = vec![gt(seq_len_expr(seq.clone()), int(0)), eq(seq, alias)];

    assert!(
        super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path should accept an explicit equality alias"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_accepts_explicit_view_alias() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let alias = var_with_sort("s_view", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(alias.clone());
    let requires = vec![gt(seq_len_expr(seq.clone()), int(0)), eq(view(seq), alias)];

    assert!(
        super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path should accept a transparent view alias"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_implicit_alias() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let alias = var_with_sort("s_view", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(alias);
    let requires = vec![gt(seq_len_expr(seq), int(0))];

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path must not accept an alias without explicit equality"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_different_sequence_alias() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let other = var_with_sort("t", ExprSort::Seq);
    let alias = var_with_sort("s_view", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr(alias.clone());
    let requires = vec![gt(seq_len_expr(seq), int(0)), eq(other, alias)];

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path must reject aliases for a different guarded sequence"
    );
}

#[test]
#[timeout(30000)]
fn test_proof_assert_sequence_lasso_exact_matcher_rejects_aliased_altered_body() {
    let seq = var_with_sort("s", ExprSort::Seq);
    let alias = var_with_sort("s_view", ExprSort::Seq);
    let ensure = sequence_lasso_bare_forall_expr_with_reverse_index(alias.clone(), false);
    let requires = vec![gt(seq_len_expr(seq.clone()), int(0)), eq(seq, alias)];

    assert!(
        !super::obligation::sequence_lasso_proof_assert_matches_exact(&ensure, &requires),
        "sequence-lasso structural path must keep exact body matching through aliases"
    );
}

// ── Error-path regression tests (#2139) ──

/// Non-boolean postcondition must produce `EncodingError::Unsupported`, not a
/// panic or spurious `Ok`. The mut_borrow path reaches the shared
/// `is_definitely_non_bool` check through the pipeline; this exercises it
/// from the mut-borrow entry.
#[test]
#[timeout(30000)]
fn test_non_bool_postcondition_returns_encoding_error() {
    let final_values = HashMap::new();
    let requires = vec![];
    // An integer literal is "definitely non-bool"
    let ensures = vec![int(42)];

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values);
    let result = verify_mut_borrow_function_with_modes(request);

    let err = result.expect_err("non-boolean postcondition should produce EncodingError");
    let msg = err.to_string();
    assert!(
        msg.contains("postcondition") || msg.contains("boolean"),
        "error message should mention postcondition/boolean, got: {msg}"
    );
}

/// `mode_overrides` length mismatch is silently dropped (#2316, #2700).
/// The overrides are computed from the full logic_fn_defs set, but logic_fns
/// may be a filtered subset. Rather than returning an encoding error, the
/// overrides are dropped so filter_logic_functions_for_goal falls back to
/// default mode scoping.
#[test]
#[timeout(30000)]
fn test_mode_overrides_length_mismatch_drops_overrides_silently() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let final_values = HashMap::new();
    let requires = vec![];
    let ensures = vec![eq(var("v"), var("v"))];

    // One logic function, but two mode overrides — length mismatch
    let logic_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    let logic_fns = [logic_fn];
    let mode_overrides = [LogicMode::Open, LogicMode::Open]; // length 2 != 1

    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .logic_fns(Some(&logic_fns))
        .mode_overrides(Some(&mode_overrides));
    let result = verify_mut_borrow_function_with_modes(request);

    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}

// ── resolve assumptions (#2124) ──────────────────────────────────────

/// Resolve assumption `v_final == v_current` should make `^v == *v` verify
/// for an identity borrow (the simplest resolve case).
#[test]
#[timeout(30000)]
fn test_resolve_assumption_identity_borrow_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Postcondition: ^v == *v (final equals current)
    let ensures = vec![eq(final_expr(var("v")), deref(var("v")))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve assumption should make ^v == *v verify: got {result:?}"
    );
}

/// Regression for `final_borrows::reborrow_id`.
///
/// Driver extraction can hand the mut-borrow verifier an unannotated identity
/// return expression for `fn reborrow_id<T>(r: &mut T) -> &mut T { r }`.
/// The postcondition is whole-borrow equality, not `*result == *r`; the verifier
/// must keep the direct return equality from becoming a dereferenced-current
/// equality that leaves `result == r` unproved.
#[test]
#[timeout(30000)]
fn test_final_borrows_identity_return_whole_borrow_equality_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(var("r")));

    let ensures = vec![eq(var("result"), var("r"))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&var("r")))
            .resolve_assumptions(Some(vec!["r".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "identity &mut return should prove whole-borrow equality: got {result:?}"
    );
}

/// Resolve assumptions should not interfere with parameters that don't
/// appear in the resolve list (they still use function-scope resolution).
#[test]
#[timeout(30000)]
fn test_resolve_assumption_does_not_affect_non_listed_params() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // Postcondition: ^v == *v + 1 (computed final value, not identity)
    let ensures = vec![eq(final_expr(var("v")), add(deref(var("v")), int(1)))];

    // Empty resolve list — v should use function-scope final_values.
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).resolve_assumptions(Some(vec![])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty resolve list should not affect function-scope resolution: got {result:?}"
    );
}

/// With resolve assumption, the resolve constraint overrides the computed
/// final_value. This models the case where `extract_mut_borrow_body`
/// returns an identity `Deref(Var("v"))` (no forward computation) and
/// the resolve assertion provides the prophecy closure.
#[test]
#[timeout(30000)]
fn test_resolve_assumption_with_precondition_constraint() {
    // Precondition: *v > 0
    let requires = vec![gt(deref(var("v")), int(0))];

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Postcondition: ^v > 0
    // This should verify because resolve says v_final == v_current,
    // and the precondition says v_current > 0.
    let ensures = vec![gt(final_expr(var("v")), int(0))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve + precondition should prove ^v > 0: got {result:?}"
    );
}

/// Non-identity final_values + resolve assumption creates a contradiction
/// that makes everything trivially verifiable. This test demonstrates the
/// redundancy: even a clearly false postcondition verifies because the
/// constraints are unsatisfiable.
///
/// This documents that the resolve assumption mechanism is only sound when
/// the driver provides identity final_values (Deref(Var("v"))) for resolved
/// parameters. The driver must NOT emit resolve assumptions for parameters
/// with computed (non-identity) final values.
///
/// `emit_resolve_assertions` SKIPS resolve for non-identity final values, so
/// the contradiction does not occur (#2663). The false postcondition
/// `^v != ^v` simply fails (correctly), because there is no UNSAT base.
///
/// Re: #2124 (resolve assertion test coverage finding), #2663 (non-identity skip)
#[test]
#[timeout(30000)]
fn test_resolve_assumption_non_identity_creates_contradiction() {
    let mut final_values = HashMap::new();
    // Non-identity: function body computes v_final = *v + 1
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // Clearly false postcondition: ^v != ^v (always false)
    let ensures = vec![ne(final_expr(var("v")), final_expr(var("v")))];

    // With resolve assumption requested but SKIPPED (#2663) because final
    // value is non-identity. The resolve assertion v_final == v_current is
    // NOT emitted, so there is no contradiction. The postcondition simply
    // fails because ^v != ^v is always false.
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    // Resolve is skipped for non-identity final values, so
    // the base is SAT (no contradiction). The false postcondition ^v != ^v
    // correctly fails with a counterexample.
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "false postcondition should fail: got {result:?}"
    );
}

/// Without resolve assumptions, non-identity body with false postcondition
/// correctly fails. This is the baseline for the contradiction test above.
///
/// Re: #2124
#[test]
#[timeout(30000)]
fn test_no_resolve_assumption_non_identity_false_postcondition_fails() {
    let mut final_values = HashMap::new();
    // Non-identity: function body computes v_final = *v + 1
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // Postcondition: ^v == *v (should fail because v_final = *v + 1, not *v)
    let ensures = vec![eq(final_expr(var("v")), deref(var("v")))];

    // No resolve assumptions — function-scope encoding is used.
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).resolve_assumptions(None),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without resolve, ^v == *v should fail when body is *v + 1: got {result:?}"
    );
}

/// With resolve assumptions on an identity body, the same postcondition
/// that fails without resolve should succeed with resolve. This is the
/// key discriminating test: it isolates the resolve assertion's effect.
///
/// Re: #2124
#[test]
#[timeout(30000)]
fn test_resolve_assumption_identity_enables_otherwise_failing_postcondition() {
    let mut final_values = HashMap::new();
    // Identity: function body is v_final = *v (no computation)
    final_values.insert("v".to_string(), deref(var("v")));

    // Precondition: *v > 0 AND *v < 100
    let requires = vec![and(
        gt(deref(var("v")), int(0)),
        gt(int(100), deref(var("v"))),
    )];

    // Postcondition: ^v > 0 AND ^v < 100
    // With resolve: v_final == v_current, so ^v == *v, and precondition
    // constrains *v to (0,100). Should verify.
    let ensures = vec![and(
        gt(final_expr(var("v")), int(0)),
        gt(int(100), final_expr(var("v"))),
    )];

    // First verify: WITHOUT resolve, this should still work (identity body).
    let result_without = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).resolve_assumptions(None),
    )
    .expect("encoding should succeed");

    // WITH resolve: should also work.
    let result_with = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result_with, VerificationResult::Verified(_)),
        "resolve + precondition should prove bounded postcondition: got {result_with:?}"
    );

    // Document whether function-scope encoding alone is sufficient.
    // For identity bodies, it IS sufficient — this is the redundancy we found.
    // This assertion documents the behavior, not a correctness requirement.
    if matches!(result_without, VerificationResult::Verified(_)) {
        // Function-scope encoding already proves this for identity bodies.
        // The resolve assertion is redundant in this case.
    }
}

/// Regression for unnest-style nested mutable-borrow returns (#2583).
///
/// `fn unnest(x: &mut &mut u32) -> &mut u32 { *x }`
///
/// The return expression is `Deref(Var("x", MutRef(MutRef(Int))))`.
/// `bind_whole_mut_ref_result` must peel the outer MutRef layer (matching the
/// Deref wrapper) so that `result_current` and `result_final` are declared with
/// sort `Int`, not `__trust_wp_mutref::int`.
#[test]
#[timeout(30000)]
fn test_unnest_nested_mut_ref_return_sort() {
    let x_sort = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int))));
    let return_expr = deref(var_with_sort("x", x_sort));

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // Postconditions exercise result_current and result_final.
    // *result == *result is trivially true but forces the encoder to use
    // result_current (which would have the wrong sort without the fix).
    let ensures = vec![
        eq(deref(var("result")), deref(var("result"))),
        eq(final_expr(var("result")), final_expr(var("result"))),
    ];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed without sort conflict (#2583)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "unnest-style nested mut-ref return should verify: got {result:?}"
    );
}

/// Regression for unnest selector-domain alignment (#2585).
///
/// Full `unnest` postconditions that cross-project both `result` and `x`:
///   *result == **x, ^result == *^x, ^*x == ^^x
///
/// `test_unnest_nested_mut_ref_return_sort` (#2583) exercises only result self-projections.
/// This test exercises the full interaction between result and parameter
/// projections at different borrow depths, which triggers the selector-domain
/// sort mismatch when wrapper-derived names use raw annotations instead of
/// effective peeled annotations.
#[test]
#[timeout(30000)]
fn test_unnest_full_postconditions_selector_domain() {
    let x_sort = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int))));
    let return_expr = deref(var_with_sort("x", x_sort.clone()));

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // Full unnest postconditions (annotation-free in ensures, matching
    // the driver's output where postcondition vars may lack ExprSort):
    //   *result == **x  (current of result == current of current of x)
    //   ^result == *^x  (final of result == current of final of x)
    //   ^*x == ^^x      (final of current of x == final of final of x)
    let ensures = vec![
        eq(deref(var("result")), deref(deref(var("x")))),
        eq(final_expr(var("result")), deref(final_expr(var("x")))),
        eq(
            final_expr(deref(var("x"))),
            final_expr(final_expr(var("x"))),
        ),
    ];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed without selector-domain sort mismatch (#2585)");

    // SOUNDNESS PIN (borrows lent into the return value): `*x` (a reborrow of the inner
    // borrow) is returned; `^result == *^x` and `^*x == ^^x` need the caller link.
    // The identity `final_values` entry below is a driver shape ay must not
    // trust: the lent param is mutation-continued, and ay must not equate
    // `^result` with `*result`, so the prophecy clause is unprovable.
    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "a lent borrow's identity final must not prove a prophecy clause: got {result:?}"
    );
}

/// Regression for `final_borrows::unnesting_non_extensional`.
///
/// The live driver extracts `&mut **x` as an over-dereferenced return chain.
/// The escaped final nested reborrow must bind both result projections to
/// `*^x`, matching the transformed non-extensional postconditions.
#[test]
#[timeout(30000)]
fn test_final_borrows_unnesting_non_extensional_overderef_return_verifies() {
    let elem_sort = ExprSort::Int;
    let result_sort = ExprSort::MutRef(Box::new(elem_sort.clone()));
    let x_sort = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(elem_sort))));
    let x = var_with_sort("x", x_sort.clone());
    let result = var_with_sort("result", result_sort);

    let return_expr = deref(deref(deref(deref(x.clone()))));

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(x.clone()));

    let target = deref(final_expr(x));
    let ensures = vec![
        eq(final_expr(result.clone()), target.clone()),
        eq(deref(result), target),
    ];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed for final nested reborrow return");

    // SOUNDNESS PIN (borrows lent into the return value): `&mut **x` is
    // returned; `^result == *^x` is not a consequence of `^x == *x` (a false premise).
    // The identity `final_values` entry below is a driver shape ay must not
    // trust: the lent param is mutation-continued, and ay must not equate
    // `^result` with `*result`, so the prophecy clause is unprovable.
    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "a lent borrow's identity final must not prove a prophecy clause: got {result:?}"
    );
}

/// Regression for `final_borrows::index_mut_slice`.
///
/// The body and postcondition are the same indexed reborrow after canonicalizing
/// the mutable slice receiver from `v` to `*v`; this should not fall through to
/// quantified index axioms.
#[test]
#[timeout(30000)]
fn test_final_borrows_index_mut_direct_result_equality_verifies() {
    let v_sort = ExprSort::MutRef(Box::new(ExprSort::Seq));
    let result_sort = ExprSort::MutRef(Box::new(ExprSort::Int));
    let v = var_with_sort("v", v_sort);
    let v_untyped = var("v");
    let result = var_with_sort("result", result_sort);

    let return_expr = method_call(v_untyped, "index_logic", vec![int(12)]);
    let canonical_index = method_call(deref(v.clone()), "index_logic", vec![int(12)]);
    let ensures = vec![eq(result, canonical_index)];

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(v));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_borrows index_mut direct result equality should verify: got {result:?}"
    );
}

/// Regression for `final_borrows::select`.
///
/// Conditional whole-borrow return equalities should use the same direct-return
/// shortcut as plain `result == r` obligations.
#[test]
#[timeout(30000)]
fn test_final_borrows_select_conditional_direct_result_equality_verifies() {
    let mut_ref_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let r1 = var_with_sort("r1", mut_ref_int.clone());
    let r2 = var_with_sort("r2", mut_ref_int.clone());
    let result_ref = var_with_sort("result", mut_ref_int);

    let return_expr = ite(var("b"), r1.clone(), r2.clone());
    let ensures = vec![ite(
        var("b"),
        eq(result_ref.clone(), r1.clone()),
        eq(result_ref, r2.clone()),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("r1".to_string(), deref(r1));
    final_values.insert("r2".to_string(), deref(r2));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_borrows select direct conditional return should verify: got {result:?}"
    );
}

/// Regression for `final_borrows::box_reborrow_indirect`.
///
/// Identity final values for nested reference-like contents must expose
/// `x_final_current == x_current_current`, making an over-deref return equal to
/// the postcondition's final-box content.
#[test]
#[timeout(30000)]
fn test_final_borrows_box_reborrow_indirect_identity_nested_current_verifies() {
    let boxed_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let x_sort = ExprSort::MutRef(Box::new(boxed_int));
    let x = var_with_sort("x", x_sort);

    let return_expr = deref(deref(x.clone()));
    let ensures = vec![eq(var("result"), deref(final_expr(x.clone())))];

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(x));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_borrows box_reborrow_indirect shape should verify: got {result:?}"
    );
}

/// Regression for `final_borrows::reborrow_in_box`.
#[test]
#[timeout(30000)]
fn test_final_borrows_reborrow_in_box_identity_nested_current_verifies() {
    let elem_sort = ExprSort::Int;
    let result_sort = ExprSort::MutRef(Box::new(elem_sort.clone()));
    let boxed_int = ExprSort::MutRef(Box::new(elem_sort));
    let x_sort = ExprSort::MutRef(Box::new(boxed_int));
    let x = var_with_sort("x", x_sort);
    let result_ref = var_with_sort("result", result_sort);

    let return_expr = deref(deref(x.clone()));
    let ensures = vec![eq(result_ref, deref(final_expr(x.clone())))];

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(x));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_borrows reborrow_in_box shape should verify: got {result:?}"
    );
}

/// Regression for `take_max` sort downgrade (#2593).
///
/// ```rust
/// #[ensures(if *ma >= *mb { *mb == ^mb && result == ma }
///                    else { *ma == ^ma && result == mb })]
/// fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
///     if *ma >= *mb {
///         ma
///     } else {
///         mb
///     }
/// }
/// ```
///
/// The live driver-shaped request keeps the ITE branches as whole-borrow vars
/// and can also preserve those same `MutRef(Int)` vars in the branch condition.
/// The mut-borrow pipeline must canonicalize that condition to current-value
/// derefs while still returning the whole-borrow branches. Combined with the
/// setup fix, this keeps `_current` / `_current_view` on `Int` and makes the
/// compat `take_max` contract provable. (#2593)
#[test]
#[timeout(30000)]
fn test_take_max_conditional_mut_ref_return_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let ma = var_with_sort("ma", mr_int.clone());
    let mb = var_with_sort("mb", mr_int.clone());

    // Driver-shaped return_expr: if ma >= mb { ma } else { mb }
    // The result binding path must canonicalize the comparison to current
    // values without rewriting the returned branches away from whole borrows.
    let return_expr_val = ite(ge(ma.clone(), mb.clone()), ma.clone(), mb.clone());

    // final_values: identity (neither param is mutated)
    use crate::tests::helpers::not;
    // Driver shape for lent borrows: both params may be
    // returned, so no `final_values` entry is emitted for either; the
    // driver's path-gated resolutions (`lent_path_resolutions`, passed as
    // call assumptions) resolve only the borrow NOT returned on each path.
    let final_values: HashMap<String, trust_wp_core::formula::PureExpr> = HashMap::new();
    let requires = vec![
        implies(
            ge(deref(ma.clone()), deref(mb.clone())),
            eq(final_expr(mb.clone()), deref(mb.clone())),
        ),
        implies(
            not(ge(deref(ma.clone()), deref(mb.clone()))),
            eq(final_expr(ma.clone()), deref(ma.clone())),
        ),
    ];

    // ensures: if *ma >= *mb { *mb == ^mb && result == ma }
    //                   else  { *ma == ^ma && result == mb }
    // Uses Deref/Final for integer equality (no View wrapper for scalars).
    let result_var = var_with_sort("result", mr_int);
    let ensures = vec![ite(
        ge(deref(ma.clone()), deref(mb.clone())),
        and(
            eq(deref(mb.clone()), final_expr(mb.clone())),
            eq(result_var.clone(), ma.clone()),
        ),
        and(
            eq(deref(ma.clone()), final_expr(ma.clone())),
            eq(result_var, mb.clone()),
        ),
    )];

    let outcome = verify_mut_borrow_function_with_modes_outcome(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .return_expr(Some(&return_expr_val)),
    )
    .expect("encoding should succeed for take_max (#2593)");
    let replay = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.native_replay_json.clone())
        .unwrap_or_else(|| "native replay unavailable".to_string());
    let result = super::legacy_result_from_outcome(outcome);

    assert!(
        matches!(&result, VerificationResult::Verified(Some(proof)) if proof.is_fully_verified()),
        "take_max conditional mut-ref return needs a fully checked proof: got {result:?}\nAY_NATIVE_REPLAY_BEGIN\n{replay}\nAY_NATIVE_REPLAY_END"
    );
}

/// Sort-focused regression for `View(Deref(Var("ma", MutRef(Int))))` (#2593).
///
/// Encoding `View(Deref(Var("x", MutRef(Int))))` must declare `x_current_view`
/// with sort `Int`, not the whole-borrow sort `__trust_wp_mutref::int`. Without
/// the fix in `encode_view_expr`, the view path uses `infer_expr_sort_with_context`
/// instead of `effective_expr_annotation`, which doesn't peel the reference layer.
#[test]
#[timeout(5000)]
fn test_view_deref_mutref_int_declares_current_view_as_int() {
    use ay_dpll::api::Sort;

    let mut encoder = crate::encoder::AYEncoder::new_all();
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    // Encode View(Deref(Var("x", MutRef(Int)))) — this should declare
    // x_current_view with sort Int.
    let expr = view(deref(var_with_sort("x", mr_int)));
    let _term = encoder
        .encode_pure(&expr)
        .expect("encoding View(Deref(Var(MutRef(Int)))) should succeed");

    // x_current_view must be Int, not __trust_wp_mutref::int.
    let current_view_sort = encoder
        .var_sort("x_current_view")
        .expect("x_current_view should be declared");
    assert_eq!(
        *current_view_sort,
        Sort::Int,
        "x_current_view should be Int, not {:?} (#2593)",
        current_view_sort
    );

    // x_current must also be Int (declared by assert_view_identity).
    let current_sort = encoder
        .var_sort("x_current")
        .expect("x_current should be declared");
    assert_eq!(
        *current_sort,
        Sort::Int,
        "x_current should be Int, not {:?} (#2593)",
        current_sort
    );
}

// ── Vacuity diagnostic tests (#2663) ─────────────────────────────────

/// Model of `bug/682.rs` `add_some`: `#[ensures(^a > *a)]` with body `*a += 1`.
///
/// The final value of `a` is `*a + 1`, so the postcondition `^a > *a` is
/// provable as `*a + 1 > *a`. This should NOT produce a vacuous proof.
/// Vacuity would mean the base assertions are contradictory, which indicates
/// an encoding bug in the borrow model.
#[test]
#[timeout(30000)]
fn test_vacuity_bug_682_add_some_non_vacuous() {
    let mut final_values = HashMap::new();
    // body: *a += 1 => final a = *a + 1
    final_values.insert("a".to_string(), add(deref(var("a")), int(1)));

    // #[requires((*a)@ <= MAX / 2)] — simplified to *a <= 1000000
    let requires = vec![le(deref(var("a")), int(1_000_000))];
    // #[ensures(^a > *a)]
    let ensures = vec![gt(final_expr(var("a")), deref(var("a")))];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "add_some pattern should NOT produce a vacuous proof (base assertions should be consistent): got {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "add_some pattern should verify: ^a = *a + 1 > *a. Got {result:?}"
    );
}

/// Model of `bug/682.rs` `foo`: calls `add_some(a)` and then `proof_assert!(*a > *a_p)`.
///
/// The postcondition `^a > *a` from `add_some` becomes an assumption, plus
/// the snapshot value. This should verify non-vacuously.
#[test]
#[timeout(30000)]
fn test_vacuity_bug_682_foo_with_call_postcondition() {
    let mut final_values = HashMap::new();
    // After calling add_some(a), the final value is the post-call state.
    // The body captures the snapshot before the call and the state after.
    // Simplified model: final a is some value > *a (from add_some's postcondition)
    final_values.insert("a".to_string(), add(deref(var("a")), int(1)));

    // #[requires(*a == 3u64)]
    let requires = vec![eq(deref(var("a")), int(3))];
    // #[ensures(^a > *a)]
    let ensures = vec![gt(final_expr(var("a")), deref(var("a")))];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "foo pattern should NOT produce a vacuous proof: got {result:?}"
    );
}

/// Simple final-greater-than-current postcondition should not be vacuous
/// even without preconditions.
#[test]
#[timeout(30000)]
fn test_vacuity_simple_increment_non_vacuous() {
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), add(deref(var("x")), int(1)));

    let ensures = vec![gt(final_expr(var("x")), deref(var("x")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "simple increment should not be vacuous: got {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x + 1 > x should verify: got {result:?}"
    );
}

/// Identity final value with equality postcondition should verify non-vacuously.
#[test]
#[timeout(30000)]
fn test_vacuity_identity_final_value_non_vacuous() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("a")));

    let ensures = vec![eq(final_expr(var("a")), deref(var("a")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "identity final value should not be vacuous: got {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "^a = *a should verify when final_value is identity: got {result:?}"
    );
}

/// Regression for resolve assertion + non-identity final value contradiction (#2663).
///
/// When the driver sends both `final_values = {"a": *a + 1}` and
/// `resolve_assumptions = Some(["a"])`, the ay layer must not assert both:
///   - `a_final == a_current + 1` (from bind_final_values)
///   - `a_final == a_current` (from emit_resolve_assertions)
/// These are contradictory (`current + 1 == current` is UNSAT), making the base
/// UNSAT and triggering vacuous proof detection, so the resolve assertion is
/// skipped when the final value is non-identity (#2663).
#[test]
#[timeout(30000)]
fn test_vacuity_resolve_with_non_identity_final_is_non_vacuous() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), add(deref(var("a")), int(1)));

    let ensures = vec![gt(final_expr(var("a")), deref(var("a")))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["a".to_string()])),
    )
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "resolve + non-identity final must not be vacuous after fix (#2663): {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve with non-identity final should verify: {result:?}"
    );
}

/// Confirm that resolve assertion correctly fires for identity final values.
///
/// When the final value IS identity (`Deref(Var("a"))` = `*a`), the resolve
/// assertion `a_final == a_current` is consistent with `a_final == *a`
/// (since `*a` encodes as `a_current`). This should remain non-vacuous.
#[test]
#[timeout(30000)]
fn test_vacuity_resolve_with_identity_final_is_non_vacuous() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("a")));

    let ensures = vec![eq(final_expr(var("a")), deref(var("a")))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["a".to_string()])),
    )
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "resolve + identity final must not be vacuous: {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve with identity final should verify: {result:?}"
    );
}

/// Regression for prophecy writeback + mutation_continued contradiction (#5, bug/682).
///
/// Mirrors the failing program at the ay layer (no driver/MIR dependency):
///
/// ```text
/// #[requires((*a)@ <= u64::MAX@ / 2)]
/// #[ensures(^a > *a)]
/// fn add_some(a: &mut u64) { *a += 1; }
///
/// #[requires(*a == 3u64)]
/// #[ensures(^a > *a)]
/// pub fn foo(a: &mut u64) {
///     let _a_p = snapshot!(*a);
///     add_some(a);
/// }
/// ```
///
/// The driver registers `a` in `mutation_continued_params` (the body calls
/// `add_some(a)`), creates a reborrow `a_rb6 = &mut *a` for the call (so
/// `prophecy_writebacks = {"a_rb6": "a"}`), and merges the call's postcondition
/// `^a > *a` (rewritten with the reborrow's SSA names) into requires as a
/// call_assumption `Final(Var("a_rb6")) > Deref(Var("a_rb6"))`.
///
/// Pre-fix, `emit_prophecy_writebacks` unconditionally asserted
/// `a_current == a_rb6_final` and `a_rb6_current == a_current`. Combined with
/// `a_current == 3` (precondition) and the call_assumption
/// `a_rb6_final > a_rb6_current`, the base premises collapsed to `3 > 3`
/// (UNSAT) — which the vacuity guard demoted to Unknown. The fix skips the
/// `parent_current == child_final` writeback when the parent is in
/// `mutation_continued_params`.
#[test]
#[timeout(30000)]
fn test_vacuity_prophecy_writeback_with_mutation_continued_is_non_vacuous() {
    // Precondition `*a == 3` together with the call_assumption
    // `Final(a_rb6) > Deref(a_rb6)` (encoded post-rewrite into the reborrow's
    // SSA names) mirrors what the driver merges into requires for bug/682.
    let requires = vec![
        eq(deref(var("a")), int(3)),
        gt(final_expr(var("a_rb6")), deref(var("a_rb6"))),
    ];

    // Function-level postcondition: `^a > *a`.
    let ensures = vec![gt(final_expr(var("a")), deref(var("a")))];

    // `a` is mutation-continued: its `_final` is advanced by the
    // call_assumption (via the prophecy chain), not by an explicit final
    // value. Use an identity final value so `bind_final_values` does not
    // tie `a_final` to `a_current` (the #2663 path).
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("a")));

    let mut writebacks = HashMap::new();
    writebacks.insert("a_rb6".to_string(), "a".to_string());

    let mutation_continued = HashSet::from(["a".to_string()]);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .prophecy_writebacks(Some(writebacks))
            .mutation_continued_params(Some(mutation_continued)),
    )
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "prophecy writeback + mutation_continued must not collapse base \
         premises to UNSAT after fix (#5, bug/682): {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "prophecy writeback for mutation-continued parent should verify \
         `^a > *a` via the call_assumption: {result:?}"
    );
}

// ── View-level resolve propagation tests (#2673) ─────────────────────

/// Resolve propagation to view level: `(*v)@ == (^v)@` for resolved borrows.
///
/// When a borrow is resolved (identity final value + resolve assertion), the
/// view of the current value should equal the view of the final value. Without
/// the view-level propagation in `emit_resolve_view_propagation`, the solver
/// must derive `v_current_view == v_final_view` from `v_current == v_final`
/// through UF congruence, which AUFLIA may not always achieve.
#[test]
#[timeout(30000)]
fn test_resolve_view_propagation_current_equals_final_view() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Postcondition: (*v)@ == (^v)@ — view of current equals view of final
    let ensures = vec![eq(view(deref(var("v"))), view(final_expr(var("v"))))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve + identity final should make (*v)@ == (^v)@ verify via view propagation: {result:?}"
    );
}

/// Writeback view propagation: reborrow's view aliases parent's view.
///
/// For `z = &mut *y` (identity reborrow), `(*z)@ == (*y)@` should hold.
/// The scalar writeback `z_current == y_current` combined with the new
/// `emit_writeback_view_propagation` makes this provable.
#[test]
#[timeout(30000)]
fn test_writeback_view_propagation_child_view_equals_parent() {
    use trust_wp_core::formula::BorrowFinality;

    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("z".to_string(), deref(var("z")));

    // Postcondition: (*z)@ == (*y)@ (child view equals parent view)
    let ensures = vec![eq(view(deref(var("z"))), view(deref(var("y"))))];

    let mut writebacks = HashMap::new();
    writebacks.insert("z".to_string(), "y".to_string());

    let mut finality = HashMap::new();
    finality.insert("z".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "writeback view propagation should make (*z)@ == (*y)@ verify: {result:?}"
    );
}

/// Soundness (vacuous whole-Seq equality): a `&mut Vec` param passed by
/// reborrow to an un-advanced mutating call (`v.extend(w)`) is
/// mutation-continued; its final value is constrained ONLY by the callee
/// postcondition, which here permits `(^v)@ != (*v)@`. The whole-Seq
/// equality `(^v)@ == (*v)@` must therefore NOT verify.
#[test]
#[timeout(120000)]
fn s25_extend_mutation_continued_whole_seq_equality_is_not_vacuous() {
    use trust_wp_core::formula::intern_sort_name;
    let vec_id = intern_sort_name("std::vec::Vec");
    let v = var_with_sort("v", ExprSort::MutRef(Box::new(ExprSort::Datatype(vec_id))));
    let w = var_with_sort("w", ExprSort::Datatype(vec_id));
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(v.clone()));
    let mutation_continued = HashSet::from(["v".to_string()]);
    let requires = vec![
        eq(
            view(final_expr(v.clone())),
            method_call(view(v.clone()), "concat", vec![view(w.clone())]),
        ),
        eq(
            method_call(view(final_expr(v.clone())), "len", vec![]),
            add(
                method_call(view(v.clone()), "len", vec![]),
                method_call(view(w.clone()), "len", vec![]),
            ),
        ),
        eq(final_expr(v.clone()), final_expr(var("v_rb4"))),
        PureExpr::Bool(true),
        PureExpr::Bool(true),
    ];
    let ensures = vec![eq(view(final_expr(v.clone())), view(deref(v.clone())))];
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mutation_continued)),
    );
    eprintln!("S25 extend result: {result:?}");
    assert!(
        !matches!(result, Ok(VerificationResult::Verified(_))),
        "(^v)@ == (*v)@ after extend must not verify: {result:?}"
    );
}
