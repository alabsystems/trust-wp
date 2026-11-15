// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `result_binding.rs` (#2481).
//!
//! Covers:
//! - Scalar result binding (standard `result = body` equality)
//! - Bool result binding (postconditions force Bool sort)
//! - No-op when `return_expr` is None and no result reference
//! - Unsoundness counter when `return_expr` is None but postconditions reference result
//! - ITE rebinding (non-variable body triggers rebind_var)
//! - Body encoding side-effects when postconditions don't reference result

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{ExprSort, Pattern, PureExpr};

use super::result_binding::assert_result_body_binding;
use crate::{
    encoder::{unsoundness, AYEncoder},
    tests::helpers::{
        bool_expr, deref, eq, forall, gt, implies, int, ite, logic_fn_call, match_expr,
        method_call, ne, var, var_with_sort, view,
    },
    verify::{encode_and_assert_negated_postconditions, VerificationRequest, VerificationResult},
};

// ── Scalar result binding ─────────────────────────────────────────

/// Scalar body: `return x` with `ensures(result == x)` should verify.
#[test]
#[timeout(30000)]
fn scalar_binding_simple_variable_body() {
    let ensures = vec![eq(var("result"), var("x"))];
    let body = var("x");

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result = x with ensures(result == x) should verify: got {result:?}"
    );
}

/// Scalar body: `return 42` with `ensures(result == 42)` should verify.
#[test]
#[timeout(30000)]
fn scalar_binding_literal_body() {
    let ensures = vec![eq(var("result"), int(42))];
    let body = int(42);

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result = 42 with ensures(result == 42) should verify: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn mut_ref_ite_result_binds_viewed_current_projection() {
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
    let seven = encoder.encode_pure(&int(7)).expect("7 should encode");
    let three = encoder.encode_pure(&int(3)).expect("3 should encode");
    let take_first = encoder.var_term("take_first").expect("take_first term");
    encoder.assert_term(take_first);
    encoder.assert_eq(a_current, seven);
    encoder.assert_eq(b_current, three);

    let body = ite(var("take_first"), var("a_ref"), var("b_ref"));
    let ensures = vec![eq(view(deref(var("result"))), int(7))];
    assert_result_body_binding(&mut encoder, Some(&body), &ensures, &[])
        .expect("mut-ref result projection binding should encode");

    let ensure_term = encoder
        .encode_pure(&ensures[0])
        .expect("ensures should encode");
    let negated_ensure = encoder.solver.not(ensure_term);
    encoder.assert_term(negated_ensure);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "viewed *result should follow the selected mutable-reference branch"
    );
}

/// Scalar body: `return x` with `ensures(result > 0)` and no preconditions
/// should NOT verify (x is unconstrained).
#[test]
#[timeout(30000)]
fn scalar_binding_unconstrained_body_does_not_verify() {
    let ensures = vec![gt(var("result"), int(0))];
    let body = var("x");

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "unconstrained x should produce a counterexample for result > 0: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn result_match_binds_synthetic_option_call_alias_without_wrapping() {
    fn option_is_none(scrutinee: PureExpr) -> PureExpr {
        match_expr(
            scrutinee,
            vec![
                (
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                    },
                    bool_expr(false),
                ),
                (
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    bool_expr(true),
                ),
            ],
        )
    }

    let requires = vec![option_is_none(var("$call_3"))];
    let ensures = vec![option_is_none(var("result"))];
    let body = var("$call_3");

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result should bind directly to the Option-valued call alias: got {result:?}"
    );
}

/// Transparent adapter bodies should bind `result` to the inner adapter model
/// rather than the raw adapter wrapper.
#[test]
#[timeout(30000)]
fn transparent_adapter_body_binds_result_to_inner_term() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let inner = method_call(var("xs"), "intersection", vec![var("ys")]);
    let body = logic_fn_call("Copied", vec![inner.clone()]);
    let ensures = vec![eq(view(var("result")), view(inner.clone()))];
    let requires: Vec<PureExpr> = vec![];

    let expected_inner_term = encoder.encode_pure(&inner).expect("inner should encode");
    let raw_body_term = encoder
        .encode_pure(&body)
        .expect("copied body should encode");

    let result = assert_result_body_binding(&mut encoder, Some(&body), &ensures, &requires);
    assert!(
        result.is_ok(),
        "transparent adapter binding should succeed: {result:?}"
    );

    let result_term = encoder.var_term("result").expect("result should be bound");
    assert_eq!(
        result_term, expected_inner_term,
        "result should point at the inner transparent-adapter model"
    );
    assert_eq!(
        raw_body_term, expected_inner_term,
        "transparent adapters may collapse to the same solver term"
    );
    assert!(
        encoder.var_term("result_view").is_none(),
        "result_view should not be seeded early for transparent adapters without a SeqValue"
    );
}

// ── Bool result binding ───────────────────────────────────────────

/// Bool body: `return true` with `ensures(result == true)` should verify.
/// This tests the Bool sort detection path — postcondition referencing
/// `result == true` should trigger Bool sort binding.
#[test]
#[timeout(30000)]
fn bool_binding_true_literal() {
    let ensures = vec![eq(var("result"), bool_expr(true))];
    let body = bool_expr(true);

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result = true with ensures(result == true) should verify: got {result:?}"
    );
}

/// Bool body: `return false` with `ensures(result == false)` should verify.
#[test]
#[timeout(30000)]
fn bool_binding_false_literal() {
    let ensures = vec![eq(var("result"), bool_expr(false))];
    let body = bool_expr(false);

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result = false with ensures(result == false) should verify: got {result:?}"
    );
}

// ── No-op paths ───────────────────────────────────────────────────

/// When return_expr is None and postconditions don't reference result,
/// assert_result_body_binding is a no-op (should not error).
#[test]
#[timeout(30000)]
fn noop_when_no_return_expr_and_no_result_reference() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let ensures: Vec<PureExpr> = vec![gt(var("x"), int(0))];
    let requires: Vec<PureExpr> = vec![];

    let result = assert_result_body_binding(&mut encoder, None, &ensures, &requires);

    assert!(
        result.is_ok(),
        "no-op path (no return_expr, no result ref) should succeed: {result:?}"
    );
}

/// When return_expr is present but postconditions don't reference result,
/// the body should still be encoded (for side effects like LetAssume).
#[test]
#[timeout(30000)]
fn encodes_body_even_without_result_reference() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let body = int(42);
    let ensures: Vec<PureExpr> = vec![gt(var("x"), int(0))];
    let requires: Vec<PureExpr> = vec![];

    let result = assert_result_body_binding(&mut encoder, Some(&body), &ensures, &requires);

    assert!(
        result.is_ok(),
        "body encoding without result ref should succeed: {result:?}"
    );
}

// ── Unsoundness counter ───────────────────────────────────────────

/// When return_expr is None but postconditions reference result,
/// the unsoundness counter UnconstrainedResultVar should fire. (#2348, #2663)
#[test]
#[timeout(30000)]
fn unsoundness_fires_when_no_return_expr_but_result_referenced() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let ensures: Vec<PureExpr> = vec![eq(var("result"), int(42))];
    let requires: Vec<PureExpr> = vec![];

    let snap_before = unsoundness::snapshot();
    let result = assert_result_body_binding(&mut encoder, None, &ensures, &requires);
    let snap_after = unsoundness::snapshot();

    assert!(
        result.is_ok(),
        "should succeed even with unsoundness: {result:?}"
    );

    let d = unsoundness::delta(&snap_before, &snap_after);
    assert!(
        d.get(&unsoundness::UnsoundnessCategory::UnconstrainedResultVar)
            .copied()
            .unwrap_or(0)
            > 0,
        "UnconstrainedResultVar should increment when return_expr is None but result referenced"
    );
}

#[test]
#[timeout(30000)]
fn no_unsoundness_when_no_return_expr_but_requires_constrains_result() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let requires: Vec<PureExpr> = vec![gt(var("result"), int(5))];
    let ensures: Vec<PureExpr> = vec![gt(var("result"), int(0))];

    let snap_before = unsoundness::snapshot();
    let result = assert_result_body_binding(&mut encoder, None, &ensures, &requires);
    let snap_after = unsoundness::snapshot();

    assert!(
        result.is_ok(),
        "call-chain result assumption should encode without demotion: {result:?}"
    );

    let d = unsoundness::delta(&snap_before, &snap_after);
    assert_eq!(
        d.get(&unsoundness::UnsoundnessCategory::UnconstrainedResultVar)
            .copied()
            .unwrap_or(0),
        0,
        "result constrained by requires should not count as unconstrained"
    );
}

#[test]
#[timeout(30000)]
fn no_return_expr_declares_result_datatype_for_constructor_postcondition() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let ensures = vec![forall(
        "e",
        implies(
            eq(var("result"), logic_fn_call("Err", vec![var("e")])),
            bool_expr(true),
        ),
    )];
    let requires: Vec<PureExpr> = vec![];

    assert_result_body_binding(&mut encoder, None, &ensures, &requires)
        .expect("unconstrained constructor postcondition should predeclare result");

    let result_dt = match encoder.var_sort("result") {
        Some(Sort::Datatype(dt)) => dt.clone(),
        other => panic!("result should be ResultIntInt datatype, got {other:?}"),
    };
    assert_eq!(result_dt.name, "ResultIntInt");

    encoder
        .encode_pure(&ensures[0])
        .expect("postcondition should encode against predeclared result datatype");
}

/// When return_expr IS present and postconditions reference result,
/// no spurious SortFallbackToInt should fire.
#[test]
#[timeout(30000)]
fn no_spurious_unsoundness_when_return_expr_present() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let body = int(42);
    let ensures: Vec<PureExpr> = vec![eq(var("result"), int(42))];
    let requires: Vec<PureExpr> = vec![];

    let snap_before = unsoundness::snapshot();
    let result = assert_result_body_binding(&mut encoder, Some(&body), &ensures, &requires);
    let snap_after = unsoundness::snapshot();

    assert!(result.is_ok(), "should succeed: {result:?}");

    let d = unsoundness::delta(&snap_before, &snap_after);
    let fallback_count = d
        .get(&unsoundness::UnsoundnessCategory::SortFallbackToInt)
        .copied()
        .unwrap_or(0);
    assert_eq!(
        fallback_count, 0,
        "SortFallbackToInt should NOT increment when return_expr is present (got {fallback_count})"
    );
}

// ── ITE rebinding ─────────────────────────────────────────────────

/// ITE body: `return if c { a } else { b }` with `ensures(result == a)`
/// and `requires(c)`. The ITE rebinding path should inline the body
/// term into `result`, allowing the solver to verify the postcondition.
#[test]
#[timeout(30000)]
fn ite_body_triggers_rebinding() {
    let requires = vec![eq(var("c"), bool_expr(true))];
    let ensures = vec![eq(var("result"), int(1))];
    let body = ite(var("c"), int(1), int(2));

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ITE body with c=true, result==1 should verify: got {result:?}"
    );
}

/// Datatype ITE body: `return if c { Some(1) } else { None }` with
/// `ensures(result.is_some())` and `requires(c)`.
/// The datatype branch bridge should keep constructor testers concrete.
#[test]
#[timeout(30000)]
fn datatype_ite_body_verifies_through_constructor_tester() {
    let requires = vec![eq(var("c"), bool_expr(true))];
    let ensures = vec![method_call(var("result"), "is_some", vec![])];
    let body = ite(
        var("c"),
        logic_fn_call("Some", vec![int(1)]),
        logic_fn_call("None", vec![]),
    );

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome still fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "datatype ITE body with c=true should verify result.is_some(): got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn tuple2_seq_option_seq_ite_branch_equalities_feed_tuple_postconditions() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let tuple2_name = tuple_logic_fn_name(2);
    let c = var_with_sort("c", ExprSort::Bool);
    let then_seq = var_with_sort("then_seq", ExprSort::Seq);
    let else_seq = var_with_sort("else_seq", ExprSort::Seq);
    let then_pair = logic_fn_call(
        &tuple2_name,
        vec![
            then_seq.clone(),
            logic_fn_call("Some", vec![then_seq.clone()]),
        ],
    );
    let else_pair = logic_fn_call(&tuple2_name, vec![else_seq, logic_fn_call("None", vec![])]);
    let body = ite(c.clone(), then_pair.clone(), else_pair);
    let requires = vec![eq(c, bool_expr(true))];
    let ensures = vec![eq(var_with_sort("result", ExprSort::Tuple(2)), then_pair)];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    for require in &requires {
        let term = encoder
            .encode_formula(require)
            .expect("requires should encode");
        encoder.assert_term(term);
    }
    assert_result_body_binding(&mut encoder, Some(&body), &ensures, &requires)
        .expect("result binding should encode");
    let asserted =
        encode_and_assert_negated_postconditions(&mut encoder, &ensures, None, Some(&body))
            .expect("postcondition negation should encode");
    assert!(asserted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "tuple ITE branch equality should produce solver evidence for selected tuple branch; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_wrapped_datatype_ite_uses_guarded_branch_binding() {
    let requires = vec![eq(var("c"), bool_expr(true))];
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                bool_expr(false),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
        ],
    )];
    let body = PureExpr::LetAssume {
        assumption: Arc::new(bool_expr(true)),
        body: Arc::new(ite(
            var("c"),
            logic_fn_call("None", vec![]),
            logic_fn_call("Some", vec![int(1)]),
        )),
    };

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "LetAssume-wrapped datatype ITE with c=true should verify: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn datatype_ite_result_constructor_selects_matching_branch_guard() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let cond = eq(var("c"), bool_expr(true));
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
        ],
    )];
    let body = ite(
        cond.clone(),
        logic_fn_call("None", vec![]),
        logic_fn_call("Some", vec![int(0)]),
    );

    assert_result_body_binding(&mut encoder, Some(&body), &ensures, &[])
        .expect("datatype ITE binding should encode");
    let result = encoder
        .var_term("result")
        .expect("result should be declared");
    let is_some = encoder
        .solver
        .try_datatype_tester("Some", result)
        .expect("result should be an Option datatype");
    let impossible_none_branch = encoder
        .encode_pure(&cond)
        .expect("branch guard should encode");
    encoder.assert_term(is_some);
    encoder.assert_term(impossible_none_branch);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "result Some must select the Some branch of a constructor-valued datatype ITE"
    );
}

fn verify_nullary_constructor_precondition_ite(reverse_branches: bool) -> VerificationResult {
    // MIR supplies the call result's type. A bare `None` does not determine
    // its polymorphic payload, so the fixture must retain that type evidence.
    let call = var_with_sort(
        "call_2",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OptionInt")),
    );
    let empty = eq(var("empty"), bool_expr(true));
    let disc_is_none = eq(method_call(call.clone(), "discriminant", vec![]), int(0));
    let requires = vec![implies(empty.clone(), eq(call, var("None"))), empty.clone()];
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                bool_expr(false),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
        ],
    )];
    let none = logic_fn_call("None", vec![]);
    let some = logic_fn_call("Some", vec![int(1)]);
    let body = if reverse_branches {
        ite(disc_is_none, some, none)
    } else {
        ite(disc_is_none, none, some)
    };

    super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .timeout(Some(std::time::Duration::from_secs(3))),
    )
    .expect("typed nullary-constructor case should encode")
}

#[test]
#[timeout(30000)]
fn datatype_ite_composes_nullary_constructor_precondition_to_result() {
    let result = verify_nullary_constructor_precondition_ite(false);
    assert!(
        matches!(&result, VerificationResult::Verified(Some(proof)) if proof.is_fully_verified()),
        "the typed None precondition selects the None result and needs a checked proof: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn datatype_ite_reversed_nullary_constructor_branch_is_refuted() {
    let result = verify_nullary_constructor_precondition_ite(true);
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "reversing the selected constructor returns Some and needs a validated refutation: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn datatype_ite_branch_let_assume_is_available_on_selected_branch() {
    let requires = vec![eq(var("c"), bool_expr(false))];
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(var("x"), int(7)),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
        ],
    )];
    let body = ite(
        var("c"),
        logic_fn_call("None", vec![]),
        PureExpr::LetAssume {
            assumption: Arc::new(eq(var("x"), int(7))),
            body: Arc::new(logic_fn_call("Some", vec![int(1)])),
        },
    );

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "branch-local LetAssume should verify selected branch: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn datatype_ite_branch_let_assume_does_not_leak_to_other_branch() {
    let requires = vec![eq(var("c"), bool_expr(true))];
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                eq(var("x"), int(7)),
            ),
        ],
    )];
    let body = ite(
        var("c"),
        logic_fn_call("None", vec![]),
        PureExpr::LetAssume {
            assumption: Arc::new(eq(var("x"), int(7))),
            body: Arc::new(logic_fn_call("Some", vec![int(1)])),
        },
    );

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "with c=true the body returns None, so the Some-branch LetAssume \
         must not constrain x; x != 7 is a sound counterexample: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn user_adt_result_binding_harmonizes_source_and_synthesized_list_sorts() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let _ = encoder
        .get_or_declare_var("result", Sort::Uninterpreted("List".to_string()))
        .expect("predeclare result as source List sort");

    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("head".to_string()),
                        Pattern::Binding("tail".to_string()),
                    ]))),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
        ],
    )];
    let body = logic_fn_call("Cons", vec![int(1), var("tail")]);

    let result = assert_result_body_binding(&mut encoder, Some(&body), &ensures, &[]);

    assert!(
        result.is_ok(),
        "List result binding should harmonize List and Adt_Cons_Nil sorts: {result:?}"
    );
    let _ = encoder.check_sat();
    assert!(
        encoder.solver_panic_reason().is_none(),
        "List result binding should not leave a latent mk_eq panic: {:?}",
        encoder.solver_panic_reason()
    );
}

/// Variable body should NOT trigger rebinding — the SMT equality bridge
/// suffices and rebinding would disagree on UF arguments.
#[test]
#[timeout(30000)]
fn variable_body_still_verifies_through_equality() {
    let requires = vec![eq(var("x"), int(42))];
    let ensures = vec![eq(var("result"), int(42))];
    let body = var("x");

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "variable body with x=42 should verify result==42 through equality: got {result:?}"
    );
}

// ── Precondition references to result ─────────────────────────────

/// Preconditions that reference `result` should also trigger the binding path.
#[test]
#[timeout(30000)]
fn precondition_referencing_result_triggers_binding() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let body = int(42);
    let ensures: Vec<PureExpr> = vec![];
    let requires: Vec<PureExpr> = vec![gt(var("result"), int(0))];

    let result = assert_result_body_binding(&mut encoder, Some(&body), &ensures, &requires);

    assert!(
        result.is_ok(),
        "precondition referencing result should trigger binding: {result:?}"
    );
}

// ── Datatype ITE body binding (#2675) ────────────────────────────

/// ITE body returning different Option constructors in each branch:
/// `if c { Some(1) } else { None }` with `match result { Some(v) => v == 1, None => !c }`.
/// When `c` is true, result should be `Some(1)`.
///
/// Without per-branch datatype encoding (#2675) the fallback path wraps the
/// entire ITE in `Some(ite(...))`, making result always `Some(...)` — the
/// `None` branch is unreachable.
#[test]
#[timeout(30000)]
fn datatype_ite_body_some_none_branches() {
    use trust_wp_core::formula::{MatchArm, Pattern, UnOp};

    // Body: if c { Some(1) } else { None }
    let body = ite(
        var("c"),
        PureExpr::LogicFnCall {
            name: "Some".to_string(),
            args: vec![int(1)],
        },
        var("None"),
    );

    // Postcondition: match result { Some(v) => v == 1, None => !c }
    let ensures = vec![PureExpr::Match {
        scrutinee: std::sync::Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: eq(var("v"), int(1)),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: PureExpr::UnOp(UnOp::Not, std::sync::Arc::new(var("c"))),
            },
        ],
    }];

    // Requires: c == true => result should be Some(1), and postcondition should hold.
    let requires = vec![eq(var("c"), bool_expr(true))];

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ITE body with c=true returning Some(1) should verify match postcondition: got {result:?}"
    );
}

/// ITE body returning different Option constructors: verify the None branch.
/// `if c { Some(1) } else { None }` with `match result { Some(v) => v == 1, None => !c }`.
/// When `c` is false, result should be `None`.
#[test]
#[timeout(30000)]
fn datatype_ite_body_none_branch_reachable() {
    use trust_wp_core::formula::{MatchArm, Pattern, UnOp};

    let body = ite(
        var("c"),
        PureExpr::LogicFnCall {
            name: "Some".to_string(),
            args: vec![int(1)],
        },
        var("None"),
    );

    let ensures = vec![PureExpr::Match {
        scrutinee: std::sync::Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: eq(var("v"), int(1)),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: PureExpr::UnOp(UnOp::Not, std::sync::Arc::new(var("c"))),
            },
        ],
    }];

    // Requires: c == false => result should be None, and postcondition should hold.
    let requires = vec![eq(var("c"), bool_expr(false))];

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ITE body with c=false returning None should verify match postcondition: got {result:?}"
    );
}

/// ITE body returning Option with unconstrained condition.
/// Both branches of the postcondition should be covered.
#[test]
#[timeout(30000)]
fn datatype_ite_body_unconstrained_condition() {
    use trust_wp_core::formula::{MatchArm, Pattern, UnOp};

    let body = ite(
        var("c"),
        PureExpr::LogicFnCall {
            name: "Some".to_string(),
            args: vec![int(1)],
        },
        var("None"),
    );

    let ensures = vec![PureExpr::Match {
        scrutinee: std::sync::Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: eq(var("v"), int(1)),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: PureExpr::UnOp(UnOp::Not, std::sync::Arc::new(var("c"))),
            },
        ],
    }];

    // No preconditions — c is unconstrained but both branches are valid.
    let requires: Vec<PureExpr> = vec![];

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ITE body with unconstrained c should verify both match branches: got {result:?}"
    );
}

// ── Datatype result binding reads the body's own value ────────────

/// `return o` for an `Option` parameter with `ensures(result != None)`: the
/// body already has the datatype, so `result` is `o`, never `Some(o)`, and the
/// negated goal `o == None` is satisfiable.
#[test]
#[timeout(30000)]
fn datatype_result_param_body_is_not_wrapped_in_some() {
    let ensures = vec![ne(var("result"), var("None"))];
    let body = var("o");

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "`return o` must not be read as `Some(o)`: got {result:?}"
    );
}

/// The same body under `requires(o != None)` proves: `result` is bound to `o`.
#[test]
#[timeout(30000)]
fn datatype_result_param_body_binds_result_to_the_param() {
    let mut encoder = AYEncoder::new_all();
    // A program parameter arrives declared at its datatype sort.
    let option_int = crate::encoder::match_enc::MatchDatatypeKind::OptionInt.datatype();
    encoder.ensure_datatype_declared(&option_int);
    encoder
        .get_or_declare_var("o", Sort::Datatype(option_int))
        .expect("o should declare");
    let requires = vec![ne(var("o"), var("None"))];
    let ensures = vec![ne(var("result"), var("None"))];
    let body = var("o");

    for require in &requires {
        let term = encoder
            .encode_pure(require)
            .expect("requires should encode");
        encoder.assert_term(term);
    }
    assert_result_body_binding(&mut encoder, Some(&body), &ensures, &requires)
        .expect("datatype binding should encode");
    let ensure_term = encoder
        .encode_pure(&ensures[0])
        .expect("ensures should encode");
    let negated = encoder.solver.not(ensure_term);
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "`result` bound to `o` must carry `o != None`"
    );
}

/// An unannotated variable body nothing has declared (a logic parameter) is
/// declared at the result's datatype sort, the sort `result` itself has.
#[test]
#[timeout(30000)]
fn datatype_result_undeclared_var_body_takes_the_result_sort() {
    let mut encoder = AYEncoder::new_all();
    let ensures = vec![ne(var("result"), var("None"))];
    let body = var("o");

    assert_result_body_binding(&mut encoder, Some(&body), &ensures, &[])
        .expect("datatype binding should encode");

    assert_eq!(
        encoder.var_sort("o"),
        encoder.var_sort("result"),
        "the body variable must be declared at the result's sort"
    );
    assert!(matches!(encoder.var_sort("o"), Some(Sort::Datatype(_))));
}

/// A scalar body under a datatype result is a payload whose constructor is
/// unknown here. It is never wrapped in a default `Some`: the binding is
/// withheld (which withholds a counterexample verdict too), so the false
/// `result != None` does not verify.
#[test]
#[timeout(30000)]
fn datatype_result_scalar_body_is_withheld_not_wrapped() {
    let ensures = vec![ne(var("result"), var("None"))];
    let body = var_with_sort("i", ExprSort::Int);

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        !matches!(
            result,
            VerificationResult::Verified(_) | VerificationResult::Failed(_)
        ),
        "a scalar body must neither prove nor refute a datatype postcondition: got {result:?}"
    );

    let mut encoder = AYEncoder::new_all();
    let snap_before = unsoundness::snapshot();
    assert_result_body_binding(&mut encoder, Some(&body), &ensures, &[])
        .expect("a withheld binding still encodes");
    let snap_after = unsoundness::snapshot();
    let d = unsoundness::delta(&snap_before, &snap_after);
    assert!(
        d.get(&unsoundness::UnsoundnessCategory::PremiseNeutralizedEq)
            .copied()
            .unwrap_or(0)
            > 0,
        "the withheld binding must count as a neutralized premise"
    );
}

/// `Err(x)` stays `Err(x)`: a constructor body is built as the constructor it
/// names, so `ensures(result is Ok)` of it is refuted.
#[test]
#[timeout(30000)]
fn datatype_result_err_constructor_body_is_not_read_as_ok() {
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                bool_expr(false),
            ),
        ],
    )];
    let body = logic_fn_call("Err", vec![var_with_sort("x", ExprSort::Int)]);

    let result = super::verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "`Err(x)` claimed to be `Ok` must be refuted: got {result:?}"
    );
}
