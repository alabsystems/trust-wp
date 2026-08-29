// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;
use crate::verify::assert_standard_axioms;

// --- deep_model + alias constraint integration tests (#2117) ---

/// Models `gt_or_le(x: &i32, y: &i32) -> bool` from ord_trait.rs.
///
/// The body computes `*x >= *y` via `PartialOrd::ge`, whose spec resolves to
/// `return_expr = View(Var("x")) >= View(Var("y"))` (the `@` operator on i32
/// is identity). The postcondition is
/// `result == (deep_model(*y) <= deep_model(*x))`.
///
/// For this to verify, the full chain must connect:
///   x_view = x  (view identity for scalars)
///   x_current = x  (by-value alias constraint)
///   deep_model(x_current) = x_current  (ground instantiation axiom)
///
/// This test exercises `verify_function_with_modes` end-to-end to reproduce
/// the gt_or_le failure that unit-level encoder tests cannot catch.
#[test]
#[timeout(30000)]
fn deep_model_gt_or_le_verifies_via_alias_and_ground_axioms() {
    use crate::tests::helpers::{deref, eq, ge, le, method_call, var, view};

    // body: View(Var("x")) >= View(Var("y"))
    // This is what the PartialOrd::ge spec produces after substitution:
    // ensures: result == (self@ >= rhs@) with self=x, rhs=y
    let body = ge(view(var("x")), view(var("y")));

    // ensures: result == (deep_model(*y) <= deep_model(*x))
    let ensures = vec![eq(
        var("result"),
        le(
            method_call(deref(var("y")), "deep_model", vec![]),
            method_call(deref(var("x")), "deep_model", vec![]),
        ),
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "gt_or_le should verify: body (x@ >= y@) with postcondition \
         (deep_model(*y) <= deep_model(*x)) requires view identity + \
         alias constraints + deep_model ground axioms. Got: {result:?}"
    );
}

/// Same as above but includes the `call_0` assumption from PartialOrd::ge spec.
///
/// In the real driver pipeline, `transform_contract` adds
/// `call_0 == (x@ >= y@)` to `effective_requires`. This test checks whether
/// the extra assumption interferes with verification.
#[test]
#[timeout(30000)]
fn deep_model_gt_or_le_with_call_assumption_verifies() {
    use crate::tests::helpers::{deref, eq, ge, le, method_call, var, var_with_sort, view};

    // body: View(Var("x")) >= View(Var("y"))
    let body = ge(view(var("x")), view(var("y")));

    // call_assumption: call_0 == (x@ >= y@)
    let call_0 = var_with_sort("call_0", ExprSort::Bool);
    let call_assumption = eq(call_0, ge(view(var("x")), view(var("y"))));

    // requires: [call_assumption]
    let requires = vec![call_assumption];

    // ensures: result == (deep_model(*y) <= deep_model(*x))
    let ensures = vec![eq(
        var("result"),
        le(
            method_call(deref(var("y")), "deep_model", vec![]),
            method_call(deref(var("x")), "deep_model", vec![]),
        ),
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "gt_or_le with call_0 assumption should still verify. Got: {result:?}"
    );
}

/// Coverage for #2520: contradictory preconditions with a quantified
/// postcondition must return a vacuity Unknown.
///
/// Note: contradictory requires are resolved by the axiom-free probe
/// (Phase 1) in <500ms, so this test exercises the axiom-free path's
/// base-recheck vacuity guard — not the full-axiom label-prefix fix.
/// The full-axiom fix (#2520 Option A) is structural: moving
/// resolve_last_unsat_with_vacuity inside with_negated_goal_label_prefix.
/// Its effect only diverges from the old code when the base re-solve
/// returns Incomplete (rare, requires mixed-sort solver limitations).
#[test]
#[timeout(30000)]
fn contradictory_requires_quantified_ensures_returns_unknown() {
    // requires: [x > 0, x < 0] — contradictory base
    let requires = vec![gt(var("x"), int(0)), lt(var("x"), int(0))];
    // ensures: [forall y. result == y] — quantified postcondition.
    // The axiom-free probe finds UNSAT from contradictory requires alone
    // (before axioms are asserted). The base re-solve then detects vacuity.
    let ensures = vec![forall("y", eq(var("result"), var("y")))];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    match result {
        VerificationResult::Unknown(reason) => assert_eq!(
            reason.as_str(),
            "vacuous proof: base assertions are UNSAT without the negated postcondition",
            "contradictory requires with quantified ensures must return the vacuous-proof Unknown reason"
        ),
        other => panic!(
            "contradictory requires with quantified ensures must return Unknown(vacuous proof), got {other:?}"
        ),
    }
}

#[test]
#[timeout(30000)]
fn proof_assert_ghost_seq_push_back_verify_function_2616() {
    let (requires, ensures, ghost_context) = proof_assert_ghost_seq_state_2616();
    let _proof_assert_guard = crate::ProofAssertModeGuard::enter();

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).ghost_context(Some(&ghost_context)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "proof_assert ghost Seq push_back state should verify once #2616 is fixed: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn proof_assert_ghost_seq_push_back_pre_axiom_base_sat_matrix_2616() {
    // The authoritative #2616 reproducer now lives in the mut-borrow lane.
    // This function-only matrix remains useful as a diagnostic probe. The
    // invariant we need here is that setup, ghost context, and aliases have an
    // independently model-validated SAT base. The broad quantified standard-
    // axiom suite has a separate bounded diagnostic below; it is not a SAT-
    // certification query. The end-to-end test above exercises the production
    // verifier's exact sliced replays.
    // (#2616)
    let (requires, ensures, ghost_context) = proof_assert_ghost_seq_state_2616();
    let setup_result = setup_verification_encoder(&VerificationSetup {
        requires: &requires,
        ensures: &ensures,
        context_exprs: &[],
        result_expr: None,
        ghost_context: Some(&ghost_context),
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        track: TrackLevel::Auto,
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("setup should succeed");
    let mut encoder = setup_result.encoder;

    assert!(
        encoder.batch_base_smt_is_sat(&encoder.solver().to_smtlib2()),
        "proof_assert #2616 function setup should have an independently model-validated SAT base"
    );

    for ghost_expr in &ghost_context {
        let term = encoder
            .encode_pure(ghost_expr)
            .expect("ghost expr should encode");
        encoder.assert_term(term);
    }
    assert!(
        encoder.batch_base_smt_is_sat(&encoder.solver().to_smtlib2()),
        "proof_assert #2616 function ghost context should have an independently model-validated SAT base"
    );

    assert_by_value_alias_constraints(&mut encoder).expect("alias constraints should succeed");
    assert!(
        encoder.batch_base_smt_is_sat(&encoder.solver().to_smtlib2()),
        "proof_assert #2616 function alias constraints should have an independently model-validated SAT base"
    );
}

#[test]
#[timeout(30000)]
fn proof_assert_ghost_seq_push_back_bounded_axiom_consistency_diagnostic_2616() {
    // This is deliberately a diagnostic, not proof authority. The complete
    // standard-axiom stack contains broad quantified Seq rules; AY may
    // conservatively return Unknown when its bounded instantiation budget is
    // exhausted. We only reject an actual UNSAT result, which would expose a
    // contradiction in the axioms. A two-second solver budget (with AY's
    // internal bounded quantifier backstop) keeps this non-gating probe below
    // the enclosing 30-second test deadline. Production verification coverage
    // is provided by `proof_assert_ghost_seq_push_back_verify_function_2616`.
    let (requires, ensures, ghost_context) = proof_assert_ghost_seq_state_2616();
    let setup_result = setup_verification_encoder(&VerificationSetup {
        requires: &requires,
        ensures: &ensures,
        context_exprs: &[],
        result_expr: None,
        ghost_context: Some(&ghost_context),
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        track: TrackLevel::Auto,
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("setup should succeed");
    let mut encoder = setup_result.encoder;

    for ghost_expr in &ghost_context {
        let term = encoder
            .encode_pure(ghost_expr)
            .expect("ghost expr should encode");
        encoder.assert_term(term);
    }
    assert_by_value_alias_constraints(&mut encoder).expect("alias constraints should succeed");

    assert_standard_axioms(&mut encoder, &requires, &[]).expect("axioms should assert");
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
    let axioms_sat = encoder.check_sat();
    assert!(
        !axioms_sat.is_unsat(),
        "proof_assert #2616 function axioms must not be contradictory in the bounded diagnostic, got {axioms_sat:?}"
    );
}
