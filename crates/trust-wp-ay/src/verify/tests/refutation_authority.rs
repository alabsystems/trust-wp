// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The refutation-authority gate: no FAILED without a validated model.
//!
//! Every test here must fail if the rule is reverted. The pair that matters is
//! [`validated_sat_refutation_survives_the_gate`] (the honest path is pinned —
//! a real counterexample must still be published) and the rest (an unattempted
//! or uncertified obligation must never be published as a refutation).

use std::time::Duration;

use crate::{
    refutation_evidence_gap_reason,
    shared_types::{
        SolveEvidenceSnapshot, SolveVerificationLevelSnapshot, SolveVerificationSnapshot,
    },
    Counterexample, UnknownReason, VerificationOutcome, VerificationProvenance, VerificationResult,
    INJECTED_FAIL_CLOSED_GOAL_REASON, OPAQUE_TYPE_PARAM_INVARIANT_GOAL_REASON,
    REFUTATION_AUTHORITY_MESSAGE,
};

/// A SAT snapshot ay validated and accepted: the shape of an honest refutation.
fn validated_sat_evidence() -> SolveEvidenceSnapshot {
    SolveEvidenceSnapshot {
        result: "sat".to_string(),
        model_validated: true,
        accepted_for_consumer: true,
        consumer_rejection: None,
        verification: SolveVerificationSnapshot {
            sat_model_validated: true,
            ..SolveVerificationSnapshot::default()
        },
        verification_level: SolveVerificationLevelSnapshot::FullyVerified,
        resource_usage: crate::shared_types::SolveResourceSnapshot::default(),
    }
}

fn outcome_with_evidence(
    result: VerificationResult,
    evidence: Option<SolveEvidenceSnapshot>,
) -> VerificationOutcome {
    VerificationOutcome::new(
        result,
        Some(
            VerificationProvenance::with_solve_time(Duration::from_millis(9))
                .with_assertion_count(3)
                .with_solve_evidence(evidence),
        ),
    )
}

fn withheld_reason(outcome: &VerificationOutcome) -> String {
    match &outcome.result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(message)) => message.clone(),
        other => panic!("expected a withheld refutation, got {other:?}"),
    }
}

/// Helpers for the injected-goal gate (D-27), which ATTRIBUTES the refutation
/// to a goal and asks whether the program text, not just a model, refuted it.
fn user_goal() -> trust_wp_core::formula::PureExpr {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )
}

fn injected_marker_goal() -> trust_wp_core::formula::PureExpr {
    trust_wp_core::formula::PureExpr::Bool(false)
}

/// A `Failed` that names `clause_idx`, with `shape` recorded when the program
/// text also refuted it.
fn refutation_of_clause(clause_idx: usize, shape: Option<&str>) -> VerificationOutcome {
    let mut counterexample = Counterexample::empty();
    counterexample.set_violated_postcondition(crate::PostconditionInfo {
        clause_idx,
        contract_text: "clause".to_string(),
        span: None,
    });
    let mut provenance = VerificationProvenance::with_solve_time(Duration::from_millis(9))
        .with_assertion_count(3)
        .with_solve_evidence(Some(validated_sat_evidence()));
    provenance.refutation_structural_shape = shape.map(str::to_string);
    VerificationOutcome::new(VerificationResult::Failed(counterexample), Some(provenance))
}

#[test]
fn validated_sat_refutation_survives_the_gate() {
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(validated_sat_evidence()),
    );

    assert_eq!(refutation_evidence_gap_reason(&outcome), None);
    assert!(matches!(
        outcome.apply_mandatory_refutation_authority().result,
        VerificationResult::Failed(_)
    ));
}

#[test]
fn failed_without_provenance_is_withheld() {
    let outcome = VerificationOutcome::without_provenance(VerificationResult::Failed(
        Counterexample::empty(),
    ));

    assert_eq!(
        refutation_evidence_gap_reason(&outcome).as_deref(),
        Some("missing solver provenance")
    );
    let gated = outcome.apply_mandatory_refutation_authority();
    assert_eq!(
        withheld_reason(&gated),
        format!("{REFUTATION_AUTHORITY_MESSAGE}: missing solver provenance")
    );
}

#[test]
fn failed_without_solve_evidence_is_withheld() {
    let outcome = outcome_with_evidence(VerificationResult::Failed(Counterexample::empty()), None);

    assert_eq!(
        refutation_evidence_gap_reason(&outcome).as_deref(),
        Some("missing solver evidence")
    );
}

/// The corpus's largest dishonest class: `ay_result=trust-wp-structural-provenance`.
#[test]
fn failed_on_structural_provenance_is_withheld() {
    let mut evidence = validated_sat_evidence();
    evidence.result = "trust-wp-structural-provenance".to_string();
    evidence.model_validated = false;
    evidence.accepted_for_consumer = false;
    evidence.consumer_rejection =
        Some("structural provenance does not include verified solver evidence".to_string());
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(evidence),
    );

    assert_eq!(
        refutation_evidence_gap_reason(&outcome).as_deref(),
        Some(
            "solver evidence was trust-wp-structural-provenance, \
             not a satisfying counterexample model"
        )
    );
    assert!(matches!(
        outcome.apply_mandatory_refutation_authority().result,
        VerificationResult::Unknown(_)
    ));
}

/// A shortcut SAT that never ran model validation is not a counterexample.
#[test]
fn failed_on_unvalidated_sat_is_withheld() {
    let mut evidence = validated_sat_evidence();
    evidence.model_validated = false;
    evidence.verification.sat_model_validated = false;
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(evidence),
    );

    assert_eq!(
        refutation_evidence_gap_reason(&outcome).as_deref(),
        Some("solver model was never validated")
    );
}

/// A validated model ay's own consumer gate rejected is not usable either.
#[test]
fn failed_on_consumer_rejected_sat_is_withheld() {
    let mut evidence = validated_sat_evidence();
    evidence.accepted_for_consumer = false;
    evidence.consumer_rejection = Some("soundness gate caught an invalid model".to_string());
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(evidence),
    );

    assert_eq!(
        refutation_evidence_gap_reason(&outcome).as_deref(),
        Some("soundness gate caught an invalid model")
    );
}

/// An UNSAT snapshot under a `Failed` verdict is the sharpest contradiction of
/// all: the solve reported the obligation's negation unsatisfiable.
#[test]
fn failed_on_unsat_evidence_is_withheld() {
    let mut evidence = validated_sat_evidence();
    evidence.result = "unsat".to_string();
    evidence.model_validated = false;
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(evidence),
    );

    assert_eq!(
        refutation_evidence_gap_reason(&outcome).as_deref(),
        Some("solver evidence was unsat, not a satisfying counterexample model")
    );
}

#[test]
fn the_gate_judges_refutations_only() {
    for result in [
        VerificationResult::Verified(None),
        VerificationResult::Unknown(UnknownReason::Timeout),
        VerificationResult::Assumed("opaque call".to_string()),
    ] {
        let outcome = VerificationOutcome::without_provenance(result.clone());
        assert_eq!(
            refutation_evidence_gap_reason(&outcome),
            None,
            "{result:?} is not a refutation and must not be touched"
        );
    }
}

#[test]
fn the_gate_is_idempotent() {
    let once = VerificationOutcome::without_provenance(VerificationResult::Failed(
        Counterexample::empty(),
    ))
    .apply_mandatory_refutation_authority();
    let twice = once.clone().apply_mandatory_refutation_authority();

    assert_eq!(withheld_reason(&once), withheld_reason(&twice));
}

/// The public boundary must run BOTH gates, not just the proof-side one.
#[test]
fn the_public_boundary_applies_the_refutation_gate() {
    let gated = VerificationOutcome::without_provenance(VerificationResult::Failed(
        Counterexample::empty(),
    ))
    .apply_mandatory_proof_authority();

    assert!(
        withheld_reason(&gated).starts_with(REFUTATION_AUTHORITY_MESSAGE),
        "apply_mandatory_proof_authority must also withhold unvalidated refutations"
    );
}

// ---------------------------------------------------------------------------
// D-27, the second half of the rule: a refutation over a goal trust-wp
// MANUFACTURED.
//
// The evidence gate above asks "did a solver really find a model?". These ask
// the other half of the same question: "was the clause that model violates one
// SOMEBODY WROTE?". A driver-injected fail-closed `false` is not — and it is
// refutable in every model, so without this gate an unmodelled construct is
// published as `FAILED ✗ (counterexample)` with a perfectly validated model
// behind it.
// ---------------------------------------------------------------------------

/// `g ==> false`, the spelling a branch arm's marker reaches the goal set in.
fn guarded(
    guard: trust_wp_core::formula::PureExpr,
    goal: trust_wp_core::formula::PureExpr,
) -> trust_wp_core::formula::PureExpr {
    use std::sync::Arc;
    trust_wp_core::formula::PureExpr::BinOp(
        Arc::new(guard),
        trust_wp_core::formula::BinOp::Implies,
        Arc::new(goal),
    )
}

fn arm_guard() -> trust_wp_core::formula::PureExpr {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("d".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    )
}

#[test]
fn a_fail_closed_marker_is_the_false_bare_or_behind_path_guards() {
    use trust_wp_core::formula::PureExpr;

    assert!(crate::is_fail_closed_marker(&PureExpr::Bool(false)));
    assert!(crate::is_fail_closed_marker(&guarded(
        arm_guard(),
        PureExpr::Bool(false)
    )));
    assert!(crate::is_fail_closed_marker(&guarded(
        arm_guard(),
        guarded(arm_guard(), PureExpr::Bool(false))
    )));
    // A guard FALSE is not a marker: `false ==> g` is a tautology.
    assert!(!crate::is_fail_closed_marker(&guarded(
        PureExpr::Bool(false),
        user_goal()
    )));
    // A guarded clause somebody wrote is not one either.
    assert!(!crate::is_fail_closed_marker(&guarded(
        arm_guard(),
        user_goal()
    )));
    assert!(crate::goals_carry_fail_closed_marker(&[guarded(
        arm_guard(),
        PureExpr::Bool(false)
    )]));
    assert!(!crate::goals_carry_fail_closed_marker(&[guarded(
        arm_guard(),
        user_goal()
    )]));

    assert!(crate::goals_carry_fail_closed_marker(&[PureExpr::Bool(
        false
    )]));
    assert!(crate::goals_carry_fail_closed_marker(&[
        PureExpr::Bool(true),
        PureExpr::Bool(false),
    ]));
    assert!(!crate::goals_carry_fail_closed_marker(&[]));
    assert!(!crate::goals_carry_fail_closed_marker(&[PureExpr::Bool(
        true
    )]));
    assert!(!crate::goals_carry_fail_closed_marker(&[PureExpr::Var(
        "x".to_string(),
        None
    )]));
}

/// The COUNT, not just the predicate: one `false` in a goal set can be the
/// panic-unreachability goal for a body that can never return, which trust-wp
/// really can refute. The driver subtracts those before asking the question,
/// so the count has to be exact.
#[test]
fn the_fail_closed_marker_count_is_exact() {
    use trust_wp_core::formula::PureExpr;

    assert_eq!(crate::fail_closed_marker_count(&[]), 0);
    assert_eq!(crate::fail_closed_marker_count(&[PureExpr::Bool(true)]), 0);
    assert_eq!(crate::fail_closed_marker_count(&[PureExpr::Bool(false)]), 1);
    assert_eq!(
        crate::fail_closed_marker_count(&[
            PureExpr::Bool(false),
            PureExpr::Bool(true),
            PureExpr::Bool(false),
        ]),
        2
    );
    // A marker behind an arm's guard still counts: the driver subtracts the
    // callee `#[requires(false)]` it counted before any guard wrapped it, so
    // leaving the guarded one out would under-count the injected ones.
    assert_eq!(
        crate::fail_closed_marker_count(&[
            PureExpr::Bool(false),
            guarded(arm_guard(), PureExpr::Bool(false)),
            guarded(arm_guard(), user_goal()),
        ]),
        2
    );
    // The predicate is the count, so the two can never disagree.
    for goals in [
        vec![],
        vec![PureExpr::Bool(true)],
        vec![PureExpr::Bool(false)],
        vec![PureExpr::Bool(false), PureExpr::Bool(false)],
    ] {
        assert_eq!(
            crate::goals_carry_fail_closed_marker(&goals),
            crate::fail_closed_marker_count(&goals) > 0
        );
    }
}

/// A guarded marker beside its arm's own unreachability goal restates that
/// goal (`g ==> false` is `!g`), so it is not counted: the prologue marker of
/// `panic!("msg")` in a reachable arm must not withhold the arm's refutation.
/// A marker without that exact partner is counted as before.
#[test]
fn a_marker_restating_its_arms_unreachability_goal_is_not_counted() {
    use std::sync::Arc;

    use trust_wp_core::formula::{PureExpr, UnOp};
    let not = |expr: PureExpr| PureExpr::UnOp(UnOp::Not, Arc::new(expr));
    let flag = PureExpr::Var("flag".to_string(), None);
    let marker = guarded(arm_guard(), PureExpr::Bool(false));

    let paired = [marker.clone(), not(arm_guard())];
    assert_eq!(crate::unpaired_fail_closed_marker_count(&paired), 0);
    assert!(!crate::goals_carry_fail_closed_marker(&paired));
    assert_eq!(
        crate::fail_closed_marker_count(&paired),
        1,
        "the total is unchanged"
    );
    // The else arm of `if flag`: its guard is `!flag`, its goal `flag`.
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[
            guarded(not(flag.clone()), PureExpr::Bool(false)),
            flag.clone(),
        ]),
        0
    );
    // Nested arms pair under the same outer guard.
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[
            guarded(flag.clone(), marker.clone()),
            guarded(flag.clone(), not(arm_guard())),
        ]),
        0
    );

    // No partner, a partner for another guard, or one under another outer
    // guard: the marker's arm goes on, and it is counted.
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[marker.clone()]),
        1
    );
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[marker.clone(), not(flag.clone())]),
        1
    );
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[
            guarded(flag.clone(), marker.clone()),
            not(arm_guard()),
        ]),
        1
    );
    assert!(crate::goals_carry_fail_closed_marker(&[
        marker.clone(),
        user_goal()
    ]));
    // A bare `false` has no guard to negate: never paired.
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[PureExpr::Bool(false), PureExpr::Bool(true)]),
        1
    );
    // Two markers under one guard both restate its goal.
    assert_eq!(
        crate::unpaired_fail_closed_marker_count(&[
            marker.clone(),
            marker.clone(),
            not(arm_guard()),
        ]),
        0
    );
}

#[test]
fn a_validated_refutation_over_an_injected_false_is_withheld() {
    // The exact shape `non_atomic_invariant_cellinv` produced: ay really did
    // find and validate a model, and the gate above therefore passes it. The
    // clause it violates is the `false` `handle_opaque_call` injected.
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(validated_sat_evidence()),
    );
    assert_eq!(
        refutation_evidence_gap_reason(&outcome),
        None,
        "the evidence gate cannot catch this one — the model IS validated"
    );

    let gated = outcome.apply_injected_goal_refutation_authority(true, &[injected_marker_goal()]);
    assert_eq!(
        withheld_reason(&gated),
        format!("{REFUTATION_AUTHORITY_MESSAGE}: {INJECTED_FAIL_CLOSED_GOAL_REASON}")
    );
    assert!(
        crate::is_withheld_refutation(&gated.result),
        "one spelling only: the #3771 policy and the counters key on this"
    );
}

#[test]
fn a_refutation_over_written_clauses_survives_the_injected_goal_gate() {
    let outcome = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(validated_sat_evidence()),
    );

    assert!(
        matches!(
            outcome
                .apply_injected_goal_refutation_authority(false, &[user_goal()])
                .result,
            VerificationResult::Failed(_)
        ),
        "no injected marker in the goals: the refutation is about the program"
    );
}

#[test]
fn the_injected_goal_gate_touches_no_other_verdict() {
    for result in [
        VerificationResult::Verified(None),
        VerificationResult::Unknown(UnknownReason::Timeout),
        VerificationResult::Assumed("because".to_string()),
    ] {
        let gated = VerificationOutcome::without_provenance(result.clone())
            .apply_injected_goal_refutation_authority(true, &[user_goal()]);
        assert_eq!(
            std::mem::discriminant(&gated.result),
            std::mem::discriminant(&result),
            "{result:?} is not a refutation and must not be touched"
        );
    }
}

#[test]
fn the_injected_goal_gate_is_idempotent() {
    let once = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(validated_sat_evidence()),
    )
    .apply_injected_goal_refutation_authority(true, &[injected_marker_goal()]);
    let twice = once
        .clone()
        .apply_injected_goal_refutation_authority(true, &[injected_marker_goal()]);

    assert_eq!(withheld_reason(&once), withheld_reason(&twice));
}

/// The withheld verdict must be an `Unknown`, never anything a downstream
/// counter could read as a pass. This is the mirror-image guard for D-27:
/// the gate moves verdicts OUT of `failed`, and none of them may land in
/// `verified`.
#[test]
fn a_withheld_injected_goal_refutation_is_never_verified() {
    let gated = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(validated_sat_evidence()),
    )
    .apply_injected_goal_refutation_authority(true, &[injected_marker_goal()]);

    assert!(
        !matches!(gated.result, VerificationResult::Verified(_)),
        "a withheld refutation must never become a proof"
    );
    assert!(matches!(gated.result, VerificationResult::Unknown(_)));
}

// ---------------------------------------------------------------------------
// The marker suppresses the refutation it MANUFACTURED, not every refutation
// in a function that happens to carry one.
// ---------------------------------------------------------------------------

/// An unmodelled call beside a clause the program's own text violates.
/// The user's clause still refutes.
#[test]
fn a_marker_does_not_swallow_a_refutation_the_program_text_forces() {
    let goals = [user_goal(), injected_marker_goal()];
    let gated = refutation_of_clause(0, Some("result-contradicts-return-expr"))
        .apply_injected_goal_refutation_authority(true, &goals);

    assert!(
        matches!(gated.result, VerificationResult::Failed(_)),
        "the violation is read off the return expression, not off a value \
         trust-wp manufactured: it must keep its FAILED"
    );
}

/// The SAME program shape with the unmodelled call's result RETURNED. The
/// user's clause is refuted only by a model that picks a value for something
/// trust-wp could not model. Withheld — this is the case the gate exists for.
#[test]
fn a_refutation_only_a_model_supports_is_still_withheld() {
    let goals = [user_goal(), injected_marker_goal()];
    let gated =
        refutation_of_clause(0, None).apply_injected_goal_refutation_authority(true, &goals);

    assert_eq!(
        withheld_reason(&gated),
        format!("{REFUTATION_AUTHORITY_MESSAGE}: {INJECTED_FAIL_CLOSED_GOAL_REASON}")
    );
}

/// A structural shape over a literal `false` goal licenses nothing: `false` is
/// refutable in every model, so a SAT answer over it is not evidence about the
/// program whatever else fired.
#[test]
fn a_shape_over_a_literal_false_goal_licenses_nothing() {
    let goals = [user_goal(), injected_marker_goal()];
    let gated = refutation_of_clause(1, Some("result-contradicts-return-expr"))
        .apply_injected_goal_refutation_authority(true, &goals);

    assert!(crate::is_withheld_refutation(&gated.result));
}

/// A marker behind the guard of the branch arm it was injected in is refuted
/// by every model that reaches the arm: that shows the unmodelled construct
/// is reachable, not that the program is wrong. The shape of a refutation
/// that fired on the arm's other goals does not license it (D-141: a refused
/// invariant grant inside a `match` arm printed FAILED on a TRUE impl).
#[test]
fn a_shape_over_a_guarded_marker_licenses_nothing() {
    let goals = [user_goal(), guarded(arm_guard(), injected_marker_goal())];
    let gated = refutation_of_clause(1, Some("result-contradicts-return-expr"))
        .apply_injected_goal_refutation_authority(true, &goals);

    assert_eq!(
        withheld_reason(&gated),
        format!("{REFUTATION_AUTHORITY_MESSAGE}: {INJECTED_FAIL_CLOSED_GOAL_REASON}")
    );
}

/// The user's own guarded clause, beside a guarded marker, keeps the shape's
/// license: the predicate reads the conclusion, not the guard.
#[test]
fn a_guarded_written_clause_keeps_its_refutation_beside_a_guarded_marker() {
    let goals = [
        guarded(arm_guard(), user_goal()),
        guarded(arm_guard(), injected_marker_goal()),
    ];
    let gated = refutation_of_clause(0, Some("result-contradicts-return-expr"))
        .apply_injected_goal_refutation_authority(true, &goals);

    assert!(matches!(gated.result, VerificationResult::Failed(_)));
}

/// An UNATTRIBUTED refutation is unattributable: fail closed.
#[test]
fn an_unattributed_refutation_is_withheld() {
    let goals = [user_goal(), injected_marker_goal()];
    let mut provenance = VerificationProvenance::with_solve_time(Duration::from_millis(9))
        .with_solve_evidence(Some(validated_sat_evidence()));
    provenance.refutation_structural_shape = Some("result-contradicts-return-expr".to_string());
    let gated = VerificationOutcome::new(
        VerificationResult::Failed(Counterexample::empty()),
        Some(provenance),
    )
    .apply_injected_goal_refutation_authority(true, &goals);

    assert!(
        crate::is_withheld_refutation(&gated.result),
        "no violated-clause tag means the gate cannot say WHICH goal the model \
         violated; the shape alone may not stand in for that"
    );
}

/// A clause index past the end of the goal set is not attribution either.
#[test]
fn a_refutation_naming_a_goal_that_is_not_there_is_withheld() {
    let goals = [user_goal()];
    let gated = refutation_of_clause(7, Some("result-contradicts-return-expr"))
        .apply_injected_goal_refutation_authority(true, &goals);

    assert!(crate::is_withheld_refutation(&gated.result));
}

// ---------------------------------------------------------------------------
// A type parameter's invariant is opaque: a model that falsifies it refutes the
// missing fact, not the program (D-141).
// ---------------------------------------------------------------------------

fn type_param_invariant_of(receiver: &str) -> trust_wp_core::formula::PureExpr {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(receiver.to_string(), None)),
        method: trust_wp_core::logic::type_param_invariant_method_name(0, "T"),
        args: vec![],
    }
}

#[test]
fn a_refutation_of_a_type_parameter_invariant_is_withheld() {
    let goals = [user_goal(), type_param_invariant_of("t")];
    let gated =
        refutation_of_clause(1, None).apply_opaque_type_param_goal_refutation_authority(&goals);

    assert_eq!(
        withheld_reason(&gated),
        format!("{REFUTATION_AUTHORITY_MESSAGE}: {OPAQUE_TYPE_PARAM_INVARIANT_GOAL_REASON}")
    );
    assert!(
        crate::is_withheld_refutation(&gated.result),
        "one spelling of a withheld refutation for the counters and the wire line"
    );
}

#[test]
fn a_type_parameter_invariant_inside_a_goal_is_seen() {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};
    // A guarded obligation, as a call inside a branch or a loop states it.
    let guarded = PureExpr::BinOp(
        Arc::new(PureExpr::Var("c".to_string(), None)),
        BinOp::Implies,
        Arc::new(type_param_invariant_of("t")),
    );
    let gated =
        refutation_of_clause(0, None).apply_opaque_type_param_goal_refutation_authority(&[guarded]);

    assert!(crate::is_withheld_refutation(&gated.result));
}

#[test]
fn a_refutation_of_a_goal_stating_no_type_parameter_invariant_is_published() {
    // The premise `inv_T(t)` is true in every model, so its interpretation cannot
    // be what falsified a clause that does not mention it.
    let goals = [user_goal(), type_param_invariant_of("t")];
    let gated =
        refutation_of_clause(0, None).apply_opaque_type_param_goal_refutation_authority(&goals);

    assert!(matches!(gated.result, VerificationResult::Failed(_)));
}

#[test]
fn a_refutation_of_a_concrete_type_invariant_is_published() {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;
    // A type's invariant has a body the solver reads; only a type PARAMETER's is opaque.
    let concrete = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
        method: trust_wp_core::logic::type_invariant_method_name("Sum10"),
        args: vec![],
    };
    let gated = refutation_of_clause(0, None)
        .apply_opaque_type_param_goal_refutation_authority(&[concrete]);

    assert!(matches!(gated.result, VerificationResult::Failed(_)));
}

#[test]
fn an_unattributed_refutation_beside_a_type_parameter_invariant_is_withheld() {
    let goals = [user_goal(), type_param_invariant_of("t")];
    let gated = outcome_with_evidence(
        VerificationResult::Failed(Counterexample::empty()),
        Some(validated_sat_evidence()),
    )
    .apply_opaque_type_param_goal_refutation_authority(&goals);

    assert!(
        crate::is_withheld_refutation(&gated.result),
        "unattributed: the model may have broken the opaque goal"
    );
}

#[test]
fn the_opaque_goal_gate_touches_no_other_verdict_and_never_makes_a_proof() {
    let goals = [type_param_invariant_of("t")];
    for result in [
        VerificationResult::Verified(None),
        VerificationResult::Unknown(UnknownReason::Timeout),
        VerificationResult::Assumed("because".to_string()),
    ] {
        let gated = VerificationOutcome::without_provenance(result.clone())
            .apply_opaque_type_param_goal_refutation_authority(&goals);
        assert_eq!(
            std::mem::discriminant(&gated.result),
            std::mem::discriminant(&result),
            "{result:?} is not a refutation and must not be touched"
        );
    }
    let once =
        refutation_of_clause(0, None).apply_opaque_type_param_goal_refutation_authority(&goals);
    let twice = once
        .clone()
        .apply_opaque_type_param_goal_refutation_authority(&goals);
    assert_eq!(withheld_reason(&once), withheld_reason(&twice));
    assert!(!matches!(once.result, VerificationResult::Verified(_)));
}
