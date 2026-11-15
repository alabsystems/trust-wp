// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for cached solve diagnostics extracted from `solver.rs` (#1988).

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::super::AYEncoder;
use crate::shared_types::{SolveVerificationLevelSnapshot, UnknownReason};

/// After a check_sat call, last_solve_statistics must be populated. (#2639)
#[test]
#[timeout(30000)]
fn test_statistics_populated_after_check_sat() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let y = encoder.solver_mut().declare_const("y", Sort::Int);
    let x_gt_y = encoder.solver_mut().gt(x, y);
    encoder.assert_term(x_gt_y);
    let y_gt_x = encoder.solver_mut().gt(y, x);
    encoder.assert_term(y_gt_x);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::unsat());

    let stats = encoder.last_solve_statistics();
    assert!(
        stats.is_some(),
        "last_solve_statistics should be populated after check_sat"
    );
    let stats = stats.unwrap();
    // At minimum, the solver should have processed some assertions
    assert!(
        stats.num_assertions > 0 || stats.num_vars > 0 || stats.decisions > 0,
        "statistics should show solver activity: {stats:?}"
    );
}

/// Cached diagnostics are cleared before each new check_sat call. (#2639)
#[test]
#[timeout(30000)]
fn test_cached_diagnostics_cleared_before_fresh_solve() {
    let mut encoder = AYEncoder::new_pure();

    // First solve: force Unknown via zero timeout
    let warmup_x = encoder.solver_mut().declare_const("warmup_x", Sort::Int);
    let warmup_zero = encoder.solver_mut().int_const(0);
    let warmup_pos = encoder.solver_mut().gt(warmup_x, warmup_zero);
    encoder.assert_term(warmup_pos);
    encoder.set_timeout(Some(std::time::Duration::ZERO));
    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    // Cached reason should be populated
    assert!(
        encoder.last_unknown_reason().is_some(),
        "should have cached unknown reason after Unknown result"
    );

    // Second solve: no timeout, trivially UNSAT
    encoder.set_timeout(None);
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::unsat());
    // Previous unknown reason should be cleared
    assert!(
        encoder.last_unknown_reason().is_none(),
        "cached unknown reason should be cleared after a new UNSAT solve"
    );
}

/// A definitive no-proof retry must not leave the proof-trusted Unknown
/// diagnostics from the failed proof-producing attempt attached to provenance.
#[test]
#[timeout(30000)]
fn test_proof_retry_success_clears_stale_unknown_diagnostics() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    encoder
        .encoding_cache
        .set_solve_unknown_reason(UnknownReason::ProofTrusted);
    encoder.encoding_cache.set_solve_executor_error(
        "proof checker rejected UNSAT proof before no-proof retry".to_string(),
    );

    let result = encoder.retry_check_sat_without_proofs();
    assert_eq!(result, Some(SolveResult::unsat()));
    assert!(
        encoder.last_unknown_reason().is_none(),
        "successful retry must clear stale unknown_reason"
    );
    assert!(
        encoder.last_executor_error().is_none(),
        "successful retry must clear stale executor_error"
    );

    let provenance = encoder.capture_provenance(std::time::Duration::ZERO);
    let evidence = provenance
        .solve_evidence
        .as_ref()
        .expect("retry solve evidence should be retained");
    assert_eq!(evidence.result, "unsat");
    assert!(provenance.unknown_reason.is_none());
    assert!(provenance.executor_error.is_none());
    assert!(
        provenance.replay_artifact.as_deref().is_some_and(
            |artifact| artifact.contains("retrying_without_proofs_after_proof_related_result")
        ),
        "replay provenance should make the no-proof retry explicit"
    );
}

/// Provenance must report what the STRICT replay MEASURED, not the incremental
/// encoder's proof-production CONFIGURATION.
///
/// Regression pin for a reporting defect that produced three wrong censuses.
/// The long-lived incremental encoder is built with `set_produce_proofs(false)`
/// and never calls `set_verification_level`, so `verification_level = Trusted`
/// and `unsat_proof_available = false` are constants it reports for EVERY query
/// — a genuine `Unsat` looks exactly like a refusal. Reading them as a
/// measurement counted the encoder's configuration and concluded that
/// obligations "have no proof object" when complete derivations existed.
///
/// The strict replay runs with proofs ON. Its observation is now retained
/// whether or not it clears the authority bar, so the two are distinguishable.
#[test]
#[timeout(60000)]
fn test_strict_replay_observation_is_retained_independently_of_authority() {
    let mut encoder = AYEncoder::new_pure();

    // x > 0 AND x < 0 — UNSAT, and small enough to replay strictly.
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    assert_eq!(encoder.check_sat(), SolveResult::unsat());

    let before = encoder.capture_provenance(std::time::Duration::ZERO);
    let incremental = before
        .solve_evidence
        .as_ref()
        .expect("the incremental solve should leave evidence");
    assert_eq!(incremental.result, "unsat");
    // The constants. This is a genuine UNSAT reporting as if nothing was proved:
    // the level carries no proof checking and no artifact is offered, because
    // proofs were never requested — not because ay failed to build one.
    assert!(
        !matches!(
            incremental.verification_level,
            SolveVerificationLevelSnapshot::ProofChecked
                | SolveVerificationLevelSnapshot::FullyVerified
        ),
        "incremental encoder reports its configured level, not a measurement; got {:?}",
        incremental.verification_level
    );
    assert!(
        !incremental.verification.unsat_proof_available,
        "proofs were never requested on this encoder, so this is always false"
    );
    assert!(
        before.strict_proof_replay.is_none(),
        "absence must mean 'no strict replay ran', never a fabricated negative"
    );

    // Ask for the stronger evidence.
    let summary = encoder.authorize_current_stack_unsat_with_strict_proof();

    let after = encoder.capture_provenance(std::time::Duration::ZERO);
    let observation = after.strict_proof_replay.as_ref().expect(
        "a strict replay ran, so provenance must retain what it measured — \
         whether or not it cleared the authority bar",
    );
    assert_eq!(observation.evidence.result, "unsat");
    assert!(
        matches!(
            observation.evidence.verification_level,
            SolveVerificationLevelSnapshot::ProofChecked
                | SolveVerificationLevelSnapshot::FullyVerified
        ),
        "the replay solves with proof checking on, so its level must differ from \
         the incremental encoder's constant `Trusted`; got {:?}",
        observation.evidence.verification_level
    );
    assert!(
        observation.evidence.verification.unsat_proof_available,
        "the replay requested proofs, so this reports a real derivation"
    );
    assert_eq!(
        observation.authority_accepted,
        summary.is_some(),
        "the observation must record the authority decision it was taken across"
    );

    // The instrument must not disturb the pair the authority boundary judges.
    let authoritative = after
        .solve_evidence
        .as_ref()
        .expect("solve evidence must still be present");
    if summary.is_none() {
        assert_eq!(
            authoritative, incremental,
            "a DECLINED replay must leave solve_evidence exactly as it found it"
        );
    }
}

/// A strict replay is reported ONLY under the obligation slice that produced it.
///
/// Regression pin for the sixth instrument defect in this area, and the one that
/// manufactured a phantom class. Letting the observation survive ordinary solve
/// diagnostics (so a certification-blocked obligation stops reporting a false
/// `strict_replay=none`) also let it survive its own slice. A multi-`ensures`
/// function solves several unrelated queries against one encoder, so whichever
/// slice recorded last was reported on the batch's line: `vector/09_capacity`
/// printed its `forall` slice's accepted 20-step certificate on a
/// `proof-trusted` verdict produced by the OTHER slice, whose own replays ay
/// refused at `trust=1 hole=0 total=17`. Corpus-wide that was 19 obligations
/// advertising a certificate they did not own.
///
/// Two prior fixes managed the observation's LIFETIME and neither closed this.
/// The binding below is an IDENTITY check, so a sibling's measurement is
/// recognised as a sibling's regardless of when it was written or which of the
/// six `capture_provenance` call sites is reading.
#[test]
#[timeout(60000)]
fn test_strict_replay_observation_is_bound_to_the_slice_that_produced_it() {
    let mut encoder = AYEncoder::new_pure();
    encoder.begin_strict_replay_obligation();
    encoder.begin_strict_replay_obligation_slice();

    // x > 0 AND x < 0 — UNSAT, and small enough to replay strictly.
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    assert_eq!(encoder.check_sat(), SolveResult::unsat());
    encoder.authorize_current_stack_unsat_with_strict_proof();

    // Same slice: this capture IS the one the replay measured.
    let own = encoder.capture_provenance(std::time::Duration::ZERO);
    assert!(
        own.strict_proof_replay.is_some(),
        "an observation must still reach the obligation that produced it — \
         binding is not a licence to report nothing"
    );
    assert_eq!(
        own.strict_proof_replay_unbound, 0,
        "nothing was refused, so the counter must say so"
    );

    // Re-record, then move to the next slice of the same batch. The measurement
    // is now a sibling's: a different query, on the same encoder.
    encoder.authorize_current_stack_unsat_with_strict_proof();
    encoder.begin_strict_replay_obligation_slice();

    let sibling = encoder.capture_provenance(std::time::Duration::ZERO);
    assert!(
        sibling.strict_proof_replay.is_none(),
        "a sibling slice's certificate must report as ABSENT, never as this \
         obligation's — that substitution is the whole defect"
    );
    assert_eq!(
        sibling.strict_proof_replay_unbound, 1,
        "absence caused by a refusal must be distinguishable from 'no replay ran'"
    );

    // The refusal consumes the observation, so it cannot be claimed later either.
    let after = encoder.capture_provenance(std::time::Duration::ZERO);
    assert!(after.strict_proof_replay.is_none());
}

/// Why the multi-slice aggregate reports `strict_replay=none`, and why
/// attributing it to the deciding slice does NOT change that.
///
/// 760fac2 flagged a follow-up: report the aggregate under the slice that
/// decided its verdict, which "needs the deciding slice index out of
/// `aggregate_slice_results`". That index is available and the deciding slice is
/// well-defined for `Failed`/`Unknown`/`Assumed` (each returns one slice's
/// payload verbatim). Threading it out and harvesting each slice's observation
/// at its own boundary was built and measured, and it recovered NOTHING. This
/// test is why, and it is the cheap reproduction of that result.
///
/// [`StrictReplayScope`](crate::encoder::state::encoding_cache::StrictReplayScope)
/// binds on (obligation, slice, SOLVE). One further `check_sat` on the SAME
/// slice — precisely what the base/vacuity recheck performs after a goal is
/// proved — already unbinds the observation. So a slice's own measurement is
/// gone before the slice ends: there is nothing at the slice boundary left for
/// an aggregate to attribute, however correctly the deciding slice is named.
///
/// Measured on the corpus at this revision, with the harvest in place:
/// `vector/09_capacity::change_capacity` and `closures/13_ref_box::test7` each
/// reported TWO refusals (`strict_replay_unbound=2`, one per slice) and both
/// still printed `strict_replay=none`; lane-wide `strict_replay=present` did not
/// move. The blocker is the `solve` component, not slice attribution, and
/// relaxing it would be a scope loosening — the regression 760fac2 exists to
/// prevent — rather than an attribution fix.
#[test]
#[timeout(60000)]
fn test_a_later_solve_on_the_same_slice_already_unbinds_the_observation() {
    let mut encoder = AYEncoder::new_pure();
    encoder.begin_strict_replay_obligation();
    encoder.begin_strict_replay_obligation_slice();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    assert_eq!(encoder.check_sat(), SolveResult::unsat());
    encoder.authorize_current_stack_unsat_with_strict_proof();

    // One more solve on the SAME slice. No obligation or slice boundary is
    // crossed — only the `solve` counter moves.
    let _ = encoder.check_sat();

    let after = encoder.capture_provenance(std::time::Duration::ZERO);
    assert!(
        after.strict_proof_replay.is_none(),
        "the observation is already unbound by a later solve WITHIN its own \
         slice, which is why per-slice harvesting recovers nothing"
    );
    assert_eq!(
        after.strict_proof_replay_unbound, 1,
        "and the refusal is tallied — this is the `strict_replay_unbound=N` a \
         census sees on the certification-blocked lane"
    );
}

/// check_sat on a satisfiable problem populates statistics. (#2639)
#[test]
#[timeout(30000)]
fn test_statistics_populated_after_sat() {
    let mut encoder = AYEncoder::new();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let stats = encoder.last_solve_statistics();
    assert!(
        stats.is_some(),
        "last_solve_statistics should be populated after SAT result"
    );
    assert!(
        encoder.last_solve_evidence().is_some(),
        "last_solve_evidence should be populated after SAT result"
    );
}

/// check_sat caches the richer ay SolveDetails envelope, including consumer
/// acceptance and resource evidence. (#2639)
#[test]
#[timeout(30000)]
fn test_solve_evidence_populated_after_check_sat() {
    let mut encoder = AYEncoder::new_pure();
    encoder.solver_mut().set_produce_proofs(true);

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::unsat());

    let evidence = encoder
        .last_solve_evidence()
        .expect("solve evidence should be cached");
    assert_eq!(evidence.result, "unsat");
    if evidence.accepted_for_consumer {
        assert!(
            evidence.consumer_rejection.is_none(),
            "accepted evidence should not carry a consumer rejection"
        );
    } else {
        assert!(
            evidence.consumer_rejection.is_some(),
            "rejected evidence should carry a consumer rejection"
        );
    }
}

#[test]
#[timeout(30000)]
fn shortcut_unsat_evidence_is_rejected_for_consumer() {
    let mut encoder = AYEncoder::new_pure();

    let b = encoder.solver_mut().declare_const("b", Sort::Bool);
    encoder.assert_term(b);
    let not_b = encoder.solver_mut().not(b);
    encoder.assert_term(not_b);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::unsat());

    let evidence = encoder
        .last_solve_evidence()
        .expect("shortcut solve evidence should be cached");
    assert_eq!(evidence.result, "unsat");
    assert!(
        !evidence.accepted_for_consumer,
        "shortcut UNSAT evidence must not be accepted without ay proof details"
    );
    assert!(
        evidence
            .consumer_rejection
            .as_deref()
            .is_some_and(|reason| reason.contains("shortcut UNSAT result")
                && reason.contains("proof validation")),
        "shortcut UNSAT evidence should explain the missing proof validation: {evidence:?}"
    );
}

#[test]
#[timeout(30000)]
fn real_solver_unsat_evidence_remains_accepted_for_consumer() {
    let mut encoder = AYEncoder::new_pure();
    encoder.solver_mut().set_produce_proofs(true);

    let x = encoder
        .solver_mut()
        .declare_const("real_unsat_x", Sort::Int);
    let y = encoder
        .solver_mut()
        .declare_const("real_unsat_y", Sort::Int);
    let x_gt_y = encoder.solver_mut().gt(x, y);
    encoder.assert_term(x_gt_y);
    let y_gt_x = encoder.solver_mut().gt(y, x);
    encoder.assert_term(y_gt_x);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::unsat());

    let evidence = encoder
        .last_solve_evidence()
        .expect("solver solve evidence should be cached");
    assert_eq!(evidence.result, "unsat");
    assert!(
        evidence.accepted_for_consumer,
        "real proof-producing UNSAT evidence should remain accepted: {evidence:?}"
    );
    assert!(
        evidence.consumer_rejection.is_none(),
        "accepted solver evidence should not carry a rejection: {evidence:?}"
    );
}

/// Build the trivial UNSAT stack `x > 0 AND x < 0` on a fresh pure encoder.
///
/// Small enough that the strict proof-producing replay certifies it outright,
/// which makes it usable as BOTH the accepted control and — once its remaining
/// budget is squeezed to nothing — the withheld case.
fn unsat_stack_encoder() -> AYEncoder {
    let mut encoder = AYEncoder::new_pure();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let positive = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(positive);
    let negative = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(negative);
    assert_eq!(encoder.check_sat(), SolveResult::unsat());
    encoder
}

/// A WITHHELD strict replay must carry the reason ay recorded for withholding.
///
/// # The defect this pins
///
/// `install_strict_unsat_authority` read `details.verification.unsat_proof_decline`
/// and dropped `details.unknown_reason` / `unknown_diagnostic` on the floor. That
/// left every withheld replay reporting `strict_replay_proof_decline=none` and
/// nothing else, which was read — twice — as "ay refused to certify and recorded
/// NO reason". It never did that. `unsat_proof_decline` carries ay's
/// `ProofDeclineMechanism`, whose mechanisms are reachable only through a parsed
/// SMT-LIB surface AST that the native-API path never builds, so it is
/// structurally `None` here and says nothing at all. The reason ay actually
/// recorded was sitting on the SAME envelope in a different field.
///
/// The squeeze below is not a contrivance for its own sake: it is the cheapest
/// way to make ay withhold a verdict it would otherwise certify, so the test
/// exercises the real population path rather than a hand-built struct.
#[test]
#[timeout(60000)]
fn test_withheld_strict_replay_carries_the_reason_ay_recorded() {
    let mut encoder = unsat_stack_encoder();

    // Leave the fresh strict solve no budget, so ay withholds a verdict it can
    // otherwise certify in microseconds.
    encoder
        .solver_mut()
        .set_timeout(Some(std::time::Duration::from_nanos(1)));

    let summary = encoder.authorize_current_stack_unsat_with_strict_proof();
    assert!(
        summary.is_none(),
        "a replay that never reached a verdict must not yield proof authority"
    );

    let provenance = encoder.capture_provenance(std::time::Duration::ZERO);
    let observation = provenance
        .strict_proof_replay
        .as_ref()
        .expect("a strict replay ran, so its measurement must be retained");

    assert_eq!(observation.evidence.result, "unknown");
    assert!(!observation.authority_accepted);

    // The point of the fix.
    assert_eq!(
        observation.unknown_reason.as_deref(),
        Some("timeout"),
        "ay recorded a reason for withholding; the observation must carry it \
         rather than force a downstream census to infer one"
    );
    assert!(
        observation
            .unknown_detail
            .as_deref()
            .is_some_and(|detail| !detail.is_empty()),
        "the instance-specific detail must survive too; got {:?}",
        observation.unknown_detail
    );

    // The field that was previously mistaken for this one. Its `None` is
    // structural, not a measurement, and must not be read as "nothing declined".
    assert!(
        observation.unsat_proof_decline.is_none(),
        "native-API solves cannot populate the parsed-source decline vocabulary"
    );
}

/// The reason fields are DIAGNOSTICS. They must not widen what earns authority.
///
/// # What a future widening would look like
///
/// The codes carried by `unknown_reason` name real certification refusals
/// (`self_check_rejected`, `proof_trusted`) — verdicts ay COMPUTED and a
/// soundness gate then took away. That makes them a standing temptation to treat
/// as "close enough to proved". They are the opposite: each one is a verdict ay
/// refused to stand behind.
///
/// This pins both directions of the boundary, so a change that starts accepting
/// on a recorded reason, or on the step counters alone, fails here:
///
/// * a withheld replay yields no authority and leaves `solve_evidence` untouched,
///   however informative its reason;
/// * `authority_accepted` still implies a real UNSAT with `proof_complete`.
///
/// That second conjunct is not redundant. `proof_complete` is INDEPENDENT of the
/// checked/total step counters — a replay can report `checked == total > 0` with
/// zero holes and `proof_complete == false` — and a census that dropped it
/// counted quantifier incompleteness, where no verdict was ever reached, as
/// certification refusal, where one was reached and withheld.
#[test]
#[timeout(60000)]
fn test_recorded_reason_cannot_widen_proof_authority() {
    // Withheld: informative reason, and still no authority.
    let mut squeezed = unsat_stack_encoder();
    let before = squeezed.capture_provenance(std::time::Duration::ZERO);
    let incremental = before
        .solve_evidence
        .as_ref()
        .expect("the incremental solve leaves evidence")
        .clone();

    squeezed
        .solver_mut()
        .set_timeout(Some(std::time::Duration::from_nanos(1)));
    let declined = squeezed.authorize_current_stack_unsat_with_strict_proof();
    let after = squeezed.capture_provenance(std::time::Duration::ZERO);
    let withheld = after
        .strict_proof_replay
        .as_ref()
        .expect("the withheld replay is still observed");

    assert!(
        withheld.unknown_reason.is_some(),
        "precondition: a reason was recorded"
    );
    assert!(
        declined.is_none() && !withheld.authority_accepted,
        "a recorded reason must never become a route to authority"
    );
    assert_eq!(
        after.solve_evidence.as_ref(),
        Some(&incremental),
        "a declined replay must leave the pair the authority boundary judges \
         exactly as it found it"
    );

    // Accepted: authority implies a genuine UNSAT with a COMPLETE proof, and
    // carries no withholding reason.
    let mut certified = unsat_stack_encoder();
    let accepted = certified.authorize_current_stack_unsat_with_strict_proof();
    let provenance = certified.capture_provenance(std::time::Duration::ZERO);
    let observation = provenance
        .strict_proof_replay
        .as_ref()
        .expect("the certified replay is observed too");

    assert_eq!(observation.authority_accepted, accepted.is_some());
    if observation.authority_accepted {
        assert_eq!(
            observation.evidence.result, "unsat",
            "authority may only ever rest on an UNSAT"
        );
        assert!(
            observation.statistics.proof_complete,
            "authority requires proof_complete, which the step counters do not imply"
        );
        assert!(
            observation.unknown_reason.is_none(),
            "nothing was withheld, so there is no reason to record; got {:?}",
            observation.unknown_reason
        );
    }
}
