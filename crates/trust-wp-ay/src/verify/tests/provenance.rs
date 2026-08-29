// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for [`VerificationProvenance`] and [`VerificationOutcome`].
//! Part of #2729: VerificationProvenance in All Verification Results.

use std::{collections::HashMap, sync::Arc, time::Duration};

use ntest::timeout;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use crate::{
    MutBorrowRequest, SolveStatisticsSnapshot, VerificationOutcome, VerificationProvenance,
    VerificationRequest, VerificationResult,
};

#[test]
#[timeout(30000)]
fn test_outcome_without_provenance() {
    let result = VerificationResult::verified();
    let outcome = VerificationOutcome::without_provenance(result);
    assert!(matches!(outcome.result, VerificationResult::Verified(_)));
    assert!(outcome.provenance.is_none());
}

#[test]
#[timeout(30000)]
fn test_outcome_with_provenance() {
    let result = VerificationResult::verified();
    let provenance =
        VerificationProvenance::with_solve_time(Duration::from_millis(42)).with_assertion_count(10);
    let outcome = VerificationOutcome::new(result, Some(provenance));
    assert!(matches!(outcome.result, VerificationResult::Verified(_)));
    let prov = outcome.provenance.expect("should have provenance");
    assert_eq!(prov.solve_time, Duration::from_millis(42));
    assert_eq!(prov.assertion_count, 10);
}

#[test]
#[timeout(30000)]
fn test_outcome_unknown_with_provenance() {
    let result = VerificationResult::unknown(crate::UnknownReason::Timeout);
    let provenance = VerificationProvenance::with_solve_time(Duration::from_mins(1))
        .with_solver_timeout(Some(Duration::from_mins(1)));
    let outcome = VerificationOutcome::new(result, Some(provenance));
    assert!(matches!(
        outcome.result,
        VerificationResult::Unknown(crate::UnknownReason::Timeout)
    ));
    let prov = outcome.provenance.expect("should have provenance");
    assert_eq!(prov.solver_timeout_ms, Some(60_000));
}

#[test]
#[timeout(30000)]
fn test_capture_provenance_from_encoder() {
    use crate::encoder::AYEncoder;

    let encoder = AYEncoder::new();
    let provenance = encoder.capture_provenance(Duration::from_millis(100));
    assert_eq!(provenance.solve_time, Duration::from_millis(100));
    // Fresh encoder has no solve statistics (no check_sat call yet).
    assert!(provenance.solver_statistics.is_none());
    // No timeout set on fresh encoder.
    assert!(provenance.solver_timeout_ms.is_none());
}

#[test]
#[timeout(30000)]
fn test_capture_provenance_after_solve() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    // Run a trivial check_sat to populate solver statistics.
    let _result = encoder.check_sat();
    let provenance = encoder.capture_provenance(Duration::from_millis(5));
    assert_eq!(provenance.solve_time, Duration::from_millis(5));
    // After a solve, statistics should be populated.
    assert!(
        provenance.solver_statistics.is_some(),
        "solver statistics should be populated after check_sat"
    );
    assert!(
        provenance.solve_evidence.is_some(),
        "solve evidence should be populated after check_sat"
    );
    let replay = provenance
        .replay_artifact
        .as_deref()
        .expect("replay artifact should be populated after check_sat");
    assert!(replay.contains("schema=trust-wp-ay-replay-artifact-v1"));
    assert!(replay.contains("check-sat|name=check_sat"));
    assert!(replay.contains("result|status="));
    let native_replay = provenance
        .native_replay_json
        .as_deref()
        .expect("native AY replay JSON should be populated after check_sat");
    assert!(native_replay.contains("\"schema\": \"ay.native-replay.v1\""));
    assert!(native_replay.contains("\"assertions\""));
    assert!(native_replay.contains("\"terms\""));
}

#[test]
#[timeout(30000)]
fn test_capture_provenance_with_timeout_set() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_secs(30)));
    let provenance = encoder.capture_provenance(Duration::from_millis(50));
    assert_eq!(provenance.solver_timeout_ms, Some(30_000));
}

#[test]
#[timeout(30000)]
fn test_provenance_vc_hash_placeholder_is_zero() {
    let provenance = VerificationProvenance::default();
    assert_eq!(
        provenance.vc_hash, [0u8; 32],
        "VC hash should default to zero (placeholder)"
    );
}

#[test]
#[timeout(30000)]
fn test_provenance_with_statistics_roundtrip() {
    let stats = SolveStatisticsSnapshot {
        decisions: 100,
        conflicts: 5,
        propagations: 500,
        theory_conflicts: 2,
        theory_propagations: 10,
        num_vars: 50,
        num_clauses: 200,
        num_assertions: 42,
        ..Default::default()
    };
    let provenance = VerificationProvenance::with_solve_time(Duration::from_secs(1))
        .with_solver_statistics(Some(stats.clone()));
    let recovered_stats = provenance.solver_statistics.expect("should have stats");
    assert_eq!(recovered_stats.decisions, 100);
    assert_eq!(recovered_stats.num_assertions, 42);
    assert_eq!(recovered_stats, stats);
}

#[test]
#[timeout(30000)]
fn test_verify_function_outcome_exposes_pipeline_provenance() {
    let result = PureExpr::Var("result".to_string(), None);
    let x = PureExpr::Var("x".to_string(), None);
    let requires = [PureExpr::BinOp(
        Arc::new(x.clone()),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let return_expr = x;
    let ensures = [PureExpr::BinOp(
        Arc::new(result),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let outcome = crate::verify_function_with_modes_outcome(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should encode");

    assert!(matches!(outcome.result, VerificationResult::Verified(_)));
    let provenance = outcome
        .provenance
        .as_ref()
        .expect("outcome API should expose pipeline provenance");
    assert!(
        provenance.replay_artifact.is_some(),
        "provenance should include replay artifact text"
    );
    assert!(
        provenance.native_replay_json.is_some(),
        "provenance should include native AY replay JSON"
    );
    assert!(
        provenance.solve_evidence.is_some(),
        "provenance should include solve evidence"
    );
    let evidence = provenance
        .solve_evidence
        .as_ref()
        .expect("verified outcome should keep proof solve evidence");
    assert!(
        evidence.result.eq_ignore_ascii_case("unsat") || evidence.result.starts_with("Unsat"),
        "verified provenance should preserve the core UNSAT solve evidence, got {}",
        evidence.result
    );
}

#[test]
#[timeout(30000)]
fn test_empty_function_obligation_exposes_accepted_solver_evidence() {
    let x = PureExpr::Var("x".to_string(), None);
    let requires = [PureExpr::BinOp(
        Arc::new(x),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let outcome =
        crate::verify_function_with_modes_outcome(VerificationRequest::new(&requires, &[]))
            .expect("empty-obligation verification should encode");

    assert!(matches!(outcome.result, VerificationResult::Verified(_)));
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("empty verified obligations should carry solver evidence");
    assert!(
        evidence.accepted_for_consumer,
        "empty-obligation solver evidence should be accepted: {evidence:?}"
    );
    assert!(
        evidence.result.eq_ignore_ascii_case("unsat") || evidence.result.starts_with("Unsat"),
        "empty-obligation evidence should be UNSAT, got {}",
        evidence.result
    );
}

#[test]
#[timeout(30000)]
fn proof_assert_mode_requires_and_retains_exact_strict_slice_certificate() {
    let ensures = [PureExpr::Bool(true)];
    let _proof_assert_guard = crate::ProofAssertModeGuard::enter();
    let outcome =
        crate::verify_function_with_modes_outcome(VerificationRequest::new(&[], &ensures))
            .expect("proof_assert obligation should encode");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "strict proof_assert solve should verify: {:?}",
        outcome.result
    );
    let provenance = outcome
        .provenance
        .expect("strict proof_assert solve should retain provenance");
    assert_eq!(
        provenance.proof_assert_slice_certificates.len(),
        1,
        "one independently solved claim requires one certificate"
    );
    let certificate = &provenance.proof_assert_slice_certificates[0];
    assert_eq!(certificate.ordinal, 0);
    assert_eq!(
        provenance.solve_evidence.as_ref(),
        Some(&certificate.solve_evidence),
        "aggregate evidence must be the final slice"
    );
    assert_eq!(
        provenance.solver_statistics.as_ref(),
        Some(&certificate.solver_statistics),
        "aggregate statistics must be the final slice"
    );
    assert_eq!(
        provenance.native_replay_json.as_deref(),
        Some(certificate.native_problem_json.as_str()),
        "aggregate native replay must be the final slice"
    );
    let artifact =
        ay_dpll::api::NativeReplayArtifact::from_json_str(&certificate.native_problem_json)
            .expect("certificate should carry canonical native replay JSON");
    assert_eq!(artifact.created_unix_ms, 0);
    assert!(artifact.solve.is_none());
    assert!(artifact.checked_replay.is_none());
    assert!(artifact.panic_payload.is_none());
    assert!(artifact.unsupported_atoms.is_empty());
    assert!(artifact.replay_gaps.is_empty());
    let replay = ay_dpll::api::Solver::replay_native_replay_artifact_with_proofs(
        &artifact,
        Duration::from_secs(6),
    )
    .expect("certificate must replay through AY's strict proof checker");
    assert!(replay.result.is_unsat());
    assert!(replay.verification_level.has_proof_checking());
    assert!(replay.verification.unsat_proof_available);
    assert_eq!(replay.verification.unsat_proof_checker_failures, 0);
    assert!(replay.statistics.proof_complete);
    assert_eq!(replay.statistics.get_int("proof_trust"), Some(0));
    assert_eq!(replay.statistics.get_int("proof_checker_failures"), Some(0));
    assert_eq!(
        replay
            .statistics
            .get_int("proof_checker_skipped_hole_steps"),
        Some(0)
    );
}

#[test]
#[timeout(30000)]
fn proof_assert_mode_retains_every_slice_in_source_order() {
    let x = PureExpr::Var("x".to_string(), None);
    let requires = [PureExpr::BinOp(
        Arc::new(x.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    )];
    let ensures = [
        PureExpr::BinOp(Arc::new(x.clone()), BinOp::Gt, Arc::new(PureExpr::Int(0))),
        PureExpr::BinOp(Arc::new(x), BinOp::Lt, Arc::new(PureExpr::Int(2))),
    ];
    let _proof_assert_guard = crate::ProofAssertModeGuard::enter();
    let outcome =
        crate::verify_function_with_modes_outcome(VerificationRequest::new(&requires, &ensures))
            .expect("multi-slice proof_assert obligation should encode");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "each strict slice should verify: {outcome:#?}"
    );
    let certificates = &outcome
        .provenance
        .expect("multi-slice proof_assert should retain provenance")
        .proof_assert_slice_certificates;
    assert_eq!(certificates.len(), 2);
    assert_eq!(certificates[0].ordinal, 0);
    assert_eq!(certificates[1].ordinal, 1);
    assert_ne!(
        certificates[0].prepared_claim_hash,
        certificates[1].prepared_claim_hash
    );
    assert_ne!(certificates[0].problem_hash, certificates[1].problem_hash);
}

/// The proof_assert certificate's `prepared_claim` is the STABLE
/// PreparedAssertion-side claim text: the driver's reporting firewall
/// independently recomputes it from the original `PreparedAssertion` and
/// refuses any certificate whose claim differs ("certificate source claim
/// mismatch").
///
/// The mut-borrow lane normalizes `base.ensures` BEFORE the pipeline —
/// `preserve_temporal_wrappers_for_mut_borrow` erases the non-MutRef `Var`
/// sort annotation under `Deref`/`Final` for every temporal param
/// (`Var("x", Some(Int))` -> `Var("x", None)`) — so computing claims from the
/// normalized form makes every such certificate structurally refusable the
/// moment ay's proof certification completes (closures/07: four proof_assert
/// slices demoted to evidence gaps at ay >= 0.10). Pin that the certificate
/// carries the PreparedAssertion-side text, annotations intact.
#[test]
#[timeout(60000)]
fn mut_borrow_certificate_carries_prepared_assertion_side_claim_text() {
    let annotated_x = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let y = PureExpr::Var("y".to_string(), None);
    // A premise-dependent goal: `^x == 5` holds only via `x_final == y == 5`,
    // so the slice takes the real negated-goal solver path (a structurally
    // true goal would be discharged without the solve evidence a certificate
    // is minted from).
    let requires = [PureExpr::BinOp(
        Arc::new(y.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    )];
    let ensures = [PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(annotated_x))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    )];
    let final_values = HashMap::from([("x".to_string(), y)]);
    let _proof_assert_guard = crate::ProofAssertModeGuard::enter();
    let outcome = crate::verify_mut_borrow_function_with_modes_outcome(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("mut-borrow proof_assert obligation should encode");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "the final-value-grounded goal should verify strictly: {:?}",
        outcome.result
    );
    let certificates = &outcome
        .provenance
        .expect("strict mut-borrow proof_assert solve should retain provenance")
        .proof_assert_slice_certificates;
    assert_eq!(certificates.len(), 1);
    let expected = crate::proof_assert_obligation_slice_claims(&ensures);
    assert_eq!(
        certificates[0].prepared_claim, expected[0],
        "the certificate must carry the PreparedAssertion-side claim text \
         (Var sort annotations intact), not the mut-borrow-normalized form"
    );
    assert!(
        certificates[0].prepared_claim.contains("Int"),
        "the pinned claim text must actually exercise a sort-annotated Var \
         (`Some(Int)`), or this pin is vacuous: {}",
        certificates[0].prepared_claim
    );
}

#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_outcome_exposes_pipeline_provenance() {
    let result = PureExpr::Var("result".to_string(), None);
    let return_expr = PureExpr::Int(1);
    let ensures = [PureExpr::BinOp(
        Arc::new(result),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let final_values = HashMap::new();

    let outcome = crate::verify_mut_borrow_function_with_modes_outcome(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("mut-borrow verification should encode");

    assert!(matches!(outcome.result, VerificationResult::Verified(_)));
    let provenance = outcome
        .provenance
        .as_ref()
        .expect("mut-borrow outcome API should expose pipeline provenance");
    assert!(
        provenance.replay_artifact.is_some(),
        "provenance should include replay artifact text"
    );
    assert!(
        provenance.native_replay_json.is_some(),
        "provenance should include native AY replay JSON"
    );
    assert!(
        provenance.solve_evidence.is_some(),
        "provenance should include solve evidence"
    );
}

/// A verified outcome's provenance must carry the evidence AND the statistics
/// of the SAME solve.
///
/// The empty-obligation lane proves its goal on a fresh proof-enabled solver
/// while the outer encoder never solves at all, so that encoder's
/// `capture_provenance` statistics are a structural placeholder. Installing the
/// retained evidence without its retained statistics produced a pair describing
/// no real solve — accepted UNSAT evidence next to `proof_complete: false` —
/// which the driver's mandatory proof-authority boundary refuses, turning every
/// contractless obligation into an evidence gap. Pin the paired shape field by
/// field so neither another provenance merge nor a solver statistics rename can
/// drop it silently again.
#[test]
#[timeout(60000)]
fn verified_provenance_pairs_evidence_with_its_own_proof_statistics() {
    let outcome = crate::verify_function_with_modes_outcome(VerificationRequest::new(&[], &[]))
        .expect("empty obligation should encode");
    assert!(matches!(
        outcome.result,
        VerificationResult::Verified(Some(_))
    ));
    let provenance = outcome
        .provenance
        .expect("verified outcome carries provenance");
    let evidence = provenance
        .solve_evidence
        .expect("verified outcome carries accepted solve evidence");
    let statistics = provenance
        .solver_statistics
        .expect("verified outcome carries the statistics of that evidence");

    assert!(evidence.accepted_for_consumer);
    assert_eq!(evidence.result, "unsat");
    assert!(evidence.verification.unsat_proof_available);
    assert_eq!(evidence.verification.unsat_proof_checker_failures, 0);
    assert!(
        crate::encoder::ay_api::solve_snapshots_have_complete_unsat_proof(&evidence, &statistics),
        "retained evidence must be paired with the statistics of its own proof"
    );

    let extra = |key: &str| {
        statistics
            .extra_ints
            .iter()
            .find_map(|(candidate, value)| (candidate == key).then_some(*value))
    };
    assert!(
        statistics.proof_complete,
        "statistics must describe the completed proof, not a placeholder"
    );
    assert_eq!(extra("proof_checker_failures"), Some(0));
    assert_eq!(extra("proof_trust"), Some(0));
    assert_eq!(extra("proof_checker_skipped_hole_steps"), Some(0));
    let checked = extra("proof_checker_checked_steps").expect("proof_checker_checked_steps");
    let total = extra("proof_checker_total_steps").expect("proof_checker_total_steps");
    assert!(
        total > 0 && checked == total,
        "every proof step must be checked: {checked}/{total}"
    );
}
