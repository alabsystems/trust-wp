// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for cached solve diagnostics extracted from `solver.rs` (#1988).

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::super::AYEncoder;
use crate::shared_types::UnknownReason;

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
