// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── resolve_sat_result_lightweight coverage (#2133) ────────────────

/// UNSAT solver result maps to VerificationResult::Verified(_).
#[test]
#[timeout(30000)]
fn resolve_sat_result_lightweight_unsat_is_verified() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    // Assert false to force UNSAT
    let false_term = encoder
        .encode_pure(&PureExpr::Bool(false))
        .expect("encoding false should succeed");
    encoder.assert_term(false_term);

    let result = resolve_sat_result_lightweight(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "UNSAT should map to Verified, got {result:?}"
    );
}

/// SAT solver result maps to VerificationResult::Failed with empty model.
#[test]
#[timeout(30000)]
fn resolve_sat_result_lightweight_sat_is_failed_empty_model() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    // Assert true — trivially SAT
    let true_term = encoder
        .encode_pure(&PureExpr::Bool(true))
        .expect("encoding true should succeed");
    encoder.assert_term(true_term);

    let result = resolve_sat_result_lightweight(&mut encoder);
    match result {
        VerificationResult::Failed(cex) => {
            assert!(
                cex.values.is_empty(),
                "lightweight resolve should produce empty model, got {} values",
                cex.values.len()
            );
            assert!(
                cex.violated_postcondition.is_none(),
                "lightweight resolve should have no violated postcondition"
            );
        }
        _ => panic!("SAT should map to Failed, got {result:?}"),
    }
}

/// Forced hard timeout on the lightweight loop resolve path returns
/// Abort(Unknown(Timeout)) instead of hanging (#1342).
#[test]
#[timeout(30000)]
fn resolve_sat_result_lightweight_forced_hard_timeout_aborts() {
    use crate::verify::{
        force_hard_timeout_for_test, run_with_hard_timeout, ResolveContinuation, UnknownReason,
    };

    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");
    encoder.set_timeout(Some(std::time::Duration::from_millis(1)));

    let _guard = force_hard_timeout_for_test();
    let result = run_with_hard_timeout(&mut encoder, resolve_sat_result_lightweight);
    assert!(
        matches!(
            result,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
        ),
        "forced hard timeout on lightweight loop path should abort with Unknown(Timeout): {result:?}"
    );
}

// ── resolve_sat_result_lightweight_timed coverage (#2457) ──────────

/// Timed wrapper on UNSAT returns Continue(Verified).
#[test]
#[timeout(30000)]
fn resolve_sat_result_lightweight_timed_unsat_is_continue_verified() {
    use crate::verify::hard_timeout::ResolveContinuation;

    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    // Assert false to force UNSAT
    let false_term = encoder
        .encode_pure(&PureExpr::Bool(false))
        .expect("encoding false should succeed");
    encoder.assert_term(false_term);

    let result = resolve_sat_result_lightweight_timed(&mut encoder);
    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Verified(_))
        ),
        "timed wrapper on UNSAT should return Continue(Verified), got {result:?}"
    );
}

/// Forced hard timeout on timed wrapper returns Abort(Unknown(Timeout)) (#2457).
#[test]
#[timeout(30000)]
fn resolve_sat_result_lightweight_timed_forced_timeout_aborts() {
    use crate::verify::{force_hard_timeout_for_test, hard_timeout::ResolveContinuation};

    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");
    encoder.set_timeout(Some(std::time::Duration::from_millis(1)));

    let _guard = force_hard_timeout_for_test();
    let result = resolve_sat_result_lightweight_timed(&mut encoder);
    assert!(
        matches!(
            result,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
        ),
        "forced hard timeout on timed wrapper should abort: {result:?}"
    );
}

// ── loop-initialization resolver coverage ─────────────────────────

/// Loop-initialization timed resolver disables direct Bool UNSAT shortcuts.
#[test]
#[timeout(30000)]
fn resolve_loop_initialization_timed_direct_bool_conflict_has_accepted_evidence() {
    use crate::verify::hard_timeout::ResolveContinuation;

    let flag = PureExpr::Var("loop_init_direct_conflict_flag".to_string(), None);
    let mut encoder = setup_loop_encoder(
        std::slice::from_ref(&flag),
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let flag_term = encoder
        .encode_pure(&flag)
        .expect("encoding flag should succeed");
    encoder.assert_term(flag_term);
    let not_flag = encoder.solver_mut().not(flag_term);
    encoder.assert_term(not_flag);

    let result =
        crate::verify::loops::encoder_setup::resolve_loop_initialization_sat_result_lightweight_timed(
            &mut encoder,
        );
    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Verified(_))
        ),
        "loop-init direct Bool conflict should verify, got {result:?}"
    );

    let evidence = encoder
        .last_solve_evidence()
        .expect("loop-init solve should cache solver evidence");
    assert!(
        evidence.result.to_ascii_lowercase().contains("unsat"),
        "loop-init direct Bool conflict should produce UNSAT evidence: {evidence:?}"
    );
    assert!(
        evidence.accepted_for_consumer,
        "loop-init direct Bool conflict must use accepted solver evidence: {evidence:?}"
    );
    assert!(
        evidence.consumer_rejection.is_none(),
        "accepted loop-init evidence should not carry a rejection: {evidence:?}"
    );
}

// ── solve_scoped_loop_obligation coverage (#2457) ──────────────────

/// Scoped obligation on UNSAT returns Continue(Verified) and pops scope.
#[test]
#[timeout(30000)]
fn solve_scoped_obligation_unsat_returns_continue_verified() {
    use crate::verify::hard_timeout::ResolveContinuation;

    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let result = solve_scoped_loop_obligation(&mut encoder, |enc| {
        // Assert false inside the scope to force UNSAT
        let false_term = enc.encode_pure(&PureExpr::Bool(false))?;
        enc.assert_term(false_term);
        Ok(())
    })
    .expect("scoped obligation should not hard-error");

    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Verified(_))
        ),
        "scoped obligation on UNSAT should return Continue(Verified), got {result:?}"
    );

    // Encoder should still be usable after pop_scope (scope was cleaned up).
    // Verify by encoding another expression — this would panic if scope state
    // is corrupt.
    let _term = encoder
        .encode_pure(&PureExpr::Bool(true))
        .expect("encoder should be usable after scoped obligation completes");
}

/// Forced hard timeout in scoped obligation returns Abort without panicking
/// on pop_scope (#2457). This is the key safety regression: before the fix,
/// a hung solver would block forever; after the fix, the Abort path skips
/// pop_scope (matching the shared pipeline's behavior).
#[test]
#[timeout(30000)]
fn solve_scoped_obligation_forced_timeout_aborts_without_panic() {
    use crate::verify::{force_hard_timeout_for_test, hard_timeout::ResolveContinuation};

    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");
    encoder.set_timeout(Some(std::time::Duration::from_millis(1)));

    let _guard = force_hard_timeout_for_test();
    let result = solve_scoped_loop_obligation(&mut encoder, |enc| {
        // Assert true — trivially SAT, but forced timeout will fire first
        let true_term = enc.encode_pure(&PureExpr::Bool(true))?;
        enc.assert_term(true_term);
        Ok(())
    })
    .expect("scoped obligation should not hard-error even on timeout");

    assert!(
        matches!(
            result,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
        ),
        "forced timeout in scoped obligation should abort: {result:?}"
    );
}

/// Build error in scoped obligation pops scope and bubbles the error.
#[test]
#[timeout(30000)]
fn solve_scoped_obligation_build_error_pops_scope() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let result = solve_scoped_loop_obligation(&mut encoder, |_enc| {
        Err(crate::error::EncodingError::unsupported("test error"))
    });

    assert!(result.is_err(), "build error should bubble as Err");

    // Encoder should still be usable after error path cleans up scope.
    let _term = encoder
        .encode_pure(&PureExpr::Bool(true))
        .expect("encoder should be usable after scoped obligation error");
}

/// Scoped obligation wrapper must demote vacuous `Verified` results after the
/// negated-goal scope is popped and the live base is re-solved. (#2622)
#[test]
#[timeout(30000)]
fn solve_scoped_obligation_with_base_recheck_demotes_vacuous_verified() {
    use crate::verify::hard_timeout::ResolveContinuation;

    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let false_term = encoder
        .encode_pure(&PureExpr::Bool(false))
        .expect("encoding false should succeed");
    encoder.assert_term(false_term);

    let result = solve_scoped_loop_obligation_with_base_recheck(&mut encoder, |enc| {
        let scoped_false = enc.encode_pure(&PureExpr::Bool(false))?;
        enc.assert_term(scoped_false);
        Ok(())
    })
    .expect("scoped obligation with base recheck should not hard-error");

    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Unknown(
                UnknownReason::SolverMessage(ref msg)
            )) if msg.contains(crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE)
        ),
        "contradictory live base should demote scoped Verified to Unknown(vacuous), got {result:?}"
    );

    let _term = encoder
        .encode_pure(&PureExpr::Bool(true))
        .expect("encoder should remain usable after base recheck");
}

/// Loop-initialization scoped helper preserves accepted UNSAT evidence for a
/// direct Bool conflict instead of returning shortcut provenance.
#[test]
#[timeout(30000)]
fn solve_scoped_loop_initialization_direct_bool_conflict_has_accepted_provenance() {
    let flag = PureExpr::Var("scoped_loop_init_direct_conflict_flag".to_string(), None);
    let mut encoder = setup_loop_encoder(
        std::slice::from_ref(&flag),
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let flag_term = encoder
        .encode_pure(&flag)
        .expect("encoding flag should succeed");
    encoder.assert_term(flag_term);

    let result =
        crate::verify::loops::encoder_setup::solve_scoped_loop_initialization_obligation_outcome(
            &mut encoder,
            |enc| {
                let scoped_flag = enc.encode_pure(&flag)?;
                let not_flag = enc.solver_mut().not(scoped_flag);
                enc.assert_term(not_flag);
                Ok(())
            },
        )
        .expect("loop-init scoped obligation should not hard-error");

    let outcome = match result {
        crate::verify::loops::encoder_setup::OutcomeContinuation::Continue(outcome) => outcome,
        crate::verify::loops::encoder_setup::OutcomeContinuation::Abort(outcome) => {
            panic!("loop-init direct Bool conflict should not abort: {outcome:?}")
        }
    };
    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "loop-init direct Bool conflict should verify, got {outcome:?}"
    );

    let provenance = outcome
        .provenance
        .as_ref()
        .expect("verified loop-init outcome should carry provenance");
    let evidence = provenance
        .solve_evidence
        .as_ref()
        .expect("verified loop-init outcome should carry solve evidence");
    assert!(
        evidence.result.to_ascii_lowercase().contains("unsat"),
        "loop-init scoped helper should produce UNSAT evidence: {evidence:?}"
    );
    assert!(
        evidence.accepted_for_consumer,
        "loop-init scoped helper must force accepted solver evidence: {evidence:?}"
    );
    assert!(
        evidence.consumer_rejection.is_none(),
        "accepted loop-init scoped evidence should not carry a rejection: {evidence:?}"
    );

    let _term = encoder
        .encode_pure(&PureExpr::Bool(true))
        .expect("encoder should be usable after loop-init scoped obligation completes");
}
