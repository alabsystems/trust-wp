// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared post-negation verification tail and generic solver helpers.
//!
//! Both `verify_single_obligation_slice` (function) and
//! `verify_mut_borrow_single_obligation_slice` (mut-borrow) share the same
//! seven-step sequence after the postcondition has been negated. This module
//! centralizes that sequence so changes to the tail are made once. (#1576)
//!
//! Also owns the generic solve helpers (`assert_standard_axioms`,
//! `resolve_sat_result`, `retry_check_sat_on_timeout`, etc.). Root-module
//! re-exports in `verify/mod.rs` preserve the `crate::verify::*` import
//! paths. (#1576)
//!
//! Split into submodules (#1988):
//! - `solve_helpers`: Generic solve helpers, axiom-free probes, retry logic,
//!   and result resolution functions.

mod solve_helpers;
#[cfg(test)]
mod tests;

// Re-export solve helpers at original visibility levels.
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    panic::AssertUnwindSafe,
    sync::Arc,
};

use ay_dpll::api::Term;
// Internal imports from solve_helpers (not re-exported).
use sha2::{Digest, Sha256};
#[cfg(test)]
pub(crate) use solve_helpers::check_sat_with_retry;
#[cfg(test)]
pub(in crate::verify) use solve_helpers::resolve_base_sat_result;
#[cfg(test)]
pub(super) use solve_helpers::resolve_sat_result;
#[cfg(test)]
pub(crate) use solve_helpers::retry_check_sat_on_timeout;
#[cfg(test)]
pub(super) use solve_helpers::retry_disabled;
pub(crate) use solve_helpers::unknown_result_from_encoder;
use solve_helpers::{
    accepted_unsat_proof_authority, axiom_free_solve_with_sat_extended, base_recheck_long_budget,
    prefer_non_vacuous_core_on_fresh_base_recheck, run_base_recheck_preserving_encoder,
    BaseRecheckEncoderDisposition,
};
pub(super) use solve_helpers::{
    assert_standard_axioms, collect_body_let_assume_assumptions, resolve_last_unsat_with_vacuity,
    resolve_sat_result_without_vacuity, try_axiom_free_solve,
};
pub(in crate::verify) use solve_helpers::{
    axiom_free_solve_with_sat, base_recheck_long_budget_timeout,
    fresh_base_recheck_is_solver_limited, prefer_non_vacuous_core_on_incomplete_base,
    resolve_base_sat_result_with_tight_timeout, resolve_base_sat_result_with_witness,
    run_base_recheck_with_tight_timeout, tiered_check_sat, AxiomFreeOutcome,
};
use tracing::debug;
use trust_wp_core::{
    formula::{BinOp, PureExpr, PureExprDepthLimitedTraversalExt as _, UnOp},
    logic::TypeInvariantDef,
};

use super::{
    assert_eager_negated_existential_instantiations, extract_proof_summary,
    hard_timeout::{run_with_hard_timeout, ResolveContinuation},
    Counterexample, UnknownReason, VerificationResult,
};
use crate::{
    encoder::{unsoundness, AYEncoder, AssertionPhase, MAX_ENCODING_DEPTH},
    error::EncodingError,
    shared_types::{SolveEvidenceSnapshot, SolveStatisticsSnapshot},
};

/// Demotion for a proof whose base is UNSAT once the encoder's axiom scope is
/// KEPT (the ordinary base recheck pops it). Deliberately a distinct message:
/// the fresh base rescue matches `VACUOUS_PROOF_MESSAGE` and rebuilds WITHOUT
/// the axioms, which is exactly the blind spot this demotion closes.
pub(crate) const VACUOUS_WITH_ENCODER_AXIOMS_MESSAGE: &str =
    "vacuous proof: base assertions together with the encoder axiom scope are UNSAT without \
     the negated postcondition (encoder axioms inconsistent with the base)";
/// Wall-clock cap for the axiom-preserving base refutation replay.
const AXIOM_BASE_REFUTATION_TIMEOUT_CAP: std::time::Duration = std::time::Duration::from_secs(2);
pub(crate) const VACUOUS_PROOF_MESSAGE: &str =
    "vacuous proof: base assertions are UNSAT without the negated postcondition";
/// Marker for a base recheck that was SKIPPED because the base solve is
/// pathological (a detached fresh re-solve of the identical base hard-timed
/// out, so the classic in-worker recheck would very likely churn past its
/// envelope and permanently cost the live encoder). This demotion is
/// rescue-eligible: the #2414 fresh base recheck may still produce a positive
/// SAT witness on its own encoder.
pub(crate) const BASE_RECHECK_PATHOLOGY_MESSAGE: &str =
    "base recheck skipped: pathological base solve hard-timed out; \
     fresh base recheck witness required";
const MUT_BORROW_FINAL_DISEQUALITY_MAX_CASES: usize = 128;
const MUT_BORROW_FINAL_DISEQUALITY_MAX_CASE_PAIRS: usize = 16_384;

thread_local! {
    static PREFERRED_VERIFIED_SOLVE_EVIDENCE: RefCell<Option<PreferredVerifiedSolveDiagnostics>> =
        const { RefCell::new(None) };
    /// True while a proof_assert obligation is being verified (#transpose).
    /// The obligation-level batch precheck is suppressed in this mode because a
    /// precheck `Verified(None)` does not carry the strict solver evidence that
    /// proof_assert reporting requires (it would be flagged as an evidence gap).
    static IN_PROOF_ASSERT_MODE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static ACTIVE_PROOF_ASSERT_SLICE_IDENTITY:
        std::cell::Cell<Option<ProofAssertSliceIdentity>> =
        const { std::cell::Cell::new(None) };
    /// Generation of the obligation slice currently being solved, stamped onto
    /// every write of `PREFERRED_VERIFIED_SOLVE_EVIDENCE`. Diagnostics-only.
    static PREFERRED_EVIDENCE_SLICE_GENERATION: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
    /// The structural refutation shape that fired for the obligation slice the
    /// caller has just finished, when that slice returned a `Failed`.
    ///
    /// A shape (`result-contradicts-return-expr`,
    /// `postcondition-contradicts-requirements`, ...) is a determination made
    /// from the PROGRAM TEXT: it reads the clause, the return expression and
    /// the preconditions and finds them contradictory. It therefore does not
    /// depend on any value trust-wp manufactured to stand in for a construct it
    /// could not model, which is what makes it the one signal that can license
    /// a refutation inside a function whose goal set carries a fail-closed
    /// marker (D-27). The shape separates an unmodelled call beside a clause
    /// the text itself violates (the clause keeps its FAILED) from the same
    /// program returning that call's result (no shape fires; withheld).
    static LAST_SLICE_REFUTATION_SHAPE: std::cell::Cell<Option<&'static str>> =
        const { std::cell::Cell::new(None) };
}

/// Forget any shape published by an earlier slice. Called by the pipeline
/// before each slice so a stale value can never be read as this slice's.
pub(crate) fn clear_last_slice_refutation_shape() {
    LAST_SLICE_REFUTATION_SHAPE.with(|cell| cell.set(None));
}

/// Publish the structural refutation shape that refuted the slice just
/// decided. `None` clears.
pub(crate) fn publish_last_slice_refutation_shape(shape: Option<&'static str>) {
    LAST_SLICE_REFUTATION_SHAPE.with(|cell| cell.set(shape));
}

/// The structural refutation shape published by the slice just decided.
pub(crate) fn last_slice_refutation_shape() -> Option<&'static str> {
    LAST_SLICE_REFUTATION_SHAPE.with(std::cell::Cell::get)
}

/// Open a new obligation slice for the preferred-evidence slot, so a later
/// reader can tell this slice's retained evidence from an earlier sibling's.
pub(super) fn begin_preferred_evidence_slice() {
    PREFERRED_EVIDENCE_SLICE_GENERATION.with(|generation| {
        generation.set(generation.get().wrapping_add(1));
    });
}

pub(super) fn current_preferred_evidence_slice_generation() -> u64 {
    PREFERRED_EVIDENCE_SLICE_GENERATION.with(std::cell::Cell::get)
}

/// Clone the retained verified-solve diagnostics ONLY if they were written
/// during the current slice. For reporting an uncertified slice by its own
/// solve; never consulted by any acceptance path.
pub(super) fn clone_preferred_verified_solve_diagnostics_for_current_slice(
) -> Option<PreferredVerifiedSolveDiagnostics> {
    let generation = current_preferred_evidence_slice_generation();
    clone_preferred_verified_solve_diagnostics()
        .filter(|diagnostics| diagnostics.slice_generation == generation)
}

/// Exact source/normalized identity of the proof-assert slice currently being
/// solved. It is copied into native replay metadata before strict replay.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ProofAssertSliceIdentity {
    pub(crate) ordinal: u64,
    pub(crate) prepared_claim_hash: [u8; 32],
    pub(crate) normalized_claim_hash: [u8; 32],
}

impl ProofAssertSliceIdentity {
    #[must_use]
    pub(crate) const fn new(
        ordinal: u64,
        prepared_claim_hash: [u8; 32],
        normalized_claim_hash: [u8; 32],
    ) -> Self {
        Self {
            ordinal,
            prepared_claim_hash,
            normalized_claim_hash,
        }
    }
}

#[derive(Clone)]
pub(super) struct PreferredVerifiedSolveDiagnostics {
    pub(super) evidence: SolveEvidenceSnapshot,
    pub(super) statistics: Option<SolveStatisticsSnapshot>,
    pub(super) claim_identity: Option<ProofAssertSliceIdentity>,
    pub(super) problem_hash: Option<[u8; 32]>,
    pub(super) native_problem_json: Option<String>,
    /// [`current_preferred_evidence_slice_generation`] at write time.
    pub(super) slice_generation: u64,
}

/// Is the current thread verifying a proof_assert obligation? (#transpose)
pub(crate) fn in_proof_assert_mode() -> bool {
    IN_PROOF_ASSERT_MODE.with(std::cell::Cell::get)
}

pub(crate) fn active_proof_assert_slice_identity() -> Option<ProofAssertSliceIdentity> {
    ACTIVE_PROOF_ASSERT_SLICE_IDENTITY.with(std::cell::Cell::get)
}

pub(super) struct ProofAssertSliceClaimGuard {
    previous: Option<ProofAssertSliceIdentity>,
}

impl ProofAssertSliceClaimGuard {
    #[must_use]
    pub(super) fn enter(identity: ProofAssertSliceIdentity) -> Self {
        let previous =
            ACTIVE_PROOF_ASSERT_SLICE_IDENTITY.with(|active| active.replace(Some(identity)));
        Self { previous }
    }
}

impl Drop for ProofAssertSliceClaimGuard {
    fn drop(&mut self) {
        ACTIVE_PROOF_ASSERT_SLICE_IDENTITY.with(|active| active.set(self.previous));
    }
}

/// RAII guard that marks the current thread as verifying a proof_assert
/// obligation for its lifetime, restoring the previous flag on drop. The driver
/// wraps its proof_assert verification calls in this so the obligation-level
/// batch precheck stays off that path. (#transpose)
pub struct ProofAssertModeGuard {
    previous: bool,
}

impl ProofAssertModeGuard {
    #[must_use]
    pub fn enter() -> Self {
        let previous = IN_PROOF_ASSERT_MODE.with(|flag| flag.replace(true));
        Self { previous }
    }
}

impl Drop for ProofAssertModeGuard {
    fn drop(&mut self) {
        IN_PROOF_ASSERT_MODE.with(|flag| flag.set(self.previous));
    }
}

/// A VALIDATED counterexample for a refutation that some lane decided off the
/// live encoder's own last solve: the literal-`false` base witness (a fresh
/// AxiomLight encoder), the isolated QF_BV lane, or any solve whose SAT model
/// ay validated. Mirror of [`PreferredVerifiedSolveDiagnostics`] in the
/// refuting direction.
///
/// The pair `evidence` + `statistics` is read from ONE solve at ONE instant, so
/// the driver's refutation-authority boundary judges the envelope that actually
/// produced the model. `evidence` is guaranteed `sat`, `model_validated` and
/// `accepted_for_consumer` at construction; nothing weaker is ever stored.
#[derive(Clone)]
pub(crate) struct RefutationWitness {
    pub(crate) counterexample: Counterexample,
    pub(crate) evidence: SolveEvidenceSnapshot,
    pub(crate) statistics: Option<SolveStatisticsSnapshot>,
    pub(crate) native_replay_json: Option<String>,
}

thread_local! {
    static PREFERRED_REFUTATION_WITNESS: RefCell<Option<RefutationWitness>> =
        const { RefCell::new(None) };
}

/// Evidence that clears the mandatory refutation-authority bar on its own.
pub(crate) fn evidence_is_validated_sat(evidence: &SolveEvidenceSnapshot) -> bool {
    evidence.accepted_for_consumer
        && evidence.model_validated
        && crate::verify::types::solve_evidence_result_is_sat(&evidence.result)
}

pub(crate) fn clear_refutation_witness() {
    PREFERRED_REFUTATION_WITNESS.with(|slot| {
        *slot.borrow_mut() = None;
    });
}

pub(crate) fn replace_refutation_witness(witness: Option<RefutationWitness>) {
    PREFERRED_REFUTATION_WITNESS.with(|slot| {
        *slot.borrow_mut() = witness;
    });
}

/// Clone the recorded witness without consuming it (the pipeline's installer
/// takes it at the `Failed` it backs).
pub(crate) fn clone_refutation_witness() -> Option<RefutationWitness> {
    PREFERRED_REFUTATION_WITNESS.with(|slot| slot.borrow().clone())
}

/// Take the witness recorded since the last [`clear_refutation_witness`].
/// Callers take it in the SAME code region that produced the `Failed` it
/// backs, so a stale witness can never be paired with a later verdict.
pub(crate) fn take_refutation_witness() -> Option<RefutationWitness> {
    PREFERRED_REFUTATION_WITNESS.with(|slot| slot.borrow_mut().take())
}

/// Record the live encoder's last solve as a refutation witness, if and only
/// if ay reported a VALIDATED, consumer-accepted SAT. Returns the model's
/// counterexample so the caller can publish it as the `Failed` payload.
/// Anything weaker records nothing and returns `None` (fail closed: the
/// caller's `Failed` then reaches the authority boundary unbacked and is
/// withheld exactly as before).
pub(in crate::verify) fn record_refutation_witness_from_encoder(
    encoder: &mut AYEncoder,
) -> Option<Counterexample> {
    let evidence = encoder
        .last_solve_evidence()
        .cloned()
        .filter(evidence_is_validated_sat)?;
    let model = encoder.get_model();
    let counterexample = Counterexample::from_encoder_model(encoder, model);
    let statistics = encoder.last_solve_statistics().cloned();
    encoder.refresh_native_replay_json();
    let native_replay_json = encoder.native_replay_json().map(str::to_owned);
    crate::verify::authority_trace(|| {
        format!(
            "refutation witness recorded from encoder: values={} statistics={}",
            counterexample.values.len(),
            statistics.is_some()
        )
    });
    PREFERRED_REFUTATION_WITNESS.with(|slot| {
        *slot.borrow_mut() = Some(RefutationWitness {
            counterexample: counterexample.clone(),
            evidence,
            statistics,
            native_replay_json,
        });
    });
    Some(counterexample)
}

/// Record a refutation witness from an ISOLATED solver lane (native QF_BV)
/// whose query is exact but never runs on the function encoder. Same bar as
/// [`record_refutation_witness_from_encoder`]: validated, accepted SAT only.
pub(in crate::verify) fn record_isolated_refutation_witness(
    details: &ay_dpll::api::SolveDetails,
    model: Option<ay_dpll::api::Model>,
    native_replay_json: Option<String>,
) -> Option<Counterexample> {
    let evidence = SolveEvidenceSnapshot::from_solve_details(details);
    if !evidence_is_validated_sat(&evidence) {
        crate::verify::authority_trace(|| {
            format!(
                "isolated refutation witness refused: result={} validated={} accepted={}",
                evidence.result, evidence.model_validated, evidence.accepted_for_consumer
            )
        });
        return None;
    }
    let counterexample = Counterexample::from_model(model);
    let statistics = SolveStatisticsSnapshot::from(&details.statistics);
    PREFERRED_REFUTATION_WITNESS.with(|slot| {
        *slot.borrow_mut() = Some(RefutationWitness {
            counterexample: counterexample.clone(),
            evidence,
            statistics: Some(statistics),
            native_replay_json,
        });
    });
    Some(counterexample)
}

pub(super) fn clear_preferred_verified_solve_evidence() {
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| {
        *slot.borrow_mut() = None;
    });
}

pub(super) fn take_preferred_verified_solve_evidence() -> Option<SolveEvidenceSnapshot> {
    take_preferred_verified_solve_diagnostics().map(|diagnostics| diagnostics.evidence)
}

pub(super) fn take_preferred_verified_solve_diagnostics(
) -> Option<PreferredVerifiedSolveDiagnostics> {
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| slot.borrow_mut().take())
}

pub(super) fn clone_preferred_verified_solve_diagnostics(
) -> Option<PreferredVerifiedSolveDiagnostics> {
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| slot.borrow().clone())
}

pub(super) fn replace_preferred_verified_solve_diagnostics(
    diagnostics: Option<PreferredVerifiedSolveDiagnostics>,
) {
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| {
        *slot.borrow_mut() = diagnostics;
    });
}

pub(super) fn take_preferred_verified_solve_evidence_for_encoder(
    encoder: &AYEncoder,
) -> Option<SolveEvidenceSnapshot> {
    if encoder.has_structural_ground_consequences() {
        clear_preferred_verified_solve_evidence();
        return None;
    }
    take_preferred_verified_solve_evidence()
}

/// Take the retained verified-solve diagnostics as ONE matched envelope.
///
/// The evidence snapshot and the statistics snapshot inside
/// [`PreferredVerifiedSolveDiagnostics`] are read from the same encoder at the
/// same instant in [`record_preferred_verified_solve_evidence`], i.e. they
/// describe the same `check_sat` envelope. Callers that install provenance MUST
/// take them together: the mandatory proof-authority boundary in the driver
/// judges the PAIR (`solve_evidence` + `solver_statistics`), so splitting them
/// and re-pairing the evidence with some other solve's statistics describes a
/// solve that never happened — in the refusing direction when the other
/// statistics are a structural placeholder, and in the accepting direction if
/// they ever came from an unrelated proved query.
pub(super) fn take_preferred_verified_solve_diagnostics_for_encoder(
    encoder: &AYEncoder,
) -> Option<PreferredVerifiedSolveDiagnostics> {
    if encoder.has_structural_ground_consequences() {
        clear_preferred_verified_solve_evidence();
        return None;
    }
    take_preferred_verified_solve_diagnostics()
}

pub(super) fn record_preferred_verified_solve_evidence(
    encoder: &mut AYEncoder,
    result: &mut VerificationResult,
) {
    if !matches!(result, VerificationResult::Verified(_)) {
        return;
    }
    crate::verify::authority_trace(|| {
        format!(
            "record_preferred_verified_solve_evidence entry {} structural={} proof_assert_mode={}",
            crate::verify::authority_result_tag(result),
            encoder.has_structural_ground_consequences(),
            in_proof_assert_mode()
        )
    });
    if encoder.has_structural_ground_consequences() {
        PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| {
            *slot.borrow_mut() = None;
        });
        return;
    }
    if in_proof_assert_mode() {
        let Some(summary) = encoder.authorize_current_stack_unsat_with_strict_proof() else {
            clear_preferred_verified_solve_evidence();
            return;
        };
        // Bind the public verdict to the same strict replay that supplied the
        // retained solve evidence. Keeping the ordinary incremental solver's
        // summary here can downgrade an otherwise fully certified slice at the
        // mandatory authority boundary, or worse, describe a different proof
        // than the certificate stored below.
        *result = VerificationResult::Verified(Some(summary));
    } else if matches!(result, VerificationResult::Verified(None)) {
        // The scope is proved, but the long-lived incremental encoder runs with
        // proof production OFF (`encoder/constructors.rs`), so its UNSAT arrives
        // with `verification_level=Trusted` and no proof artifact. The mandatory
        // authority boundary refuses an uncertified `Verified` — correctly, and
        // borrowing the base recheck's certificate would be worse still, since
        // that proof is about a different query.
        //
        // Rather than accept weaker evidence, ASK FOR THE STRONGER EVIDENCE:
        // re-derive THIS scope's proof on a fresh proof-producing solver.
        // `authorize_current_stack_unsat_with_strict_proof` replays the
        // identical closed stack (same declarations, same assertions, nothing
        // added or dropped) and returns `Some` only when the replay is UNSAT and
        // every raw authority field checks out — proof artifact present, zero
        // checker failures, zero trust steps, zero holes, every step checked —
        // and the summary is fully verified. It can therefore only supply
        // authority for a verdict that was already `Verified`; it can never
        // create one, and a genuinely satisfiable scope replays SAT (or runs out
        // its cap) and is left demoted exactly as before. Failure to obtain a
        // certificate leaves `Verified(None)` in place, i.e. fails closed.
        if let Some(summary) = encoder.authorize_current_stack_unsat_with_strict_proof() {
            *result = VerificationResult::Verified(Some(summary));
        }
    }
    let Some(evidence) = encoder
        .last_solve_evidence()
        .filter(|evidence| {
            evidence.accepted_for_consumer && solve_evidence_result_is_unsat(&evidence.result)
        })
        .cloned()
    else {
        return;
    };
    let statistics = encoder.last_solve_statistics().cloned();
    let proof_assert_mode = in_proof_assert_mode();
    let native_problem_json = if proof_assert_mode {
        encoder
            .strict_proof_native_replay_json()
            .map(ToOwned::to_owned)
    } else {
        encoder.native_replay_json().map(ToOwned::to_owned)
    };
    if proof_assert_mode
        && !statistics.as_ref().is_some_and(|statistics| {
            native_problem_json.is_some()
                && crate::encoder::ay_api::solve_snapshots_have_complete_unsat_proof(
                    &evidence, statistics,
                )
        })
    {
        clear_preferred_verified_solve_evidence();
        return;
    }
    let problem_hash = native_problem_json.as_deref().map(|replay| {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-wp.proof-assert-native-problem.v1\0");
        hasher.update(replay.as_bytes());
        hasher.finalize().into()
    });
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| {
        *slot.borrow_mut() = Some(PreferredVerifiedSolveDiagnostics {
            evidence,
            statistics,
            claim_identity: active_proof_assert_slice_identity(),
            problem_hash,
            native_problem_json,
            slice_generation: current_preferred_evidence_slice_generation(),
        });
    });
}

/// Preserve proof authority from an isolated solver lane whose query is exact
/// but does not run on the function encoder itself (for example native QF_BV).
/// The caller must still attach the exported strict proof summary to its
/// `VerificationResult`; this records the matching atomic solve envelope for
/// downstream provenance and replay.
pub(in crate::verify) fn record_isolated_strict_unsat_diagnostics(
    details: &ay_dpll::api::SolveDetails,
    native_problem_json: Option<String>,
) -> bool {
    if !crate::encoder::ay_api::solve_details_have_complete_unsat_proof(details) {
        crate::verify::authority_trace(|| {
            let stat = |key: &str| details.statistics.get_int(key);
            format!(
                "isolated strict UNSAT refused: unsat={} consumer_ok={} proof_checking={} \
                 proof_available={} proof_complete={} trust={:?} checked={:?} total={:?} \
                 skipped_holes={:?} failures={:?} unknown={:?}",
                details.result.is_unsat(),
                details.accept_for_consumer().is_ok(),
                details.verification_level.has_proof_checking(),
                details.verification.unsat_proof_available,
                details.statistics.proof_complete,
                stat("proof_trust"),
                stat("proof_checker_checked_steps"),
                stat("proof_checker_total_steps"),
                stat("proof_checker_skipped_hole_steps"),
                stat("proof_checker_failures"),
                details.unknown_summary().map(|s| s.reason_code.to_string()),
            )
        });
        clear_preferred_verified_solve_evidence();
        return false;
    }
    let evidence = SolveEvidenceSnapshot::from_solve_details(details);
    if !evidence.accepted_for_consumer || !solve_evidence_result_is_unsat(&evidence.result) {
        clear_preferred_verified_solve_evidence();
        return false;
    }
    let statistics = SolveStatisticsSnapshot::from(&details.statistics);
    let problem_hash = native_problem_json.as_deref().map(|replay| {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-wp.isolated-strict-native-problem.v1\0");
        hasher.update(replay.as_bytes());
        hasher.finalize().into()
    });
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| {
        *slot.borrow_mut() = Some(PreferredVerifiedSolveDiagnostics {
            evidence,
            statistics: Some(statistics),
            claim_identity: None,
            problem_hash,
            native_problem_json,
            slice_generation: current_preferred_evidence_slice_generation(),
        });
    });
    true
}

fn solve_evidence_result_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
}

fn try_prove_literal_false_negated_goal_with_solver_evidence(
    encoder: &mut AYEncoder,
    negated_ensure: Term,
    body_div_obligations: &[Term],
    post_div_obligations: &[Term],
    _obligation_index: usize,
) -> Result<Option<ResolveContinuation>, EncodingError> {
    let false_const = encoder.solver_mut().bool_const(false);
    if negated_ensure != false_const
        || !body_div_obligations.is_empty()
        || !post_div_obligations.is_empty()
    {
        return Ok(None);
    }

    // The contradiction is closed and independent of the surrounding encoder.
    // Prove it on a fresh proof-enabled solver so a large function context
    // cannot suppress certificate production or contaminate its provenance.
    let result = prove_prechecked_literal_false_with_solver_evidence();
    Ok(Some(ResolveContinuation::Continue(result)))
}

pub(super) fn prove_prechecked_literal_false_with_solver_evidence() -> VerificationResult {
    let mut encoder = AYEncoder::new();
    encoder.solver_mut().set_produce_proofs(true);
    if encoder
        .solver_mut()
        .try_set_option(":check-proofs-strict", "true")
        .is_err()
    {
        return VerificationResult::Unknown(UnknownReason::ProofTrusted);
    }
    let false_const = encoder.solver_mut().bool_const(false);
    let mut result = encoder.with_negated_goal_label_prefix(
        "__trust_wp_prechecked_literal_false".to_string(),
        |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                encoder.assert_term(false_const);
            });
            resolve_sat_result_without_vacuity(encoder)
        },
    );
    record_preferred_verified_solve_evidence(&mut encoder, &mut result);
    result
}

fn prefer_specific_fallback_unknown(
    original_reason: &UnknownReason,
    fallback_result: VerificationResult,
) -> VerificationResult {
    match fallback_result {
        VerificationResult::Unknown(UnknownReason::Unspecified) => {
            VerificationResult::Unknown(original_reason.clone())
        }
        other => other,
    }
}

fn should_rescue_with_axiom_free_sat(reason: &UnknownReason) -> bool {
    matches!(
        reason,
        UnknownReason::Timeout
            | UnknownReason::Incomplete
            | UnknownReason::QuantifierRoundLimit
            | UnknownReason::QuantifierDeferred
            | UnknownReason::QuantifierUnhandled
            | UnknownReason::QuantifierEmatchingExistsIncomplete
    )
}

fn should_abort_with_axiom_free_sat_after_solver_panic(reason: &UnknownReason) -> bool {
    matches!(
        reason,
        UnknownReason::SolverPanic(message)
            if message.contains("IncrementalTheoryState::pop() underflow")
    )
}

fn is_incremental_pop_underflow_error(error: &EncodingError) -> bool {
    error
        .to_string()
        .contains("IncrementalTheoryState::pop() underflow")
}

fn should_skip_axiom_free_probe_for_seq_ext_eq_index(ctx: &ObligationSliceContext<'_>) -> bool {
    let exprs = ctx
        .requires
        .iter()
        .chain(ctx.all_ensures.iter())
        .chain(ctx.return_expr);

    let mut has_ext_eq = false;
    let mut has_index = false;
    for expr in exprs {
        has_ext_eq |= expr_has_method(expr, |method| method == "ext_eq");
        has_index |= expr_has_method(expr, |method| matches!(method, "index" | "index_logic"));
        if has_ext_eq && has_index {
            return true;
        }
    }
    false
}

/// Recursive open logic functions have no global defining axiom; their
/// bounded ground definitions are materialized only in the full axiom phase.
/// An axiom-free solve that already mentions one of those functions therefore
/// cannot discharge a proof depending on its definition. More importantly,
/// AY can enter a non-interruptible recursive-UF search on that deliberately
/// incomplete stack, preventing the probe's 500ms timeout from returning and
/// starving the full ground-instance phase. Skip the optional probe when a
/// recursive open function is actually referenced by this obligation.
fn should_skip_axiom_free_probe_for_recursive_logic(ctx: &ObligationSliceContext<'_>) -> bool {
    let Some(logic_fns) = ctx.logic_fns else {
        return false;
    };
    let recursive_open_functions: Vec<(&str, &str)> = logic_fns
        .iter()
        .enumerate()
        .filter_map(|(index, logic_fn)| {
            let effective_mode = ctx
                .mode_overrides
                .and_then(|modes| modes.get(index).copied())
                .unwrap_or(logic_fn.mode());
            (logic_fn.is_recursive()
                && !logic_fn.is_opaque()
                && effective_mode == trust_wp_core::logic::LogicMode::Open)
                .then(|| (logic_fn.name(), logic_fn.full_path()))
        })
        .collect();
    if recursive_open_functions.is_empty() {
        return false;
    }

    ctx.requires
        .iter()
        .chain(ctx.all_ensures.iter())
        .chain(ctx.return_expr)
        .any(|expr| {
            expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |nested| {
                let call_name = match nested {
                    PureExpr::LogicFnCall { name, .. } => name.as_str(),
                    PureExpr::MethodCall { method, .. } => method.as_str(),
                    _ => return false,
                };
                recursive_open_functions.iter().any(|(name, full_path)| {
                    logic_fn_reference_name_matches(call_name, name, full_path)
                })
            })
        })
}

fn logic_fn_reference_name_matches(call_name: &str, name: &str, full_path: &str) -> bool {
    call_name == name
        || call_name == full_path
        || call_name
            .rsplit("::")
            .next()
            .is_some_and(|tail| tail == name)
}

fn expr_has_method(expr: &PureExpr, predicate: impl Fn(&str) -> bool) -> bool {
    expr.any_recursive_with_depth_limit(
        MAX_ENCODING_DEPTH,
        true,
        |e| matches!(e, PureExpr::MethodCall { method, .. } if predicate(method.as_str())),
    )
}

fn is_closure_counterexample_spec_method(method: &str) -> bool {
    matches!(method, "postcondition_mut" | "postcondition_once")
}

fn expr_has_closure_counterexample_spec_method(
    expr: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        let PureExpr::MethodCall { method, .. } = e else {
            return false;
        };
        is_closure_counterexample_spec_method(method)
            || (method == "postcondition" && ctx.mut_borrow_final_values.is_none())
    })
}

fn ctx_has_closure_counterexample_spec_method(
    ctx: &ObligationSliceContext<'_>,
    body_assumptions: &[&PureExpr],
) -> bool {
    ctx.requires
        .iter()
        .chain(ctx.all_ensures.iter())
        .chain(ctx.return_expr)
        .chain(body_assumptions.iter().copied())
        .any(|expr| expr_has_closure_counterexample_spec_method(expr, ctx))
}

fn has_validated_closure_unknown_counterexample(
    encoder: &AYEncoder,
    reason: &UnknownReason,
    ctx: &ObligationSliceContext<'_>,
    body_assumptions: &[&PureExpr],
) -> bool {
    let flags = encoder.closure_postcondition_flags();
    let encoder_has_counterexample_spec = if ctx.mut_borrow_final_values.is_some() {
        flags.has_fn || flags.has_once
    } else {
        flags.has_mut || flags.has_once || flags.has_fn
    };
    let ctx_has = ctx_has_closure_counterexample_spec_method(ctx, body_assumptions);
    if !(ctx_has || encoder_has_counterexample_spec) || !should_rescue_with_axiom_free_sat(reason) {
        return false;
    }
    encoder.last_solve_evidence().is_some_and(|evidence| {
        evidence.accepted_for_consumer
            && evidence.model_validated
            && evidence.result.eq_ignore_ascii_case("unknown")
    })
}

fn should_retry_without_axioms_after_unknown(reason: &UnknownReason) -> bool {
    matches!(
        reason,
        UnknownReason::Timeout
            | UnknownReason::Incomplete
            | UnknownReason::QuantifierRoundLimit
            | UnknownReason::QuantifierDeferred
            | UnknownReason::QuantifierUnhandled
            | UnknownReason::QuantifierEmatchingExistsIncomplete
    )
}

fn assert_direct_arithmetic_consequences(
    encoder: &mut AYEncoder,
    ctx: &ObligationSliceContext<'_>,
    obligation_index: usize,
) -> Result<(), EncodingError> {
    if let Some(fact) = triangular_sum_postcondition_consequence(ctx, obligation_index) {
        let term = encoder.encode_pure(&fact)?;
        encoder.assert_term(term);
    }
    if let Some(fact) = mut_borrow_final_disequality_consequence(ctx, obligation_index) {
        let term = encoder.encode_pure(&fact)?;
        encoder.assert_term(term);
    }
    Ok(())
}

fn iterator_produces_singleton_failure_result(
    ctx: &ObligationSliceContext<'_>,
    obligation_index: usize,
) -> Option<VerificationResult> {
    let ensure = ctx.all_ensures.get(obligation_index)?;
    let (_, produced_var, expected) = var_int_equality(ensure)?;
    if let Some(observed) = iterator_produces_singleton_observed_value(ctx.requires, produced_var) {
        return (observed != expected).then(|| crate::verify::structural_failed_traced());
    }
    iterator_produces_singleton_unconstrained(ctx.requires, produced_var)
        .then(|| crate::verify::structural_failed_traced())
}

fn iterator_produces_singleton_observed_value(
    requires: &[PureExpr],
    produced_var: &str,
) -> Option<i64> {
    if requires.len() != 3 {
        return None;
    }

    let mut receiver: Option<&PureExpr> = None;
    let mut observed_value = None;
    let mut has_positive_len = false;
    let mut has_produces = false;

    for require in requires {
        if let Some((candidate, value)) = seq_index_zero_int_equality(require) {
            if !merge_same_receiver(&mut receiver, candidate) {
                return None;
            }
            observed_value = Some(value);
            continue;
        }
        if let Some(candidate) = positive_seq_len_requirement(require) {
            if !merge_same_receiver(&mut receiver, candidate) {
                return None;
            }
            has_positive_len = true;
            continue;
        }
        if let Some(candidate) = singleton_produces_receiver(require, produced_var) {
            if !merge_same_receiver(&mut receiver, candidate) {
                return None;
            }
            has_produces = true;
            continue;
        }
        return None;
    }

    (has_positive_len && has_produces).then_some(observed_value?)
}

fn iterator_produces_singleton_unconstrained(requires: &[PureExpr], produced_var: &str) -> bool {
    if requires.is_empty() {
        return false;
    }
    let mut receiver: Option<&PureExpr> = None;
    let mut has_produces = false;

    for require in requires {
        if seq_index_zero_int_equality(require).is_some() {
            return false;
        }
        if let Some(candidate) = positive_seq_len_requirement(require) {
            if !merge_same_receiver(&mut receiver, candidate) {
                return false;
            }
            continue;
        }
        if let Some(candidate) = singleton_produces_receiver(require, produced_var) {
            if !merge_same_receiver(&mut receiver, candidate) {
                return false;
            }
            has_produces = true;
            continue;
        }
        return false;
    }

    has_produces
}

fn merge_same_receiver<'a>(slot: &mut Option<&'a PureExpr>, candidate: &'a PureExpr) -> bool {
    if let Some(existing) = slot {
        existing == &candidate
    } else {
        *slot = Some(candidate);
        true
    }
}

fn seq_index_zero_int_equality(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    seq_index_zero_int_equality_sides(left, right)
        .or_else(|| seq_index_zero_int_equality_sides(right, left))
}

fn seq_index_zero_int_equality_sides<'a>(
    index_expr: &'a PureExpr,
    value_expr: &PureExpr,
) -> Option<(&'a PureExpr, i64)> {
    let PureExpr::Int(value) = value_expr else {
        return None;
    };
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = index_expr
    else {
        return None;
    };
    (method == "index_logic" && matches!(args.as_slice(), [PureExpr::Int(0)]))
        .then_some((receiver.as_ref(), *value))
}

fn positive_seq_len_requirement(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            seq_len_positive_eq_side(left, right).or_else(|| seq_len_positive_eq_side(right, left))
        }
        PureExpr::BinOp(left, BinOp::Gt, right) if matches!(right.as_ref(), PureExpr::Int(0)) => {
            seq_len_receiver(left)
        }
        PureExpr::BinOp(left, BinOp::Lt, right) if matches!(left.as_ref(), PureExpr::Int(0)) => {
            seq_len_receiver(right)
        }
        _ => None,
    }
}

fn seq_len_positive_eq_side<'a>(
    len_expr: &'a PureExpr,
    value_expr: &PureExpr,
) -> Option<&'a PureExpr> {
    let PureExpr::Int(value) = value_expr else {
        return None;
    };
    (*value > 0).then(|| seq_len_receiver(len_expr)).flatten()
}

fn seq_len_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == "len" && args.is_empty()).then_some(receiver.as_ref())
}

fn singleton_produces_receiver<'a>(expr: &'a PureExpr, produced_var: &str) -> Option<&'a PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "ext_eq" {
        return None;
    }
    let [other] = args.as_slice() else {
        return None;
    };
    is_singleton_concat_for_var(other, produced_var).then_some(receiver.as_ref())
}

fn is_singleton_concat_for_var(expr: &PureExpr, produced_var: &str) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    if method != "concat" || args.len() != 1 {
        return false;
    }
    let PureExpr::LogicFnCall { name, args } = receiver.as_ref() else {
        return false;
    };
    matches!(
        (name.as_str(), args.as_slice()),
        ("seq" | "Seq::singleton", [PureExpr::Var(var, _)]) if var == produced_var
    )
}

fn var_int_equality(expr: &PureExpr) -> Option<(&PureExpr, &str, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    var_int_equality_sides(left, right).or_else(|| var_int_equality_sides(right, left))
}

fn var_int_equality_sides<'a>(
    var_expr: &'a PureExpr,
    value_expr: &PureExpr,
) -> Option<(&'a PureExpr, &'a str, i64)> {
    let PureExpr::Var(name, _) = var_expr else {
        return None;
    };
    let PureExpr::Int(value) = value_expr else {
        return None;
    };
    Some((var_expr, name.as_str(), *value))
}

pub(in crate::verify) fn mut_borrow_final_disequality_consequence(
    ctx: &ObligationSliceContext<'_>,
    obligation_index: usize,
) -> Option<PureExpr> {
    let final_values = ctx.mut_borrow_final_values?;
    let ensure = ctx.all_ensures.get(obligation_index)?;
    let PureExpr::BinOp(left, BinOp::Ne, right) = ensure else {
        return None;
    };
    let left_name = final_expr_base_name(left)?;
    let right_name = final_expr_base_name(right)?;
    if left_name == right_name {
        return None;
    }
    // A mutation-continued parameter's `final_values` entry is not asserted
    // (the callee postcondition alone constrains its prophecy), so it cannot
    // justify a structural consequence.
    if ctx
        .mutation_continued_params
        .is_some_and(|params| params.contains(left_name) || params.contains(right_name))
    {
        return None;
    }
    let left_final = final_values.get(left_name)?;
    let right_final = final_values.get(right_name)?;

    mut_borrow_final_values_prove_distinct(left_final, right_final).then(|| ensure.clone())
}

fn final_expr_base_name(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Final(inner) = expr else {
        return None;
    };
    peel_deref_var_name(inner)
}

fn peel_deref_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => peel_deref_var_name(inner),
        _ => None,
    }
}

fn mut_borrow_final_values_prove_distinct(left: &PureExpr, right: &PureExpr) -> bool {
    let Some(left_cases) = expand_arithmetic_ite_cases(left) else {
        return false;
    };
    let Some(right_cases) = expand_arithmetic_ite_cases(right) else {
        return false;
    };
    if left_cases.is_empty()
        || right_cases.is_empty()
        || left_cases.len().saturating_mul(right_cases.len())
            > MUT_BORROW_FINAL_DISEQUALITY_MAX_CASE_PAIRS
    {
        return false;
    }

    for left_case in &left_cases {
        for right_case in &right_cases {
            let mut path = Vec::with_capacity(left_case.path.len() + right_case.path.len());
            path.extend(left_case.path.iter().cloned());
            path.extend(right_case.path.iter().cloned());
            if !arithmetic_path_proves_distinct(&path, &left_case.value, &right_case.value) {
                return false;
            }
        }
    }
    true
}

#[derive(Debug, Clone)]
struct ArithmeticIteCase {
    value: PureExpr,
    path: Vec<PureExpr>,
}

fn expand_arithmetic_ite_cases(expr: &PureExpr) -> Option<Vec<ArithmeticIteCase>> {
    expand_arithmetic_ite_cases_inner(expr, MUT_BORROW_FINAL_DISEQUALITY_MAX_CASES)
}

fn expand_arithmetic_ite_cases_inner(
    expr: &PureExpr,
    max_cases: usize,
) -> Option<Vec<ArithmeticIteCase>> {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(_, _) => {
            Some(vec![ArithmeticIteCase {
                value: expr.clone(),
                path: Vec::new(),
            }])
        }
        PureExpr::BinOp(left, op, right) if arithmetic_ite_binop_supported(*op) => {
            let left_cases = expand_arithmetic_ite_cases_inner(left, max_cases)?;
            let right_cases = expand_arithmetic_ite_cases_inner(right, max_cases)?;
            combine_arithmetic_cases(&left_cases, &right_cases, max_cases, |left, right| {
                PureExpr::BinOp(Arc::new(left.clone()), *op, Arc::new(right.clone()))
            })
        }
        PureExpr::UnOp(op @ (UnOp::Not | UnOp::Neg), inner) => {
            let inner_cases = expand_arithmetic_ite_cases_inner(inner, max_cases)?;
            map_arithmetic_cases(&inner_cases, max_cases, |inner| {
                PureExpr::UnOp(*op, Arc::new(inner.clone()))
            })
        }
        PureExpr::Ite(condition, then_expr, else_expr) => {
            let condition_cases = expand_arithmetic_ite_cases_inner(condition, max_cases)?;
            let then_cases = expand_arithmetic_ite_cases_inner(then_expr, max_cases)?;
            let else_cases = expand_arithmetic_ite_cases_inner(else_expr, max_cases)?;
            let mut out = Vec::new();
            for condition_case in &condition_cases {
                for then_case in &then_cases {
                    push_arithmetic_branch_case(
                        &mut out,
                        condition_case,
                        then_case,
                        condition_case.value.clone(),
                        max_cases,
                    )?;
                }
                for else_case in &else_cases {
                    push_arithmetic_branch_case(
                        &mut out,
                        condition_case,
                        else_case,
                        not_expr(condition_case.value.clone()),
                        max_cases,
                    )?;
                }
            }
            Some(out)
        }
        PureExpr::Old(inner) => {
            let inner_cases = expand_arithmetic_ite_cases_inner(inner, max_cases)?;
            map_arithmetic_cases(&inner_cases, max_cases, |inner| {
                PureExpr::Old(Arc::new(inner.clone()))
            })
        }
        PureExpr::Deref(inner) if wrapper_chain_base_name(inner).is_some() => {
            Some(vec![ArithmeticIteCase {
                value: expr.clone(),
                path: Vec::new(),
            }])
        }
        PureExpr::Final(inner) if wrapper_chain_base_name(inner).is_some() => {
            Some(vec![ArithmeticIteCase {
                value: expr.clone(),
                path: Vec::new(),
            }])
        }
        _ => None,
    }
}

fn arithmetic_ite_binop_supported(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add
            | BinOp::Sub
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or
            | BinOp::Implies
    )
}

fn combine_arithmetic_cases(
    left_cases: &[ArithmeticIteCase],
    right_cases: &[ArithmeticIteCase],
    max_cases: usize,
    build: impl Fn(&PureExpr, &PureExpr) -> PureExpr,
) -> Option<Vec<ArithmeticIteCase>> {
    let mut out = Vec::new();
    for left_case in left_cases {
        for right_case in right_cases {
            if out.len() >= max_cases {
                return None;
            }
            let mut path = Vec::with_capacity(left_case.path.len() + right_case.path.len());
            path.extend(left_case.path.iter().cloned());
            path.extend(right_case.path.iter().cloned());
            out.push(ArithmeticIteCase {
                value: build(&left_case.value, &right_case.value),
                path,
            });
        }
    }
    Some(out)
}

fn map_arithmetic_cases(
    cases: &[ArithmeticIteCase],
    max_cases: usize,
    build: impl Fn(&PureExpr) -> PureExpr,
) -> Option<Vec<ArithmeticIteCase>> {
    let mut out = Vec::new();
    for case in cases {
        if out.len() >= max_cases {
            return None;
        }
        out.push(ArithmeticIteCase {
            value: build(&case.value),
            path: case.path.clone(),
        });
    }
    Some(out)
}

fn push_arithmetic_branch_case(
    out: &mut Vec<ArithmeticIteCase>,
    condition_case: &ArithmeticIteCase,
    value_case: &ArithmeticIteCase,
    branch_condition: PureExpr,
    max_cases: usize,
) -> Option<()> {
    if out.len() >= max_cases {
        return None;
    }
    let mut path = Vec::with_capacity(condition_case.path.len() + 1 + value_case.path.len());
    path.extend(condition_case.path.iter().cloned());
    path.push(branch_condition);
    path.extend(value_case.path.iter().cloned());
    out.push(ArithmeticIteCase {
        value: value_case.value.clone(),
        path,
    });
    Some(())
}

fn not_expr(expr: PureExpr) -> PureExpr {
    match expr {
        PureExpr::Bool(value) => PureExpr::Bool(!value),
        PureExpr::UnOp(UnOp::Not, inner) => inner.as_ref().clone(),
        other => PureExpr::UnOp(UnOp::Not, Arc::new(other)),
    }
}

fn wrapper_chain_base_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            wrapper_chain_base_name(inner)
        }
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UnitAffine {
    symbol: Option<String>,
    constant: i64,
}

impl UnitAffine {
    fn constant(value: i64) -> Self {
        Self {
            symbol: None,
            constant: value,
        }
    }

    fn symbol(symbol: String) -> Self {
        Self {
            symbol: Some(symbol),
            constant: 0,
        }
    }

    fn add(&self, other: &Self) -> Option<Self> {
        match (&self.symbol, &other.symbol) {
            (None, None) => Some(Self::constant(self.constant.checked_add(other.constant)?)),
            (Some(symbol), None) => Some(Self {
                symbol: Some(symbol.clone()),
                constant: self.constant.checked_add(other.constant)?,
            }),
            (None, Some(symbol)) => Some(Self {
                symbol: Some(symbol.clone()),
                constant: self.constant.checked_add(other.constant)?,
            }),
            (Some(_), Some(_)) => None,
        }
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        match (&self.symbol, &other.symbol) {
            (None, None) => Some(Self::constant(self.constant.checked_sub(other.constant)?)),
            (Some(symbol), None) => Some(Self {
                symbol: Some(symbol.clone()),
                constant: self.constant.checked_sub(other.constant)?,
            }),
            _ => None,
        }
    }
}

fn unit_affine(expr: &PureExpr) -> Option<UnitAffine> {
    match expr {
        PureExpr::Int(value) => Some(UnitAffine::constant(*value)),
        PureExpr::Var(name, _) => Some(UnitAffine::symbol(name.clone())),
        PureExpr::Deref(_) | PureExpr::Final(_) | PureExpr::Old(_) => {
            Some(UnitAffine::symbol(arithmetic_atom_name(expr)?))
        }
        PureExpr::BinOp(left, BinOp::Add, right) => unit_affine(left)?.add(&unit_affine(right)?),
        PureExpr::BinOp(left, BinOp::Sub, right) => unit_affine(left)?.sub(&unit_affine(right)?),
        PureExpr::UnOp(UnOp::Neg, inner) => {
            let inner = unit_affine(inner)?;
            if inner.symbol.is_some() {
                return None;
            }
            Some(UnitAffine::constant(inner.constant.checked_neg()?))
        }
        _ => None,
    }
}

fn arithmetic_atom_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(name.clone()),
        PureExpr::Old(inner) => Some(format!("old({})", arithmetic_atom_name(inner)?)),
        PureExpr::Deref(inner) => Some(format!("*{}", arithmetic_atom_name(inner)?)),
        PureExpr::Final(inner) => Some(format!("^{}", arithmetic_atom_name(inner)?)),
        _ => None,
    }
}

fn arithmetic_path_proves_distinct(path: &[PureExpr], left: &PureExpr, right: &PureExpr) -> bool {
    let Some(left) = unit_affine(left) else {
        return false;
    };
    let Some(right) = unit_affine(right) else {
        return false;
    };
    let Some(mut bounds) = DifferenceBounds::from_path(path) else {
        return false;
    };
    bounds.close();
    if bounds.is_inconsistent() {
        return true;
    }
    unit_affines_prove_distinct(&bounds, &left, &right)
}

fn unit_affines_prove_distinct(
    bounds: &DifferenceBounds,
    left: &UnitAffine,
    right: &UnitAffine,
) -> bool {
    if left.symbol == right.symbol && left.constant != right.constant {
        return true;
    }

    let Some(left_over_right_threshold) = right
        .constant
        .checked_sub(left.constant)
        .and_then(|value| value.checked_add(1))
    else {
        return false;
    };
    if bounds
        .lower_bound(right.symbol.as_deref(), left.symbol.as_deref())
        .is_some_and(|bound| bound >= left_over_right_threshold)
    {
        return true;
    }

    let Some(right_over_left_threshold) = left
        .constant
        .checked_sub(right.constant)
        .and_then(|value| value.checked_add(1))
    else {
        return false;
    };
    bounds
        .lower_bound(left.symbol.as_deref(), right.symbol.as_deref())
        .is_some_and(|bound| bound >= right_over_left_threshold)
}

struct DifferenceBounds {
    symbols: HashMap<String, usize>,
    lower_bounds: Vec<Vec<Option<i64>>>,
}

impl DifferenceBounds {
    fn from_path(path: &[PureExpr]) -> Option<Self> {
        let mut bounds = Self::new();
        for condition in path {
            bounds.add_path_condition(condition)?;
        }
        Some(bounds)
    }

    fn new() -> Self {
        let mut symbols = HashMap::new();
        symbols.insert(String::new(), 0);
        Self {
            symbols,
            lower_bounds: vec![vec![Some(0)]],
        }
    }

    fn add_path_condition(&mut self, condition: &PureExpr) -> Option<()> {
        match condition {
            PureExpr::Bool(true) => Some(()),
            PureExpr::Bool(false) => {
                self.mark_inconsistent();
                Some(())
            }
            PureExpr::BinOp(left, BinOp::And, right) => {
                self.add_path_condition(left)?;
                self.add_path_condition(right)
            }
            PureExpr::BinOp(left, BinOp::Eq, right) => {
                self.add_order_constraint(left, right, false)?;
                self.add_order_constraint(right, left, false)
            }
            PureExpr::BinOp(left, BinOp::Lt, right) => self.add_order_constraint(left, right, true),
            PureExpr::BinOp(left, BinOp::Le, right) => {
                self.add_order_constraint(left, right, false)
            }
            PureExpr::BinOp(left, BinOp::Gt, right) => self.add_order_constraint(right, left, true),
            PureExpr::BinOp(left, BinOp::Ge, right) => {
                self.add_order_constraint(right, left, false)
            }
            PureExpr::UnOp(UnOp::Not, inner) => self.add_negated_path_condition(inner),
            _ => None,
        }
    }

    fn add_negated_path_condition(&mut self, condition: &PureExpr) -> Option<()> {
        match condition {
            PureExpr::Bool(value) => self.add_path_condition(&PureExpr::Bool(!value)),
            PureExpr::BinOp(left, BinOp::Lt, right) => {
                self.add_order_constraint(right, left, false)
            }
            PureExpr::BinOp(left, BinOp::Le, right) => self.add_order_constraint(right, left, true),
            PureExpr::BinOp(left, BinOp::Gt, right) => {
                self.add_order_constraint(left, right, false)
            }
            PureExpr::BinOp(left, BinOp::Ge, right) => self.add_order_constraint(left, right, true),
            PureExpr::BinOp(left, BinOp::Eq, right) => {
                let left = unit_affine(left)?;
                let right = unit_affine(right)?;
                if left.symbol == right.symbol {
                    if left.constant == right.constant {
                        self.mark_inconsistent();
                    }
                    Some(())
                } else {
                    None
                }
            }
            PureExpr::UnOp(UnOp::Not, inner) => self.add_path_condition(inner),
            _ => None,
        }
    }

    fn add_order_constraint(
        &mut self,
        left: &PureExpr,
        right: &PureExpr,
        strict: bool,
    ) -> Option<()> {
        let left = unit_affine(left)?;
        let right = unit_affine(right)?;
        let margin = i64::from(strict);
        let weight = left
            .constant
            .checked_sub(right.constant)?
            .checked_add(margin)?;
        self.add_lower_bound(left.symbol.as_deref(), right.symbol.as_deref(), weight);
        Some(())
    }

    fn add_lower_bound(&mut self, source: Option<&str>, target: Option<&str>, weight: i64) {
        let source = self.symbol_index(source);
        let target = self.symbol_index(target);
        let entry = &mut self.lower_bounds[source][target];
        if entry.is_none_or(|existing| weight > existing) {
            *entry = Some(weight);
        }
    }

    fn symbol_index(&mut self, symbol: Option<&str>) -> usize {
        let symbol = symbol.unwrap_or("");
        if let Some(index) = self.symbols.get(symbol) {
            return *index;
        }
        let index = self.symbols.len();
        self.symbols.insert(symbol.to_string(), index);
        for row in &mut self.lower_bounds {
            row.push(None);
        }
        self.lower_bounds.push(vec![None; index + 1]);
        self.lower_bounds[index][index] = Some(0);
        index
    }

    fn close(&mut self) {
        let len = self.lower_bounds.len();
        for pivot in 0..len {
            for source in 0..len {
                let Some(source_to_pivot) = self.lower_bounds[source][pivot] else {
                    continue;
                };
                for target in 0..len {
                    let Some(pivot_to_target) = self.lower_bounds[pivot][target] else {
                        continue;
                    };
                    let Some(candidate) = source_to_pivot.checked_add(pivot_to_target) else {
                        continue;
                    };
                    let entry = &mut self.lower_bounds[source][target];
                    if entry.is_none_or(|existing| candidate > existing) {
                        *entry = Some(candidate);
                    }
                }
            }
        }
    }

    fn is_inconsistent(&self) -> bool {
        self.lower_bounds
            .iter()
            .enumerate()
            .any(|(index, row)| row[index].is_some_and(|bound| bound > 0))
    }

    fn lower_bound(&self, source: Option<&str>, target: Option<&str>) -> Option<i64> {
        let source = self.symbols.get(source.unwrap_or(""))?;
        let target = self.symbols.get(target.unwrap_or(""))?;
        self.lower_bounds[*source][*target]
    }

    fn mark_inconsistent(&mut self) {
        self.add_lower_bound(None, None, 1);
    }
}

fn triangular_sum_postcondition_consequence(
    ctx: &ObligationSliceContext<'_>,
    obligation_index: usize,
) -> Option<PureExpr> {
    let ensure = ctx.all_ensures.get(obligation_index)?;
    let (goal_value, goal_index) = triangular_division_postcondition_parts(ensure)
        .or_else(|| triangular_expanded_postcondition_parts(ensure))?;
    let return_expr = ctx.return_expr?;

    for req in ctx.requires {
        let Some((accumulator, produced_len)) = triangular_sum_invariant_parts(req) else {
            continue;
        };
        if !postcondition_value_matches_accumulator(
            goal_value,
            return_expr,
            accumulator,
            ctx.requires,
        ) {
            continue;
        }
        if !context_completes_len_to_goal_index(ctx.requires, produced_len, goal_index) {
            continue;
        }
        return Some(expanded_triangular_equality(goal_value, goal_index));
    }

    None
}

fn postcondition_value_matches_accumulator(
    goal_value: &PureExpr,
    return_expr: &PureExpr,
    accumulator: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    expr_same_mod_view(goal_value, accumulator)
        || (is_result_value(goal_value) && expr_same_mod_view(return_expr, accumulator))
        || requires
            .iter()
            .any(|req| equality_connects(req, goal_value, accumulator))
}

fn is_result_value(expr: &PureExpr) -> bool {
    matches!(strip_outer_views(expr), PureExpr::Var(name, _) if name == "result")
}

fn triangular_division_postcondition_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    triangular_division_orientation(lhs, rhs).or_else(|| triangular_division_orientation(rhs, lhs))
}

fn triangular_division_orientation<'a>(
    value: &'a PureExpr,
    rhs: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let PureExpr::BinOp(numerator, BinOp::Div, denominator) = rhs else {
        return None;
    };
    if !matches!(denominator.as_ref(), PureExpr::Int(2)) {
        return None;
    }
    let index = triangular_product_index(numerator)?;
    Some((value, index))
}

fn triangular_expanded_postcondition_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    triangular_expanded_orientation(lhs, rhs).or_else(|| triangular_expanded_orientation(rhs, lhs))
}

fn triangular_expanded_orientation<'a>(
    twice_value: &'a PureExpr,
    expanded: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let value = times_two_operand(twice_value)?;
    let index = expanded_triangular_index(expanded)?;
    Some((value, index))
}

fn triangular_sum_invariant_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    triangular_sum_invariant_orientation(lhs, rhs)
        .or_else(|| triangular_sum_invariant_orientation(rhs, lhs))
}

fn triangular_sum_invariant_orientation<'a>(
    twice_accumulator: &'a PureExpr,
    triangular_product: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let accumulator = times_two_operand(twice_accumulator)?;
    let produced_len = triangular_product_index(triangular_product)?;
    Some((accumulator, produced_len))
}

fn times_two_operand(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Mul, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (PureExpr::Int(2), value) | (value, PureExpr::Int(2)) => Some(value),
        _ => None,
    }
}

fn triangular_product_index(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Mul, rhs) = expr else {
        return None;
    };
    if is_plus_one_of(rhs, lhs) {
        return Some(lhs.as_ref());
    }
    if is_plus_one_of(lhs, rhs) {
        return Some(rhs.as_ref());
    }
    None
}

fn expanded_triangular_index(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return None;
    };
    square_of(lhs, rhs).or_else(|| square_of(rhs, lhs))
}

fn square_of<'a>(square: &'a PureExpr, linear: &'a PureExpr) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Mul, rhs) = square else {
        return None;
    };
    (expr_same_mod_view(lhs, linear) && expr_same_mod_view(rhs, linear)).then_some(linear)
}

fn is_plus_one_of(candidate: &PureExpr, base: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = candidate else {
        return false;
    };
    matches!(
        (lhs.as_ref(), rhs.as_ref()),
        (PureExpr::Int(1), other) | (other, PureExpr::Int(1)) if expr_same_mod_view(other, base)
    )
}

fn context_completes_len_to_goal_index(
    requires: &[PureExpr],
    produced_len: &PureExpr,
    goal_index: &PureExpr,
) -> bool {
    requires
        .iter()
        .any(|req| direct_len_completion(req, produced_len, goal_index))
        || (requires
            .iter()
            .any(|req| inclusive_start_one_len_completion(req, produced_len, goal_index))
            && requires
                .iter()
                .any(|req| nonnegative_bound_for_goal_index(req, goal_index)))
}

fn direct_len_completion(expr: &PureExpr, produced_len: &PureExpr, goal_index: &PureExpr) -> bool {
    let Some((lhs, rhs)) = equality_sides(expr) else {
        return false;
    };
    (same_len_expr(lhs, produced_len) && expr_same_mod_view(rhs, goal_index))
        || (same_len_expr(rhs, produced_len) && expr_same_mod_view(lhs, goal_index))
}

fn inclusive_start_one_len_completion(
    expr: &PureExpr,
    produced_len: &PureExpr,
    goal_index: &PureExpr,
) -> bool {
    let Some((lhs, rhs)) = equality_sides(expr) else {
        return false;
    };
    (same_len_expr(lhs, produced_len) && inclusive_start_one_len_expr(rhs, goal_index))
        || (same_len_expr(rhs, produced_len) && inclusive_start_one_len_expr(lhs, goal_index))
}

fn inclusive_start_one_len_expr(expr: &PureExpr, goal_index: &PureExpr) -> bool {
    let PureExpr::Ite(condition, then_expr, else_expr) = expr else {
        return false;
    };
    matches!(else_expr.as_ref(), PureExpr::Int(0))
        && inclusive_nonempty_condition(condition, goal_index)
        && inclusive_start_one_span(then_expr, goal_index)
}

fn inclusive_nonempty_condition(expr: &PureExpr, goal_index: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            expr_same_mod_view(lhs, goal_index) && matches!(rhs.as_ref(), PureExpr::Int(1))
        }
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(1)) && expr_same_mod_view(rhs, goal_index)
        }
        _ => false,
    }
}

fn inclusive_start_one_span(expr: &PureExpr, goal_index: &PureExpr) -> bool {
    if expr_same_mod_view(expr, goal_index) {
        return true;
    }
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return false;
    };
    (is_goal_minus_one(lhs, goal_index) && matches!(rhs.as_ref(), PureExpr::Int(1)))
        || (matches!(lhs.as_ref(), PureExpr::Int(1)) && is_goal_minus_one(rhs, goal_index))
}

fn is_goal_minus_one(expr: &PureExpr, goal_index: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Sub, rhs) = expr else {
        return false;
    };
    expr_same_mod_view(lhs, goal_index) && matches!(rhs.as_ref(), PureExpr::Int(1))
}

fn nonnegative_bound_for_goal_index(expr: &PureExpr, goal_index: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && expr_same_mod_view(rhs, goal_index)
        }
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            expr_same_mod_view(lhs, goal_index) && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        _ => false,
    }
}

fn equality_sides(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    Some((lhs.as_ref(), rhs.as_ref()))
}

fn equality_connects(expr: &PureExpr, first: &PureExpr, second: &PureExpr) -> bool {
    let Some((lhs, rhs)) = equality_sides(expr) else {
        return false;
    };
    (expr_same_mod_view(lhs, first) && expr_same_mod_view(rhs, second))
        || (expr_same_mod_view(lhs, second) && expr_same_mod_view(rhs, first))
}

fn same_len_expr(actual: &PureExpr, expected: &PureExpr) -> bool {
    len_base_name(actual)
        .zip(len_base_name(expected))
        .is_some_and(|(actual, expected)| actual == expected)
}

fn len_base_name(expr: &PureExpr) -> Option<&str> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "len" || !args.is_empty() {
        return None;
    }
    collection_base_name(receiver)
}

fn collection_base_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner) => collection_base_name(inner),
        _ => None,
    }
}

fn expanded_triangular_equality(value: &PureExpr, index: &PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(value.clone()),
            BinOp::Mul,
            Arc::new(PureExpr::Int(2)),
        )),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(index.clone()),
                BinOp::Mul,
                Arc::new(index.clone()),
            )),
            BinOp::Add,
            Arc::new(index.clone()),
        )),
    )
}

fn strip_outer_views(mut expr: &PureExpr) -> &PureExpr {
    while let PureExpr::View(inner) = expr {
        expr = inner;
    }
    expr
}

fn expr_same_mod_view(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        strip_outer_views(lhs),
        strip_outer_views(rhs),
    )
}

pub(super) type FreshBaseRecheckFn<'a> = dyn Fn() -> Result<VerificationResult, EncodingError> + 'a;

// ── Per-obligation shared tail (#1576 Slice A) ────────────────────────

/// Selects the alias constraint re-assertion strategy for the post-negation tail.
#[derive(Clone, Copy)]
pub(super) enum AliasConstraintMode {
    /// By-value alias constraints for standard function verification.
    ByValue,
    /// Current-chain alias constraints for mutable-borrow verification.
    CurrentChain,
}

/// Parameters for per-slice verification shared across all obligation slices.
pub(super) struct ObligationSliceContext<'a> {
    pub(super) all_ensures: &'a [PureExpr],
    pub(super) requires: &'a [PureExpr],
    pub(super) logic_fns: Option<&'a [trust_wp_core::logic::LogicFnDef]>,
    pub(super) mode_overrides: Option<&'a [trust_wp_core::logic::LogicMode]>,
    pub(super) type_invariants: Option<&'a [TypeInvariantDef]>,
    pub(super) return_expr: Option<&'a PureExpr>,
    pub(super) mut_borrow_final_values: Option<&'a HashMap<String, PureExpr>>,
    pub(super) mutation_continued_params: Option<&'a HashSet<String>>,
    pub(super) body_div_obligations: &'a [Term],
    pub(super) fresh_base_recheck: Option<&'a FreshBaseRecheckFn<'a>>,
    /// The AxiomLight fresh base recheck that records a refutation WITNESS on
    /// a validated SAT (`resolve_base_sat_result_with_witness`). A structural
    /// slice refutation the solver cannot confirm uses it: the shape proves
    /// `requires ⟹ ¬ensure`, so a validated model of the base is a validated
    /// counterexample.
    pub(super) literal_false_base_recheck: Option<&'a FreshBaseRecheckFn<'a>>,
    pub(super) slice_length_stable_vars: Option<&'a Vec<String>>,
    /// Latched to `true` when a base recheck for one of this obligation's
    /// slices hit a pathological (hard-timeout) base solve. Later slices of
    /// the same obligation then skip both base recheck strategies and go
    /// straight to the #2414 fresh rescue — the base is the same, so
    /// re-solving it would churn again (and the classic in-worker recheck
    /// would lose the live encoder).
    pub(super) base_recheck_pathology: std::cell::Cell<bool>,
}

impl ObligationSliceContext<'_> {
    /// Base vacuity recheck for a proven slice: encoder-preserving when the
    /// #2414 fresh rescue is available downstream, classic otherwise.
    fn base_recheck_for_slice(&self, encoder: &mut AYEncoder) -> ResolveContinuation {
        if self.fresh_base_recheck.is_some() {
            run_base_recheck_preserving_encoder(
                encoder,
                &self.base_recheck_pathology,
                BaseRecheckEncoderDisposition::Live,
            )
        } else {
            run_base_recheck_with_tight_timeout(encoder)
        }
    }
}

/// Goal-side sort-coercion guard, part 1 (#knights_tour soundness guard):
/// whether encoding the negated goal introduced a `SortCoercionBridge`
/// increment relative to the snapshot taken just before the goal encode.
///
/// A coercion bridge inside the GOAL means the negated postcondition ranges
/// over fresh, completely unconstrained constants that are provably
/// disconnected from the program state. A `sat` model for such a goal is
/// meaningless as a counterexample. This mirrors how the axiom side treats
/// the same counter (`unfolding_recursive_call_was_coerced` →
/// `SpecAxiomDropped` in `verify/function/mod.rs`).
pub(in crate::verify) fn negated_goal_encode_introduced_sort_coercion(
    before: &unsoundness::Snapshot,
) -> bool {
    let after = unsoundness::snapshot();
    unsoundness::delta(before, &after)
        .get(&unsoundness::UnsoundnessCategory::SortCoercionBridge)
        .is_some_and(|&count| count > 0)
}

/// Goal-side sort-coercion guard, part 2: demote a `Failed(counterexample)`
/// slice result to `Unknown` when the negated goal itself was encoded through
/// unconstrained sort-coercion constants (see
/// [`negated_goal_encode_introduced_sort_coercion`]).
///
/// This can never cause a false ACCEPT: it only weakens acceptance of a
/// counterexample (`Failed`) into `Unknown`; `Verified` results are untouched
/// (and a coerced goal cannot manufacture UNSAT from the disconnected
/// constants any more easily — if anything the guard is conservative).
pub(in crate::verify) fn demote_sort_coerced_goal_counterexample(
    cont: ResolveContinuation,
    obligation_index: usize,
) -> ResolveContinuation {
    let demote = |result: VerificationResult| -> VerificationResult {
        match result {
            VerificationResult::Failed(_) => {
                debug!(
                    "[TRUST_WP_DEBUG] slice {obligation_index}: sat accepted over a negated \
                     goal that required sort-coercion bridging; the model ranges over \
                     unconstrained coercion constants — demoting counterexample to Unknown"
                );
                VerificationResult::Unknown(UnknownReason::Demoted(
                    "sort-coercion bridge in negated goal: counterexample model ranges over \
                     unconstrained coercion constants disconnected from the program state"
                        .to_string(),
                ))
            }
            other => other,
        }
    };
    match cont {
        ResolveContinuation::Continue(result) => ResolveContinuation::Continue(demote(result)),
        ResolveContinuation::Abort(result) => ResolveContinuation::Abort(demote(result)),
    }
}

/// Execute the shared post-negation verification tail.
///
/// Steps:
/// 1. Re-assert alias constraints (by-value or current-chain).
/// 2. Assert standard axioms.
/// 3. Assert recursive logic fn ground instances.
/// 4. Assert eager negated existential instantiations.
/// 5. Assert ground pool instances.
/// 6. Push a nested scope, assert the negated disjunction
///    (`NOT ensure OR NOT div_1 OR ...`), and solve it.
/// 7. If the nested scope is UNSAT, pop it and explicitly re-solve the
///    base slice context to distinguish genuine proofs from vacuous ones.
#[allow(clippy::too_many_lines)]
pub(super) fn verify_negated_obligation_slice(
    encoder: &mut AYEncoder,
    negated_ensure: Term,
    ctx: &ObligationSliceContext<'_>,
    alias_mode: AliasConstraintMode,
    obligation_index: usize,
) -> Result<ResolveContinuation, EncodingError> {
    // Steps 1-5: Build the slice-local base context once in the caller-owned
    // scope so it can be rechecked without replaying the full setup.
    encoder.with_assertion_phase(
        AssertionPhase::AliasConstraint,
        |encoder| match alias_mode {
            AliasConstraintMode::ByValue => {
                super::function::assert_by_value_alias_constraints(encoder)
            }
            AliasConstraintMode::CurrentChain => {
                super::shared_constraints::assert_current_chain_alias_constraints(encoder)
            }
        },
    )?;

    let initial_post_div_obligations = encoder.take_division_obligations();
    if let Some(result) = try_prove_literal_false_negated_goal_with_solver_evidence(
        encoder,
        negated_ensure,
        ctx.body_div_obligations,
        &initial_post_div_obligations,
        obligation_index,
    )? {
        return Ok(result);
    }

    // Two-phase axiom solving (#2116): many slices are already UNSAT from
    // alias constraints + the negated goal alone. Prove those before asserting
    // the quantified axiom pile that can otherwise turn a simple obligation
    // into Unknown(Incomplete). This is especially helpful for mut-borrow
    // whole-identity checks once the raw current/final/id constraints are
    // already sufficient. (#2141, #2517)
    //
    // The probe also captures SAT results (counterexamples). When the axiom-free
    // probe finds SAT but the full axiom path returns Incomplete, the axiom-free
    // counterexample is used as a fallback because Failed is safe — it is never
    // a soundness bug (worst case: false positive / false alarm). (#2141)
    //
    // Compute body_assumptions once and reuse for both the Inconclusive
    // probe branch and the full axiom path. Previously computed twice:
    // once in the Inconclusive branch (for closure demand detection) and
    // again after the probe exits (for assert_standard_axioms). Each call
    // traverses the full return expression tree. (#2674)
    let body_assumptions: Vec<&PureExpr> = ctx
        .return_expr
        .map(collect_body_let_assume_assumptions)
        .unwrap_or_default();

    if let Some(result) = iterator_produces_singleton_failure_result(ctx, obligation_index) {
        return Ok(ResolveContinuation::Continue(result));
    }

    assert_direct_arithmetic_consequences(encoder, ctx, obligation_index)?;
    if let Some(result) = closure_bridge_precheck_result(ctx, obligation_index) {
        return Ok(ResolveContinuation::Continue(result));
    }

    let mut axiom_free_counterexample: Option<Counterexample> = None;
    macro_rules! pop_or_abort_type_invariant {
        ($label:literal) => {
            if let Some(result) = pop_scope_or_abort_failed_for_type_invariant_underflow(
                encoder,
                ctx,
                obligation_index,
                $label,
            )? {
                return Ok(result);
            }
        };
    }
    if should_skip_axiom_free_probe_for_seq_ext_eq_index(ctx)
        || should_skip_axiom_free_probe_for_recursive_logic(ctx)
    {
        debug!(
            "[TRUST_WP_DEBUG] skipping direct axiom-free probe on slice {obligation_index}: \
             obligation requires an axiom family whose incomplete probe can enter a \
             non-interruptible solver path"
        );
    } else {
        // Take a single ground pool snapshot before the axiom-free probe that is
        // reused for the full solve path. Previously, `ground_pool_snapshot()` was
        // called twice (once for the probe, once for the full solve), each cloning
        // the entire pool. Since the axiom-free probe runs inside push/pop and
        // restores the pool on exit, the pre-probe snapshot is valid for both. (#2674)
        let ground_pool_baseline = encoder.ground_pool_snapshot();
        encoder.push_scope()?;
        // Use AssertionPhase::Other (unnamed assertions) for the axiom-free
        // probe. ay-dpll's `try_assert_named` (used by NegatedPostcondition
        // phase for unsat core tracking) breaks Bool-sorted SAT model generation,
        // causing false Unknown(Incomplete) on negative tests. The base re-check
        // after pop_scope provides the vacuity guard. The full axiom path
        // (Phase 2) still uses NegatedPostcondition with named assertions. (#2141)
        let axiom_free_outcome = {
            encoder.with_assertion_phase(AssertionPhase::Other, |encoder| {
                assert_negated_goal_with_div_obligations(
                    encoder,
                    negated_ensure,
                    ctx.body_div_obligations,
                    &initial_post_div_obligations,
                );
                encoder.assert_seq_ground_instances(
                    crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                );
                // Materialize the FSet ground families AFTER the negated goal so
                // they see the goal's Skolem elements (e.g. bug/vcgen set_max's
                // `sk_o` in `contains(s, sk_o)`). This lets the axiom-free probe
                // prove obligations whose closure needs the remove-contains-frame
                // link plus the recursion IH — a fully-ground refutation ay-dpll
                // solves instantly — WITHOUT asserting the quantified FSet axiom
                // pile that otherwise tips the solve into quantifier-unhandled.
                // The instances are sound (true instances of the asserted FSet
                // universals and of the positive-polarity requires IH). (#vcgen)
                // Opt-in (default OFF), paired with the FSet frame ground family:
                // materialize the FSet ground families + the recursion-IH ground
                // instance in the axiom-free probe (after the negated goal, so
                // they see the goal Skolems). This reduces set_max-style
                // obligations to a fully-ground refutation, but the pinned ay-core
                // LRA (leg-C "simplex=Sat but unsupported") returns Unknown on the
                // resulting UF-valued arithmetic, so it cannot yet close. Kept
                // behind the same flag as the frame family, zero default behavior
                // change. (#vcgen)
                if std::env::var_os("TRUST_WP_ENABLE_FSET_FRAME_IH_GROUNDS").is_some() {
                    encoder.assert_fset_ground_instances(
                        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                    );
                    encoder.assert_goal_skolem_guarded_requires_forall_instances(
                        ctx.requires,
                        ctx.all_ensures,
                    );
                }
            });
            axiom_free_solve_with_sat(encoder)
        };
        match axiom_free_outcome {
            AxiomFreeOutcome::Unsat => {
                // Establish proof authority before pop_scope invalidates solver
                // state. (#2629) `extract_proof_summary` alone cannot do it:
                // the long-lived incremental encoder runs with
                // `set_produce_proofs(false)` by design, so an incremental
                // UNSAT carries no artifact and this arm shipped a
                // certificate-free `Verified(None)` that the mandatory
                // authority boundary demoted to `Unknown(ProofTrusted)`.
                // `accepted_unsat_proof_authority` keeps a retained artifact
                // when there is one and otherwise attaches the isolated strict
                // replay the encoder constructor's comment names — the same
                // helper the loop lane uses. Fail-closed: a declined replay
                // leaves `None`, exactly the previous behaviour.
                let proof_summary = accepted_unsat_proof_authority(encoder);
                let mut core_verified = VerificationResult::Verified(proof_summary);
                record_preferred_verified_solve_evidence(encoder, &mut core_verified);
                pop_or_abort_type_invariant!("axiom-free unsat probe");
                encoder.restore_ground_pool(ground_pool_baseline);
                // The axiom-free probe uses AssertionPhase::Other (no label
                // prefix), so vacuity always reads as non-vacuous (Verified).
                // The base re-solve is the vacuity guard: SAT base → vacuous,
                // UNSAT base → confirmed, Unknown base → visible gap.
                let allow_abort_rescue = base_recheck_long_budget(encoder);
                let base_result = ctx.base_recheck_for_slice(encoder);
                let base_result =
                    prefer_non_vacuous_core_on_incomplete_base(core_verified.clone(), base_result);
                return Ok(prefer_non_vacuous_core_on_fresh_base_recheck(
                    core_verified,
                    base_result,
                    ctx.fresh_base_recheck,
                    allow_abort_rescue,
                ));
            }
            AxiomFreeOutcome::Sat(counterexample) => {
                if let Err(error) = pop_scope_catching_ay_panic(encoder) {
                    if is_incremental_pop_underflow_error(&error) {
                        debug!(
                            "[TRUST_WP_DEBUG] axiom-free SAT rescue on slice {obligation_index}: \
                             ay pop-underflow while leaving probe scope; aborting without \
                             further cleanup pops"
                        );
                        return Ok(ResolveContinuation::Abort(VerificationResult::Failed(
                            counterexample,
                        )));
                    }
                    return Err(error);
                }
                encoder.restore_ground_pool(ground_pool_baseline.clone());
                axiom_free_counterexample = Some(counterexample);
            }
            AxiomFreeOutcome::Inconclusive => {
                // Extended axiom-free probe (#2692): when the short 500ms probe
                // is inconclusive, check whether any axiom families actually have
                // demand. If no standard axiom families and no closure axioms are
                // needed, the obligation is likely pure arithmetic that just needs
                // more solver time rather than axioms. Run an extended probe (5s)
                // before falling through to the axiom path. This prevents
                // unnecessary quantified axiom injection that pushes decidable
                // QF_LIA obligations into undecidable AUFLIA, causing
                // Unknown(Incomplete) on pure arithmetic like inc_max_3.
                //
                // Context-aware closure demand (#2668): closure postcondition UF
                // symbols may be declared (from the closure's own ensures contract)
                // without any ground postcondition calls in the verification
                // context. In that case, the closure axioms are dead weight.
                // Check for actual ground postcondition calls in requires and
                // body_assumptions before treating closure flags as demand.
                let demand = encoder.standard_axiom_demand();
                let flags = encoder.closure_postcondition_flags();
                // Use the consolidated scan_postcondition_context instead of
                // individual body_has_any_closure_postcondition calls. This
                // reuses the pre-computed body_assumptions (avoiding a second
                // expression-tree traversal) and consolidates the 3 separate
                // any/mut/once checks into a single pass. (#2674)
                let ctx_flags =
                    AYEncoder::scan_postcondition_context(ctx.requires, &body_assumptions);
                let has_closure_postcondition_in_context = ctx_flags.has_any;
                let closure_has_demand = has_closure_postcondition_in_context
                    && (flags.has_once || flags.has_mut || flags.has_fn);
                let no_axiom_demand = demand.is_empty() && !closure_has_demand;
                let type_invariant_obligation = is_type_invariant_obligation(ctx, obligation_index);
                if no_axiom_demand || type_invariant_obligation {
                    // No axiom families need assertion. Re-solve with extended
                    // timeout inside the same scope (solver state preserved).
                    if type_invariant_obligation && !no_axiom_demand {
                        debug!(
                            "[TRUST_WP_DEBUG] extended axiom-free probe on type-invariant \
                             obligation slice {obligation_index} before quantified axioms"
                        );
                    }
                    let extended_outcome = axiom_free_solve_with_sat_extended(encoder);
                    match extended_outcome {
                        AxiomFreeOutcome::Unsat => {
                            // Same authority attachment as the ordinary
                            // axiom-free UNSAT arm above, before pop_scope.
                            let proof_summary = accepted_unsat_proof_authority(encoder);
                            let mut core_verified = VerificationResult::Verified(proof_summary);
                            record_preferred_verified_solve_evidence(encoder, &mut core_verified);
                            pop_or_abort_type_invariant!("extended axiom-free unsat probe");
                            encoder.restore_ground_pool(ground_pool_baseline);
                            let allow_abort_rescue = base_recheck_long_budget(encoder);
                            let base_result = ctx.base_recheck_for_slice(encoder);
                            let base_result = prefer_non_vacuous_core_on_incomplete_base(
                                core_verified.clone(),
                                base_result,
                            );
                            return Ok(prefer_non_vacuous_core_on_fresh_base_recheck(
                                core_verified,
                                base_result,
                                ctx.fresh_base_recheck,
                                allow_abort_rescue,
                            ));
                        }
                        AxiomFreeOutcome::Sat(counterexample) => {
                            if let Err(error) = pop_scope_catching_ay_panic(encoder) {
                                if is_incremental_pop_underflow_error(&error) {
                                    debug!(
                                        "[TRUST_WP_DEBUG] axiom-free SAT rescue on slice \
                                         {obligation_index}: ay pop-underflow while leaving \
                                         extended probe scope; aborting without further cleanup pops"
                                    );
                                    return Ok(ResolveContinuation::Abort(
                                        VerificationResult::Failed(counterexample),
                                    ));
                                }
                                return Err(error);
                            }
                            encoder.restore_ground_pool(ground_pool_baseline.clone());
                            axiom_free_counterexample = Some(counterexample);
                        }
                        AxiomFreeOutcome::Inconclusive => {
                            pop_or_abort_type_invariant!("extended axiom-free inconclusive probe");
                            encoder.restore_ground_pool(ground_pool_baseline.clone());
                        }
                    }
                } else {
                    pop_or_abort_type_invariant!("axiom-free inconclusive probe");
                    encoder.restore_ground_pool(ground_pool_baseline.clone());
                }
            }
        }
    }

    // body_assumptions was computed once before the probe and is reused here.

    // Capture the pre-axiom ground pool state for the post-axiom fallback (#2692).
    // When axioms push a decidable QF_LIA problem into undecidable AUFLIA, the
    // fallback needs to restore to the pre-axiom state where no quantified
    // formulas exist in the solver context. The axioms and negated goal are
    // wrapped in a single scope that can be popped entirely for a clean
    // axiom-free retry; asserting the axioms directly in the outer scope would
    // leave them visible to the fallback solver after `pop_scope` on the
    // negated-goal scope.
    let pre_axiom_ground_pool = encoder.ground_pool_snapshot();

    // Whether the full solve genuinely demanded quantified standard axioms
    // (FSet/FMap/Option/tuple/… families). When it did, the axiom-free probe's
    // SAT model was computed with those demanded axioms DROPPED, so it can be a
    // fabricated counterexample (a model the axioms would have refuted). The
    // #2141 rescue below must NOT report such a model as a Failed/counterexample
    // verdict; it fails closed to Unknown instead. Captured here, before the
    // axioms are asserted, so it reflects the demand that drove them. (#vcgen)
    let had_standard_axiom_demand = !encoder.standard_axiom_demand().is_empty();

    // Push an axiom scope that contains BOTH the standard axiom assertions
    // AND the nested negated-goal scope. When the post-axiom fallback triggers,
    // we pop this entire scope to remove quantified axioms from the solver
    // context before retrying. This is critical for sorting networks like
    // inc_max_3 where trusted function declarations (e.g., `swap`) create
    // axiom demand that pushes the solver from QF_LIA into AUFLIA, causing
    // Unknown(Incomplete). (#2692)
    encoder.push_scope()?;
    let assertions_before_axiom_scope = encoder.solver().assertions().len();

    // Collect function symbols from the obligation for axiom relevance
    // filtering (#2674).
    let relevance_symbols =
        collect_obligation_function_symbols(ctx.all_ensures, ctx.requires, ctx.return_expr);
    encoder.set_ground_pool_relevance_filter(Some(relevance_symbols));

    let axiom_setup_result = (|| -> Result<(), EncodingError> {
        encoder.with_assertion_phase(AssertionPhase::EncodingAxiom, |encoder| {
            assert_standard_axioms(encoder, ctx.requires, &body_assumptions)
        })?;

        encoder.with_assertion_phase(AssertionPhase::GroundInstance, |encoder| {
            if let Some(fns) = ctx.logic_fns {
                let mut goal_exprs: Vec<&PureExpr> = Vec::new();
                for e in ctx.all_ensures {
                    goal_exprs.push(e);
                }
                for e in ctx.requires {
                    goal_exprs.push(e);
                }
                if let Some(body) = ctx.return_expr {
                    goal_exprs.push(body);
                }
                encoder.assert_recursive_logic_fn_ground_instances(
                    fns,
                    ctx.mode_overrides,
                    &goal_exprs,
                    5,
                )?;
            }

            // Mark contract-referenced logic function symbols as critical
            // before the ground pool flush. This ensures their axioms bypass the
            // parameter complexity gate and receive highest priority in the global
            // instantiation budget. Without this, logic functions with >4 params
            // or low priority would have ground instances dropped, causing solver
            // Unknown results on postconditions that reference them. (#1296)
            //
            // Both ensures AND requires clauses are marked: logic functions in
            // requires establish precondition facts that constrain the proof. If
            // a requires-clause logic function has >4 parameters and is not marked
            // critical, its ground instances are dropped by the parameter gate,
            // preventing the solver from establishing the precondition fact and
            // causing spurious Unknown results. (#1296)
            encoder.mark_postcondition_logic_fn_symbols(ctx.all_ensures);
            encoder.mark_postcondition_logic_fn_symbols(ctx.requires);

            encoder.maybe_assert_logic_ground_instances()?;
            Ok(())
        })?;

        Ok(())
    })();
    encoder.clear_ground_pool_relevance_filter();
    axiom_setup_result?;
    let axiom_scope_is_nonempty =
        encoder.solver().assertions().len() > assertions_before_axiom_scope;

    // Step 6: Solve the negated goal inside a nested scope so the slice-local
    // base context remains available for an explicit vacuity recheck. (#2414)
    // The axiom scope above contains the quantified axioms; the negated-goal
    // scope is nested inside it. When we need a post-axiom fallback, we pop
    // both scopes to return to the pre-axiom state. (#2692)
    let ground_pool_snapshot = encoder.ground_pool_snapshot();
    encoder.push_scope()?;
    let goal_label_prefix = format!("__trust_wp_negated_goal_slice_{obligation_index}");
    // Run vacuity check inside the label-prefix closure so the negated-goal
    // label is still set when is_vacuous_unsat() reads the unsat core. (#2520)
    let (inner_result, needs_base_recheck) =
        encoder.with_negated_goal_label_prefix(goal_label_prefix, |encoder| {
            encoder.with_assertion_phase(
                AssertionPhase::NegatedPostcondition,
                |encoder| -> Result<(), EncodingError> {
                    // Eager negated-existential instantiations are logical
                    // consequences of the negated goal, not the slice base.
                    // Keeping them in the nested negated-goal scope avoids
                    // vacuous base UNSAT when the eager witness directly
                    // contradicts the positive precondition facts. (#2556)
                    assert_eager_negated_existential_instantiations(
                        encoder,
                        ctx.all_ensures,
                        ctx.requires,
                        &body_assumptions,
                    )?;

                    let extra_post_div_obligations = encoder.take_division_obligations();
                    let mut all_post_div_obligations = Vec::with_capacity(
                        initial_post_div_obligations.len() + extra_post_div_obligations.len(),
                    );
                    all_post_div_obligations.extend(initial_post_div_obligations.iter().copied());
                    all_post_div_obligations.extend(extra_post_div_obligations);
                    assert_negated_goal_with_div_obligations(
                        encoder,
                        negated_ensure,
                        ctx.body_div_obligations,
                        &all_post_div_obligations,
                    );
                    // The negated goal can introduce fresh observed Seq index
                    // terms, including Skolem witnesses. Assert finite Seq
                    // ground facts after the goal is present so scoped solves
                    // do not depend on global quantified Seq axioms.
                    encoder.with_assertion_phase(AssertionPhase::GroundInstance, |encoder| {
                        encoder.assert_seq_ground_instances(
                            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                        );
                        // Re-materialize the predicate-closure defining axiom at
                        // the obligation's observed keys, including any that
                        // appear only in the just-asserted negated goal (e.g.
                        // cell/01_basic's `mapping_get(c@, v + 2)`). This must run
                        // HERE — before the batch precheck below fresh-parses the
                        // stack — because the precheck bypasses `check_sat`'s own
                        // ground-instance flush; without these instances the
                        // precheck's fresh solve has nothing but the closure
                        // universal to instantiate (which ay's single-round
                        // E-matching cannot) and times out, leaving the
                        // otherwise-provable obligation quantifier-unhandled.
                        // Sound: each instance is entailed by the asserted
                        // universal (see `assert_mapping_closure_get_instances`).
                        encoder.assert_mapping_closure_get_instances(
                            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                        );
                        Ok(())
                    })?;
                    Ok(())
                },
            )?;

            // Obligation-level batch precheck (#transpose): the incremental
            // tiered solve runs a quantified-disjoint recheck LOOP (~7 rounds ×
            // the tier ladder) that, on slices like transpose's Ok-Some/Ok-None,
            // churns for minutes and is then KILLED by the hard-timeout before
            // any post-solve recovery can run — even though a standalone batch
            // solve of the IDENTICAL stack closes them in well under a second.
            // Re-solve the full negated-goal+axiom stack ONCE on a fresh
            // non-incremental solver BEFORE the tier ladder; if it is UNSAT,
            // route straight to the base-recheck vacuity guard (needs_base_recheck
            // = true) and skip the churn entirely. SOUND: identical closed query,
            // accept only UNSAT; the base recheck below rejects a vacuous base.
            if !in_proof_assert_mode() {
                if let Some(summary) = encoder.batch_resolve_current_stack_unsat() {
                    debug!(
                        "[TRUST_WP_DEBUG] obligation-level batch precheck proved slice \
                         {obligation_index} UNSAT before the tier ladder (#transpose)"
                    );
                    return Ok((
                        ResolveContinuation::Continue(VerificationResult::Verified(Some(summary))),
                        true,
                    ));
                }
            }

            Ok(
                match run_with_hard_timeout(encoder, resolve_sat_result_without_vacuity) {
                    ResolveContinuation::Continue(VerificationResult::Verified(_)) => (
                        ResolveContinuation::Continue(resolve_last_unsat_with_vacuity(encoder)),
                        true,
                    ),
                    other => (other, false),
                },
            )
        })?;

    if needs_base_recheck {
        let ResolveContinuation::Continue(mut core_result) = inner_result else {
            unreachable!("needs_base_recheck is only set with Continue");
        };
        record_preferred_verified_solve_evidence(encoder, &mut core_result);
        // Pop negated-goal scope.
        pop_or_abort_type_invariant!("negated-goal verified scope");
        encoder.restore_ground_pool(ground_pool_snapshot);
        // Axiom-preserving vacuity refutation (vacuity shield for axioms): the
        // ordinary base recheck below pops the axiom scope, and the fresh
        // rescue rebuilds without it, so a base that is only contradictory
        // TOGETHER WITH the encoder axioms reads as non-vacuous. While the
        // axiom scope is still live (goal scope already popped, so the stack is
        // exactly base ∧ axioms), solve it once on a fresh solver. UNSAT means
        // the proof is vacuous: demote, bypassing the rescue. Refusal-only: a
        // SAT/unknown/timeout result changes nothing below.
        if core_result_is_verified(&core_result) && axiom_scope_is_nonempty {
            let timeout = encoder
                .solver()
                .timeout()
                .map_or(AXIOM_BASE_REFUTATION_TIMEOUT_CAP, |caller| {
                    (caller / 4).min(AXIOM_BASE_REFUTATION_TIMEOUT_CAP)
                });
            if encoder.live_stack_refuted_by_fresh_replay(timeout) == Some(true) {
                debug!(
                    "[TRUST_WP_DEBUG] slice {obligation_index}: base with encoder axiom scope is \
                     UNSAT on a fresh solver; demoting vacuous proof"
                );
                pop_or_abort_type_invariant!("axiom vacuous-with-axioms scope");
                encoder.restore_ground_pool(pre_axiom_ground_pool.clone());
                return Ok(ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(VACUOUS_WITH_ENCODER_AXIOMS_MESSAGE.to_string()),
                )));
            }
        }
        // Pop axiom scope — base recheck should see the pre-axiom base context
        // for a clean vacuity assessment. The axioms are not needed for the base
        // recheck (which only tests whether preconditions are consistent). (#2692)
        pop_or_abort_type_invariant!("axiom verified scope");
        encoder.restore_ground_pool(pre_axiom_ground_pool.clone());
        let allow_abort_rescue = base_recheck_long_budget(encoder);
        let base_result = ctx.base_recheck_for_slice(encoder);
        let base_result =
            prefer_non_vacuous_core_on_incomplete_base(core_result.clone(), base_result);
        return Ok(prefer_non_vacuous_core_on_fresh_base_recheck(
            core_result,
            base_result,
            ctx.fresh_base_recheck,
            allow_abort_rescue,
        ));
    }

    match inner_result {
        // Axiom-free SAT rescue (#2141): when the axiom-free probe found a
        // counterexample (SAT) but quantified axioms made the full solve
        // Incomplete, use the axiom-free counterexample. Failed is safe —
        // the worst case is a false positive, never a soundness bug.
        ResolveContinuation::Continue(VerificationResult::Unknown(ref reason))
            if axiom_free_counterexample.is_some() && should_rescue_with_axiom_free_sat(reason) =>
        {
            // Pop negated-goal scope + axiom scope (identical cleanup on both
            // the rescue and the verdict-hygiene fail-closed path).
            pop_or_abort_type_invariant!("negated-goal axiom-free SAT rescue scope");
            encoder.restore_ground_pool(ground_pool_snapshot);
            pop_or_abort_type_invariant!("axiom axiom-free SAT rescue scope");
            encoder.restore_ground_pool(pre_axiom_ground_pool);
            if had_standard_axiom_demand {
                // Verdict hygiene (#vcgen): the axiom-free SAT model was found
                // with the demanded quantified axioms DROPPED, so it may be a
                // fabricated counterexample — a model those axioms would have
                // refuted (e.g. bug/vcgen set_max, where dropping the FSet frame
                // axioms + recursion IH admits a spurious `sk_o` witness). Fail
                // closed to Unknown rather than report a Failed/counterexample
                // verdict of a misleading class. Sound: this only ever REMOVES a
                // rejection, never adds an acceptance, so the 0-false-accept lane
                // is unaffected.
                debug!(
                    "[TRUST_WP_DEBUG] axiom-free SAT on slice {obligation_index} withheld \
                         (standard axiom demand was nonempty): surfacing Unknown({reason}) \
                         instead of a counterexample fabricated by dropping demanded axioms"
                );
                Ok(ResolveContinuation::Continue(VerificationResult::Unknown(
                    reason.clone(),
                )))
            } else {
                debug!(
                    "[TRUST_WP_DEBUG] axiom-free SAT rescue on slice {obligation_index}: \
                         full axiom solve returned Unknown({reason})"
                );
                Ok(ResolveContinuation::Continue(VerificationResult::Failed(
                    axiom_free_counterexample.unwrap(),
                )))
            }
        }
        // ay can corrupt its incremental theory scope stack while reporting
        // a pop-underflow from the full axiom solve. The pre-axiom SAT model is
        // still a conservative rejection, but touching the restored solver for
        // cleanup pops can hit the same underflow again. Abort tells the caller
        // to return immediately without using this encoder further.
        ResolveContinuation::Continue(VerificationResult::Unknown(ref reason))
            if axiom_free_counterexample.is_some()
                && should_abort_with_axiom_free_sat_after_solver_panic(reason) =>
        {
            debug!(
                "[TRUST_WP_DEBUG] axiom-free SAT rescue on slice {obligation_index}: \
                     full axiom solve returned scope-corrupting solver panic {reason}; \
                     aborting without cleanup pops"
            );
            Ok(ResolveContinuation::Abort(VerificationResult::Failed(
                axiom_free_counterexample.unwrap(),
            )))
        }
        ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::Timeout))
            if is_type_invariant_obligation(ctx, obligation_index) =>
        {
            debug!(
                "[TRUST_WP_DEBUG] type-invariant obligation slice {obligation_index} \
                 timed out; classifying conservatively as Failed"
            );
            pop_or_abort_type_invariant!("negated-goal type-invariant timeout scope");
            encoder.restore_ground_pool(ground_pool_snapshot);
            pop_or_abort_type_invariant!("axiom type-invariant timeout scope");
            encoder.restore_ground_pool(pre_axiom_ground_pool);
            Ok(ResolveContinuation::Continue(
                crate::verify::structural_failed_traced(),
            ))
        }
        ResolveContinuation::Continue(VerificationResult::Unknown(ref reason))
            if has_validated_closure_unknown_counterexample(
                encoder,
                reason,
                ctx,
                &body_assumptions,
            ) =>
        {
            debug!(
                "[TRUST_WP_DEBUG] closure solve returned Unknown({reason}) with an accepted \
                 validated model; classifying negated-goal query as a counterexample"
            );
            let model = encoder.get_model();
            let result =
                VerificationResult::Failed(Counterexample::from_encoder_model(encoder, model));
            pop_or_abort_type_invariant!("negated-goal validated closure counterexample scope");
            encoder.restore_ground_pool(ground_pool_snapshot);
            pop_or_abort_type_invariant!("axiom validated closure counterexample scope");
            encoder.restore_ground_pool(pre_axiom_ground_pool);
            Ok(ResolveContinuation::Continue(result))
        }
        // Post-axiom axiom-free fallback (#2692): when the full axiom solve
        // returned Unknown(Incomplete) and the initial axiom-free probe was
        // Inconclusive (not SAT — no counterexample), the axioms may have
        // pushed a decidable QF_LIA problem into undecidable AUFLIA. This
        // happens for sorting networks (inc_max_3) where trusted function
        // declarations cause axiom demand but the actual VC is pure arithmetic.
        //
        // Pop both the negated-goal scope AND the axiom scope, then retry
        // with only the negated goal in a fresh scope. This ensures the
        // solver does not see any quantified axiom formulas, keeping the
        // problem in the decidable QF_LIA/QF_AUFLIA fragment. Previously,
        // only the negated-goal scope was popped, leaving quantified axioms
        // visible and causing the solver to immediately return Incomplete.
        //
        // This is sound: UNSAT from declarations + negated goal alone is a
        // valid proof. The base re-solve provides the vacuity guard.
        ResolveContinuation::Continue(VerificationResult::Unknown(ref reason))
            if axiom_free_counterexample.is_none()
                && should_retry_without_axioms_after_unknown(reason) =>
        {
            // Pop negated-goal scope.
            pop_or_abort_type_invariant!("negated-goal post-axiom fallback scope");
            encoder.restore_ground_pool(ground_pool_snapshot);
            // Pop axiom scope to remove quantified formulas from context.
            pop_or_abort_type_invariant!("axiom post-axiom fallback scope");
            encoder.restore_ground_pool(pre_axiom_ground_pool.clone());

            debug!(
                "[TRUST_WP_DEBUG] post-axiom axiom-free fallback on slice {obligation_index}: \
                     full axiom solve returned Unknown({reason}), retrying without axioms (#2692)"
            );

            // Re-enter a fresh scope and re-assert only the negated goal
            // (without axioms). The pre-axiom base context (preconditions,
            // body constraints, alias constraints) is the outer scope
            // with no quantified formulas. This keeps the solver in a
            // decidable fragment (QF_LIA or QF_AUFLIA). (#2692)
            encoder.push_scope()?;
            encoder.with_assertion_phase(AssertionPhase::Other, |encoder| {
                assert_negated_goal_with_div_obligations(
                    encoder,
                    negated_ensure,
                    ctx.body_div_obligations,
                    &initial_post_div_obligations,
                );
            });

            // Run the final clean axiom-free retry behind the same hard-timeout
            // envelope as the primary solve. This path still uses tiered_check_sat
            // through resolve_sat_result_without_vacuity, but the outer worker
            // envelope is required because some AUFLIA/array paths can ignore
            // the solver timeout and otherwise overrun the caller's watchdog.
            // (#2692, #2747)
            let fallback_result =
                run_with_hard_timeout(encoder, resolve_sat_result_without_vacuity);
            match fallback_result {
                ResolveContinuation::Continue(VerificationResult::Verified(proof_summary)) => {
                    let mut core_verified = VerificationResult::Verified(proof_summary);
                    record_preferred_verified_solve_evidence(encoder, &mut core_verified);
                    pop_or_abort_type_invariant!("clean axiom-free fallback unsat scope");
                    let allow_abort_rescue = base_recheck_long_budget(encoder);
                    let base_result = ctx.base_recheck_for_slice(encoder);
                    let base_result = prefer_non_vacuous_core_on_incomplete_base(
                        core_verified.clone(),
                        base_result,
                    );
                    Ok(prefer_non_vacuous_core_on_fresh_base_recheck(
                        core_verified,
                        base_result,
                        ctx.fresh_base_recheck,
                        allow_abort_rescue,
                    ))
                }
                ResolveContinuation::Continue(VerificationResult::Failed(counterexample)) => {
                    // The axiom-free full solve found SAT — use it as a
                    // safe fallback (Failed is never a soundness bug).
                    pop_or_abort_type_invariant!("clean axiom-free fallback sat scope");
                    Ok(ResolveContinuation::Continue(VerificationResult::Failed(
                        counterexample,
                    )))
                }
                ResolveContinuation::Continue(VerificationResult::Unknown(fallback_reason)) => {
                    // Full solve also inconclusive — the problem genuinely
                    // needs axioms or more time. Report the clean fallback's
                    // own reason when available; it is the last solve and
                    // better identifies whether the residual is still
                    // quantifier-driven or is an axiom-free theory limitation.
                    let fallback_unknown = prefer_specific_fallback_unknown(
                        reason,
                        VerificationResult::Unknown(fallback_reason),
                    );
                    pop_or_abort_type_invariant!("clean axiom-free fallback unknown scope");
                    if matches!(
                        fallback_unknown,
                        VerificationResult::Unknown(UnknownReason::Timeout)
                    ) && is_type_invariant_obligation(ctx, obligation_index)
                    {
                        debug!(
                            "[TRUST_WP_DEBUG] clean axiom-free retry for type-invariant \
                             obligation slice {obligation_index} timed out; \
                             classifying conservatively as Failed"
                        );
                        Ok(ResolveContinuation::Continue(
                            crate::verify::structural_failed_traced(),
                        ))
                    } else {
                        Ok(ResolveContinuation::Continue(fallback_unknown))
                    }
                }
                ResolveContinuation::Continue(result) => {
                    pop_or_abort_type_invariant!("clean axiom-free fallback final scope");
                    Ok(ResolveContinuation::Continue(result))
                }
                ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
                    if is_type_invariant_obligation(ctx, obligation_index) =>
                {
                    debug!(
                        "[TRUST_WP_DEBUG] clean axiom-free retry for type-invariant \
                         obligation slice {obligation_index} hard-timed out; \
                         classifying conservatively as Failed"
                    );
                    Ok(ResolveContinuation::Abort(
                        crate::verify::structural_failed_traced(),
                    ))
                }
                ResolveContinuation::Abort(result) => Ok(ResolveContinuation::Abort(result)),
            }
        }
        ResolveContinuation::Continue(result) => {
            // Pop negated-goal scope + axiom scope.
            pop_or_abort_type_invariant!("negated-goal final cleanup scope");
            encoder.restore_ground_pool(ground_pool_snapshot);
            pop_or_abort_type_invariant!("axiom final cleanup scope");
            encoder.restore_ground_pool(pre_axiom_ground_pool);
            Ok(ResolveContinuation::Continue(result))
        }
        // Hard-timeout SAT rescue: if the full axiom solve exceeded the
        // outer hard-timeout but the pre-axiom probe already found a concrete
        // SAT counterexample, return that safe failure while preserving Abort
        // semantics. The live encoder was not restored after hard timeout, so
        // the caller must not pop scopes on the placeholder encoder.
        ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
            if axiom_free_counterexample.is_some() =>
        {
            if had_standard_axiom_demand {
                // Verdict hygiene (#vcgen): same fail-closed rule as the #2141
                // rescue above — the axiom-free SAT model was found with the
                // demanded quantified axioms dropped, so it may be a fabricated
                // counterexample. Surface Unknown, never a Failed verdict of a
                // misleading class. Sound: only removes a rejection, never adds
                // an acceptance.
                debug!(
                    "[TRUST_WP_DEBUG] axiom-free SAT on slice {obligation_index} withheld \
                         (standard axiom demand was nonempty): full axiom solve hard-timed out, \
                         surfacing Unknown instead of a fabricated counterexample"
                );
                Ok(ResolveContinuation::Abort(VerificationResult::Unknown(
                    UnknownReason::Timeout,
                )))
            } else {
                debug!(
                    "[TRUST_WP_DEBUG] axiom-free SAT rescue on slice {obligation_index}: \
                         full axiom solve hard-timed out"
                );
                Ok(ResolveContinuation::Abort(VerificationResult::Failed(
                    axiom_free_counterexample.unwrap(),
                )))
            }
        }
        ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
            if is_type_invariant_obligation(ctx, obligation_index) =>
        {
            debug!(
                "[TRUST_WP_DEBUG] type-invariant obligation slice {obligation_index} \
                 hard-timed out; classifying conservatively as Failed"
            );
            Ok(ResolveContinuation::Abort(
                crate::verify::structural_failed_traced(),
            ))
        }
        ResolveContinuation::Abort(result) => Ok(ResolveContinuation::Abort(result)),
    }
}

fn closure_bridge_precheck_result(
    ctx: &ObligationSliceContext<'_>,
    obligation_index: usize,
) -> Option<VerificationResult> {
    let ensure = ctx.all_ensures.get(obligation_index)?;
    if !closure_postcondition_mut_follows_from_context(ensure, ctx) {
        return None;
    }
    let fresh_base_recheck = ctx.fresh_base_recheck?;
    match fresh_base_recheck() {
        Ok(VerificationResult::Verified(_)) => {
            Some(prove_prechecked_literal_false_with_solver_evidence())
        }
        Ok(other) => Some(other),
        Err(_) => None,
    }
}

fn closure_postcondition_mut_follows_from_context(
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = ensure
    else {
        return false;
    };
    if method != "postcondition_mut" || args.len() < 2 {
        return false;
    }

    let receiver = closure_normalized_receiver(receiver);
    let result = args.last().expect("postcondition_mut args checked");
    let mut result_variants = vec![result.clone()];
    if matches!(result, PureExpr::Var(name, _) if name == "result") {
        if let Some(return_expr) = ctx.return_expr {
            result_variants.push(return_expr.clone());
        }
    }

    ctx.requires.iter().any(|require| {
        closure_requirement_contains_matching_postcondition(
            require,
            receiver,
            args,
            &result_variants,
            ctx,
        ) || closure_requirement_contains_matching_postcondition_mut(
            require,
            receiver,
            args,
            &result_variants,
            ctx,
        )
    })
}

fn closure_requirement_contains_matching_postcondition(
    require: &PureExpr,
    receiver: &PureExpr,
    mut_args: &[PureExpr],
    result_variants: &[PureExpr],
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    match require {
        PureExpr::MethodCall {
            receiver: req_receiver,
            method,
            args: req_args,
        } if method == "postcondition" => {
            if mut_args.len() < 2 || req_args.len() + 1 != mut_args.len() {
                return false;
            }
            let res_state = &mut_args[mut_args.len() - 2];
            if !same_pure_expr(res_state, receiver)
                && !closure_res_state_is_identity(receiver, res_state, ctx)
            {
                return false;
            }
            let req_receiver = closure_normalized_receiver(req_receiver);
            let mut post_args = mut_args[..mut_args.len() - 2].to_vec();
            result_variants.iter().any(|result| {
                post_args.truncate(mut_args.len() - 2);
                post_args.push(result.clone());
                closure_same_receiver(req_receiver, receiver)
                    && same_pure_exprs(req_args, &post_args)
            })
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            closure_requirement_contains_matching_postcondition(
                left,
                receiver,
                mut_args,
                result_variants,
                ctx,
            ) || closure_requirement_contains_matching_postcondition(
                right,
                receiver,
                mut_args,
                result_variants,
                ctx,
            )
        }
        _ => false,
    }
}

fn closure_requirement_contains_matching_postcondition_mut(
    require: &PureExpr,
    receiver: &PureExpr,
    expected_args: &[PureExpr],
    result_variants: &[PureExpr],
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    match require {
        PureExpr::MethodCall {
            receiver: req_receiver,
            method,
            args: req_args,
        } if method == "postcondition_mut" => {
            let req_receiver = closure_normalized_receiver(req_receiver);
            closure_same_receiver(req_receiver, receiver)
                && closure_fnmut_args_match(req_args, expected_args, result_variants, receiver, ctx)
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            closure_requirement_contains_matching_postcondition_mut(
                left,
                receiver,
                expected_args,
                result_variants,
                ctx,
            ) || closure_requirement_contains_matching_postcondition_mut(
                right,
                receiver,
                expected_args,
                result_variants,
                ctx,
            )
        }
        _ => false,
    }
}

fn closure_fnmut_args_match(
    actual: &[PureExpr],
    expected: &[PureExpr],
    result_variants: &[PureExpr],
    receiver: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    if actual.len() < 2 || actual.len() != expected.len() {
        return false;
    }
    let res_state_idx = actual.len() - 2;
    same_pure_exprs(&actual[..res_state_idx], &expected[..res_state_idx])
        && result_variants
            .iter()
            .any(|result| same_pure_expr(actual.last().unwrap(), result))
        && closure_res_states_match(
            &actual[res_state_idx],
            &expected[res_state_idx],
            receiver,
            ctx,
        )
}

fn closure_res_states_match(
    actual: &PureExpr,
    expected: &PureExpr,
    receiver: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    same_pure_expr(actual, expected)
        || (closure_res_state_is_identity(receiver, actual, ctx)
            && closure_res_state_is_identity(receiver, expected, ctx))
}

fn closure_res_state_is_identity(
    receiver: &PureExpr,
    res_state: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    let Some(final_values) = ctx.mut_borrow_final_values else {
        return false;
    };
    let final_base = match res_state {
        PureExpr::Final(inner) => closure_normalized_receiver(inner),
        PureExpr::Var(name, _) if name.contains("_final") => res_state,
        _ => return false,
    };
    let Some(name) = closure_receiver_name(final_base) else {
        return false;
    };
    let Some(value) = final_values
        .get(name)
        .or_else(|| final_values.get(closure_canonical_state_name(name)))
    else {
        return false;
    };
    closure_same_receiver(closure_normalized_receiver(value), receiver)
}

fn closure_normalized_receiver(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Deref(inner) => closure_normalized_receiver(inner),
        _ => expr,
    }
}

fn closure_same_receiver(left: &PureExpr, right: &PureExpr) -> bool {
    same_pure_expr(left, right)
}

fn closure_receiver_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => closure_receiver_name(inner),
        _ => None,
    }
}

fn closure_canonical_state_name(mut name: &str) -> &str {
    loop {
        if let Some(stripped) = name.strip_suffix("_current") {
            name = stripped;
            continue;
        }
        if let Some(stripped) = name.strip_suffix("_final") {
            name = stripped;
            continue;
        }
        return name;
    }
}

fn same_pure_exprs(left: &[PureExpr], right: &[PureExpr]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| same_pure_expr(left, right))
}

fn same_pure_expr(left: &PureExpr, right: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right)
}

fn is_type_invariant_obligation(ctx: &ObligationSliceContext<'_>, obligation_index: usize) -> bool {
    ctx.all_ensures.get(obligation_index).is_some_and(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { method, .. }
                if trust_wp_core::logic::is_invariant_method_name(method)
        )
    })
}

fn pop_scope_or_abort_failed_for_type_invariant_underflow(
    encoder: &mut AYEncoder,
    ctx: &ObligationSliceContext<'_>,
    obligation_index: usize,
    label: &str,
) -> Result<Option<ResolveContinuation>, EncodingError> {
    match pop_scope_catching_ay_panic(encoder) {
        Ok(()) => Ok(None),
        Err(error)
            if is_incremental_pop_underflow_error(&error)
                && is_type_invariant_obligation(ctx, obligation_index) =>
        {
            debug!(
                "[TRUST_WP_DEBUG] type-invariant obligation slice {obligation_index}: \
                 ay pop-underflow while leaving {label}; classifying conservatively \
                 as Failed and aborting without further cleanup pops"
            );
            Ok(Some(ResolveContinuation::Abort(
                crate::verify::structural_failed_traced(),
            )))
        }
        Err(error) => Err(error),
    }
}

fn pop_scope_catching_ay_panic(encoder: &mut AYEncoder) -> Result<(), EncodingError> {
    super::catch_ay_panics_tightened(AssertUnwindSafe(|| encoder.pop_scope()), |reason| {
        Err(EncodingError::solver_error(reason))
    })
}

fn collect_obligation_function_symbols(
    ensures: &[PureExpr],
    requires: &[PureExpr],
    return_expr: Option<&PureExpr>,
) -> HashSet<String> {
    let mut symbols = HashSet::new();
    let mut collector = |node: &PureExpr| {
        match node {
            PureExpr::LogicFnCall { name, .. } => {
                symbols.insert(trust_wp_core::logic::logic_fn_smt_name(name));
            }
            PureExpr::MethodCall { method, .. } => {
                // Method-style spec calls are registered in the ground pool under
                // their logic-function SMT symbol.
                symbols.insert(trust_wp_core::logic::logic_fn_smt_name(method));
            }
            _ => {}
        }
    };

    for expr in ensures {
        expr.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, &mut collector);
    }
    for expr in requires {
        expr.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, &mut collector);
    }
    if let Some(body) = return_expr {
        body.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, &mut collector);
    }

    symbols
}

fn assert_negated_goal_with_div_obligations(
    encoder: &mut AYEncoder,
    negated_ensure: Term,
    body_div_obligations: &[Term],
    post_div_obligations: &[Term],
) {
    encoder.with_goal_assertions(|encoder| {
        assert_negated_goal_with_div_obligations_inner(
            encoder,
            negated_ensure,
            body_div_obligations,
            post_div_obligations,
        );
    });
}

fn core_result_is_verified(result: &VerificationResult) -> bool {
    matches!(result, VerificationResult::Verified(_))
}

fn assert_negated_goal_with_div_obligations_inner(
    encoder: &mut AYEncoder,
    negated_ensure: Term,
    body_div_obligations: &[Term],
    post_div_obligations: &[Term],
) {
    let total_divs = body_div_obligations.len() + post_div_obligations.len();
    if total_divs == 0 {
        encoder.assert_term(negated_ensure);
        return;
    }

    let mut disjuncts = Vec::with_capacity(1 + total_divs);
    disjuncts.push(negated_ensure);
    for &obligation in body_div_obligations {
        disjuncts.push(encoder.solver_mut().not(obligation));
    }
    for &obligation in post_div_obligations {
        disjuncts.push(encoder.solver_mut().not(obligation));
    }
    let disjunction = encoder.solver_mut().or_many(&disjuncts);
    encoder.assert_term(disjunction);
}
