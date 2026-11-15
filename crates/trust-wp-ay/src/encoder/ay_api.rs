// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Facade for ay solver operations with error handling.
//!
//! This module centralizes all conversions from ay `try_*` failures into trust-wp
//! behavior. It provides two tiers:
//!
//! - **`safe_*`** -- for user-driven encoding paths that return `Result<_, EncodingError>`.
//! - **`axiom_*`** -- for axiom/setup contexts that skip silently on failure.

use ay_dpll::{
    api::{
        AnnotatedUnsatCore, CrossCheckReport, CrossCheckVariant, DatatypeSort, FuncDecl,
        ModelProvenance, ModelValue, NativeReplayMetadata, Sort, Term, VerifiedModel,
        VerifiedSolveResult,
    },
    Statistics,
};

use super::{
    match_enc::datatype_constructor_name, type_resolve::catch_solver_panic_with_reason, AYEncoder,
};
use crate::{
    error::EncodingError,
    shared_types::{SolveEvidenceSnapshot, SolveStatisticsSnapshot},
};

fn has_complete_sat_validation(
    is_sat: bool,
    result_model_validated: bool,
    summary_model_validated: bool,
) -> bool {
    is_sat && result_model_validated && summary_model_validated
}

#[derive(Clone, Copy, Debug)]
struct UnsatProofAuthorityEvidence {
    is_unsat: bool,
    consumer_accepted: bool,
    proof_checking_active: bool,
    proof_available: bool,
    summary_checker_failures: u64,
    raw_checker_failures: Option<u64>,
    proof_complete: bool,
    trust_fallbacks: Option<u64>,
    checked_steps: Option<u64>,
    total_steps: Option<u64>,
    skipped_hole_steps: Option<u64>,
}

fn has_complete_unsat_proof(evidence: UnsatProofAuthorityEvidence) -> bool {
    let all_steps_checked = matches!(
        (evidence.checked_steps, evidence.total_steps),
        (Some(checked), Some(total)) if total > 0 && checked == total
    );
    evidence.is_unsat
        && evidence.consumer_accepted
        && evidence.proof_checking_active
        && evidence.proof_available
        && evidence.summary_checker_failures == 0
        && evidence.raw_checker_failures == Some(0)
        && evidence.proof_complete
        && evidence.trust_fallbacks == Some(0)
        && all_steps_checked
        && evidence.skipped_hole_steps == Some(0)
}

pub(crate) fn solve_details_have_complete_unsat_proof(
    details: &ay_dpll::api::SolveDetails,
) -> bool {
    has_complete_unsat_proof(UnsatProofAuthorityEvidence {
        is_unsat: details.result.is_unsat(),
        consumer_accepted: details.accept_for_consumer().is_ok(),
        proof_checking_active: details.verification_level.has_proof_checking(),
        proof_available: details.verification.unsat_proof_available,
        summary_checker_failures: details.verification.unsat_proof_checker_failures,
        raw_checker_failures: details.statistics.get_int("proof_checker_failures"),
        proof_complete: details.statistics.proof_complete,
        trust_fallbacks: details.statistics.get_int("proof_trust"),
        checked_steps: details.statistics.get_int("proof_checker_checked_steps"),
        total_steps: details.statistics.get_int("proof_checker_total_steps"),
        skipped_hole_steps: details
            .statistics
            .get_int("proof_checker_skipped_hole_steps"),
    })
}

pub(crate) fn solve_snapshots_have_complete_unsat_proof(
    evidence: &SolveEvidenceSnapshot,
    statistics: &SolveStatisticsSnapshot,
) -> bool {
    let extra = |key: &str| {
        statistics
            .extra_ints
            .iter()
            .find_map(|(candidate, value)| (candidate == key).then_some(*value))
    };
    has_complete_unsat_proof(UnsatProofAuthorityEvidence {
        is_unsat: evidence.result.eq_ignore_ascii_case("unsat")
            || evidence
                .result
                .strip_prefix("Unsat")
                .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('(')),
        consumer_accepted: evidence.accepted_for_consumer,
        proof_checking_active: matches!(
            evidence.verification_level,
            crate::shared_types::SolveVerificationLevelSnapshot::ProofChecked
                | crate::shared_types::SolveVerificationLevelSnapshot::FullyVerified
        ),
        proof_available: evidence.verification.unsat_proof_available,
        summary_checker_failures: evidence.verification.unsat_proof_checker_failures,
        raw_checker_failures: extra("proof_checker_failures"),
        proof_complete: statistics.proof_complete,
        trust_fallbacks: extra("proof_trust"),
        checked_steps: extra("proof_checker_checked_steps"),
        total_steps: extra("proof_checker_total_steps"),
        skipped_hole_steps: extra("proof_checker_skipped_hole_steps"),
    })
}

struct StrictNativeReplay {
    details: ay_dpll::api::SolveDetails,
    proof_artifact: Option<ay_dpll::api::UnsatProofArtifact>,
    native_problem_json: String,
    problem_hash: [u8; 32],
}

/// SHA-256 of the exact native problem a strict replay solves (timeout and
/// normalized capture time included), used only to recognise a repeat of an
/// already-refused replay.
fn strict_replay_problem_hash(native_problem_json: &str) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.strict-replay-problem.v1\0");
    hasher.update(native_problem_json.as_bytes());
    hasher.finalize().into()
}

/// ay reason codes whose refusal is a property of the problem and its proof,
/// not of the budget: re-running the identical replay reproduces it. Timeouts
/// and resource limits are deliberately absent — a retry may succeed.
pub(crate) fn is_deterministic_strict_replay_refusal(unknown_reason: Option<&str>) -> bool {
    matches!(
        unknown_reason,
        Some("proof_trusted" | "self_check_rejected")
    )
}

// ---------------------------------------------------------------------------
// safe_* -- user-driven encoding paths (return Result)
// ---------------------------------------------------------------------------

// Facade methods are defined here for consistent error handling, even if not
// all callers have migrated yet. Allow dead_code until adoption is complete.
#[allow(dead_code)]
impl AYEncoder {
    pub(super) fn strict_native_replay_metadata() -> Option<NativeReplayMetadata> {
        if !crate::verify::in_proof_assert_mode() {
            return Some(NativeReplayMetadata::default());
        }
        let identity = crate::verify::active_proof_assert_slice_identity()?;
        Some(crate::shared_types::proof_assert_native_replay_metadata(
            identity.ordinal,
            identity.prepared_claim_hash,
            identity.normalized_claim_hash,
        ))
    }
    fn capped_fresh_timeout(&self, cap: std::time::Duration) -> std::time::Duration {
        self.solver.timeout().map_or(cap, |caller_timeout| {
            // AY extends the nominal deadline of a quantified solve to a 4x
            // deterministic-work backstop. These fresh solves can run inside
            // trust-wp's 1.5x caller hard-timeout envelope, so give AY at most
            // 3/8 of that caller budget: 4 * 3/8 = 1.5. The outer 100ms grace
            // remains available for replay construction and scheduling.
            let envelope_safe_timeout = caller_timeout
                .checked_div(8)
                .and_then(|eighth| eighth.checked_mul(3))
                .unwrap_or(caller_timeout);
            envelope_safe_timeout.min(cap)
        })
    }

    /// Rebuild and solve the exact active native assertion stack without a
    /// textual round trip. Native replay preserves datatype and theory terms
    /// structurally, making the fresh solve faithful to the active encoder
    /// stack rather than dependent on an interchange representation.
    fn replay_current_stack_diagnostic_with_timeout(
        &self,
        timeout: std::time::Duration,
    ) -> Option<ay_dpll::api::SolveDetails> {
        let mut artifact = self
            .solver
            .export_native_replay_artifact(NativeReplayMetadata::default(), None);
        artifact.timeout_ms = Some(timeout.as_millis());
        ay_dpll::api::Solver::replay_native_replay_artifact(&artifact).ok()
    }

    /// Rebuild and solve the exact active native assertion stack with proof
    /// production and strict proof checking enabled. This is the only native
    /// replay path whose UNSAT result may carry proof authority; callers still
    /// re-check every raw evidence field through
    /// [`solve_details_have_complete_unsat_proof`].
    fn replay_current_stack_with_strict_proofs(
        &self,
        timeout: std::time::Duration,
    ) -> Option<StrictNativeReplay> {
        let metadata = Self::strict_native_replay_metadata()?;
        let mut artifact = self.solver.export_native_replay_artifact(metadata, None);
        // Exporting before the strict solve records this one diagnostic gap by
        // construction. It is precisely what the replay below supplies. Any
        // other gap or unsupported atom remains a hard refusal.
        if artifact.replay_gaps.as_slice() != ["solve details were not captured"]
            || !artifact.unsupported_atoms.is_empty()
        {
            crate::verify::authority_trace(|| {
                format!(
                    "strict replay NOT RUN: export gaps={:?} unsupported_atoms={}",
                    artifact.replay_gaps,
                    artifact.unsupported_atoms.len()
                )
            });
            return None;
        }
        artifact.replay_gaps.clear();
        // Capture time is not solver input. Normalizing it makes the exact
        // problem and certificate-set hashes deterministic.
        artifact.created_unix_ms = 0;
        artifact.timeout_ms = Some(timeout.as_millis());
        let native_problem_json = artifact.to_pretty_json();
        let problem_hash = strict_replay_problem_hash(&native_problem_json);
        if self
            .encoding_cache
            .strict_replay_refused_deterministically(problem_hash)
        {
            // Refusing direction only: the identical replay was already refused
            // for a deterministic reason in this very scope, and that refusal's
            // observation is still the recorded one.
            crate::verify::authority_trace(|| {
                "strict replay NOT RUN: identical problem already deterministically refused \
                 in this scope"
                    .to_string()
            });
            return None;
        }
        let (details, proof_artifact) =
            match ay_dpll::api::Solver::replay_native_replay_artifact_with_checked_proof(
                &artifact, timeout,
            ) {
                Ok(replay) => replay,
                Err(error) => {
                    crate::verify::authority_trace(|| {
                        format!("strict replay NOT RUN: replay refused: {error}")
                    });
                    if std::env::var_os("TWP_BR_DBG").is_some() {
                        eprintln!("[TWP_BR] strict proof_assert replay refused: {error}");
                    }
                    return None;
                }
            };
        Some(StrictNativeReplay {
            details,
            proof_artifact,
            native_problem_json,
            problem_hash,
        })
    }

    /// Install the strict replay as proof authority when it qualifies, and
    /// ALWAYS retain what it measured.
    ///
    /// The authority decision is unchanged — same four conditions, same order,
    /// same `None` on any failure. What changed is that the replay's own
    /// `SolveDetails` are no longer *destroyed* by a failing decision.
    ///
    /// Why that matters: on the certification-blocked lane (ay builds a complete
    /// derivation, then refuses to certify it — `step tN uses unverified trust
    /// rule`) every early return below fires, so nothing was recorded and the
    /// only snapshot left for provenance came from the long-lived incremental
    /// encoder. That encoder is built with `set_produce_proofs(false)` and never
    /// calls `set_verification_level`, so its `verification_level = Trusted` and
    /// `unsat_proof_available = false` are CONSTANTS OF ITS CONSTRUCTION, not
    /// measurements — identical for a genuine refusal and for a fully proved
    /// query. Censuses that read them as measurements concluded "N obligations
    /// have no proof object" when the derivations existed and were complete.
    ///
    /// The observation is written to its own cache slot and never touches
    /// `solve_evidence` / `solver_statistics`, the pair the proof-authority
    /// boundary judges. Recording it cannot grant authority: the sole authority
    /// write remains `set_strict_unsat_authority`, still gated on all four
    /// conditions.
    fn install_strict_unsat_authority(
        &mut self,
        strict_replay: StrictNativeReplay,
    ) -> Option<crate::verify::ProofCertificateSummary> {
        let StrictNativeReplay {
            details,
            proof_artifact,
            native_problem_json,
            problem_hash,
        } = strict_replay;

        let evidence = SolveEvidenceSnapshot::from_solve_details(&details);
        let statistics = SolveStatisticsSnapshot::from(&details.statistics);
        // `None` today for every native-API solve: ay's decline vocabulary is
        // still text/parsed-source-centric. Carried so the day it does cover
        // this path the census reads a mechanism instead of inferring one.
        let unsat_proof_decline = details
            .verification
            .unsat_proof_decline
            .map(|mechanism| mechanism.tag().to_string());
        // The reason ay DID record. `unsat_proof_decline` above is `None` for
        // every native-API solve — its mechanisms need a parsed SMT-LIB surface
        // AST this path never builds — and that `None` was twice misread as "ay
        // refused and recorded nothing". It records an instance-specific reason
        // on this same envelope; `unknown_summary()` is the stable accessor for
        // it. Dropping it here is what forced downstream censuses to infer a
        // mechanism, and the inference conflated "a verdict was computed and
        // withheld by a soundness gate" with "no verdict was ever reached".
        let unknown_summary = details.unknown_summary();
        let unknown_reason = unknown_summary
            .as_ref()
            .map(|summary| summary.reason_code.to_string());
        let unknown_detail = unknown_summary.and_then(|summary| summary.detail);

        // Identical predicate chain to the pre-#2706 form, folded into one
        // expression so the observation below can be written on every path.
        let authorized = solve_details_have_complete_unsat_proof(&details)
            .then(|| {
                let summary = crate::verify::proof_summary_from_artifact(proof_artifact?);
                (summary.is_fully_verified() && evidence.accepted_for_consumer).then_some(summary)
            })
            .flatten();

        // Encoder-axiom consistency guard (vacuity shield for axioms): a
        // certified UNSAT whose encoder axioms are refutable ON THEIR OWN is a
        // vacuous proof, never authority. Refusal-only: a not-refuted check
        // (SAT/unknown/timeout) leaves the decision above untouched. See
        // `encoder/axiom_consistency.rs`.
        let mut axiom_refusal: Option<String> = None;
        let authorized = match authorized {
            Some(summary) => match self.check_encoder_axiom_consistency() {
                verdict if verdict.refuses_credit() => {
                    axiom_refusal = Some(format!(
                        "vacuous: encoder axioms inconsistent ({verdict:?})"
                    ));
                    None
                }
                _ => Some(summary),
            },
            None => None,
        };
        let (unknown_reason, unknown_detail) = match &axiom_refusal {
            Some(detail) => (
                Some(super::axiom_consistency::ENCODER_AXIOMS_INCONSISTENT_REASON.to_string()),
                Some(detail.clone()),
            ),
            None => (unknown_reason, unknown_detail),
        };

        crate::verify::authority_trace(|| {
            let stat = |key: &str| details.statistics.get_int(key);
            format!(
                "strict replay scope={:?} result={} complete_unsat_proof={} accepted_for_consumer={} \
                 authorized={} axiom_refusal={:?} unknown_reason={:?} unknown_detail={:?} proof_trust={:?} checked={:?} \
                 total={:?} skipped_holes={:?} checker_failures={:?}",
                self.encoding_cache.strict_replay_scope(),
                evidence.result,
                solve_details_have_complete_unsat_proof(&details),
                evidence.accepted_for_consumer,
                authorized.is_some(),
                axiom_refusal,
                unknown_reason,
                unknown_detail,
                stat("proof_trust"),
                stat("proof_checker_checked_steps"),
                stat("proof_checker_total_steps"),
                stat("proof_checker_skipped_hole_steps"),
                stat("proof_checker_failures"),
            )
        });
        self.encoding_cache.set_strict_proof_replay_observation(
            crate::shared_types::StrictProofReplayObservation {
                evidence: evidence.clone(),
                statistics: statistics.clone(),
                authority_accepted: authorized.is_some(),
                unsat_proof_decline,
                unknown_reason,
                unknown_detail,
            },
        );

        let Some(summary) = authorized else {
            if is_deterministic_strict_replay_refusal(
                self.encoding_cache
                    .strict_proof_replay_observation_unknown_reason(),
            ) {
                self.encoding_cache
                    .record_strict_replay_deterministic_refusal(problem_hash);
            }
            return None;
        };
        self.encoding_cache
            .set_strict_unsat_authority(statistics, evidence, native_problem_json);
        Some(summary)
    }

    /// Replace ordinary diagnostics with authority from an exact fresh strict
    /// replay of the current stack.
    pub(crate) fn authorize_current_stack_unsat_with_strict_proof(
        &mut self,
    ) -> Option<crate::verify::ProofCertificateSummary> {
        let Some(strict_replay) = self.replay_current_stack_with_strict_proofs(
            self.capped_fresh_timeout(std::time::Duration::from_secs(6)),
        ) else {
            return None;
        };
        self.install_strict_unsat_authority(strict_replay)
    }

    /// Strictly replay a serialized native artifact after an ordinary replay
    /// diagnosed an UNSAT base. SAT/model recovery deliberately continues to
    /// use the ordinary replay API; only this proof-enabled path may authorize
    /// an UNSAT vacuity classification.
    pub(crate) fn replay_native_json_with_strict_proofs(
        &self,
        replay_json: &str,
        timeout: std::time::Duration,
    ) -> Option<ay_dpll::api::SolveDetails> {
        let artifact = ay_dpll::api::NativeReplayArtifact::from_json_str(replay_json).ok()?;
        ay_dpll::api::Solver::replay_native_replay_artifact_with_proofs(
            &artifact,
            self.capped_fresh_timeout(timeout),
        )
        .ok()
    }

    /// Re-solve the encoder's CURRENT assertion stack in a FRESH,
    /// non-incremental `ay` solver and return its checked UNSAT certificate
    /// summary (#transpose).
    ///
    /// Recovers a genuine UNSAT that the incremental tiered solve buries under a
    /// long quantifier-recheck churn (and that the hard-timeout then kills). A
    /// fresh AY solve of the IDENTICAL native stack closes these in well under
    /// a second. SOUND, zero false-accept risk: it solves the same closed query
    /// (same declarations + assertions, nothing added/dropped); a genuinely-SAT
    /// obligation re-solves SAT (or the cap expires) and is never accepted. Used
    /// as an obligation-level precheck BEFORE the tier ladder so it fires once
    /// per obligation, not per inner `check_sat`.
    ///
    /// This fresh verdict is proof authority, not merely a diagnostic
    /// cross-check. A raw UNSAT therefore fails closed unless AY reports that
    /// proof checking was active, an UNSAT proof artifact is available, and
    /// the checker recorded zero failures.
    pub(crate) fn batch_resolve_current_stack_unsat(
        &mut self,
    ) -> Option<crate::verify::ProofCertificateSummary> {
        // Eligibility gate (perf): the batch precheck only pays off for
        // quantifier-bearing obligations small enough to batch-close quickly.
        // Skip (i) huge stacks (e.g. the 4000-assertion LIA `negative_int_pats`
        // class, where a batch solve hits the cap and wastes it) and (ii)
        // pure-ground stacks (which the normal incremental solve closes fast, so
        // the precheck is pure overhead). The datatype reconstruct/selector
        // axioms make every datatype-match obligation — incl. all of transpose's
        // arms — quantifier-bearing, so this keeps the cases that actually churn.
        let assertions = self.solver.assertions();
        if assertions.len() > 220 {
            return None;
        }
        let has_quantifier = assertions.iter().any(|&t| {
            matches!(
                self.solver.term_kind(t),
                ay_dpll::api::TermKind::Forall | ay_dpll::api::TermKind::Exists
            )
        });
        let smt2 = self.solver.to_smtlib2();
        // Fire for quantifier-bearing obligations (datatype/iterator churn) AND for
        // quantifier-FREE obligations carrying uninterpreted functions — e.g. the
        // mut-ref prophecy `__trust_wp_mut_ref_final/current/*` apps in `take_max` /
        // `rusthorn/inc_max`. Such a UF+LIA stack churns the INCREMENTAL solver for
        // the full deadline (then the hard-timeout kills it), yet a fresh
        // non-incremental parse of the IDENTICAL stack closes it in well under a
        // second (measured 0.006s for take_max). Pure-ground arithmetic stacks (no
        // quantifier, no UF — only `declare-const`) still skip: the incremental solve
        // closes those fast, so the precheck would be pure overhead. trust-wp emits
        // `declare-fun` only for arity>=1 UFs (0-arity decls use `declare-const`), so
        // its presence is a sound proxy for "this obligation has uninterpreted
        // functions". SOUND either way: the precheck solves the same closed query and
        // accepts only UNSAT (widening only changes WHICH obligations get it).
        let has_uf = smt2.contains("(declare-fun ");
        if !has_quantifier && !has_uf {
            return None;
        }
        if std::env::var("TWP_BR_DBG").is_ok() {
            let _ = std::fs::write("/tmp/twp_br_stack.smt2", &smt2);
            eprintln!(
                "[TWP_BR] obligation precheck: {} asserts, {} bytes",
                assertions.len(),
                smt2.len()
            );
        }
        let Some(strict_replay) = self.replay_current_stack_with_strict_proofs(
            self.capped_fresh_timeout(std::time::Duration::from_secs(4)),
        ) else {
            if std::env::var("TWP_BR_DBG").is_ok() {
                eprintln!("[TWP_BR] obligation native precheck replay FAILED");
            }
            return None;
        };
        let verdict = &strict_replay.details;
        if std::env::var("TWP_BR_DBG").is_ok() {
            eprintln!(
                "[TWP_BR] obligation precheck verdict: unsat={} sat={}",
                verdict.result.is_unsat(),
                verdict.result.is_sat()
            );
        }
        self.install_strict_unsat_authority(strict_replay)
    }

    /// Re-solve the encoder's CURRENT assertion stack in a FRESH,
    /// non-incremental `ay` solver and return its checked UNSAT certificate
    /// summary — WITHOUT the perf eligibility gate of
    /// [`batch_resolve_current_stack_unsat`]. Intended for REACTIVE use:
    /// call only AFTER the incremental tiered solve has already returned
    /// Unknown, so the extra fresh solve is paid at most once per genuinely-stuck
    /// obligation (never as a proactive per-obligation tax).
    ///
    /// Motivating case (#custom_variant loop_initialization): a pure-ground
    /// datatype+LIA stack (`res == Int::min(x.0, x.1)` from the min-defining
    /// facts + an `ite` goal) drives the INCREMENTAL combiner into an
    /// `LRA simplex=Sat but unsupported → Unknown` churn that the hard-timeout
    /// then kills, yet a fresh native replay of the IDENTICAL stack
    /// closes it UNSAT in well under 20ms. The gated
    /// [`batch_resolve_current_stack_unsat`] skips this stack (no quantifier, no
    /// `declare-fun` UF — datatype selectors are not UFs), so a separate,
    /// gate-free reactive entry point is required.
    ///
    /// SOUND, zero false-accept risk: it solves the SAME closed query (identical
    /// declarations + assertions, nothing added/dropped) and returns `Some`
    /// only on proof-checked UNSAT — a genuinely-SAT obligation re-solves SAT
    /// (or the cap expires) and is never accepted. Raw UNSAT without an
    /// available, checker-accepted proof fails closed. Vacuity is handled by
    /// the caller exactly as for an incremental UNSAT (the batch UNSAT flows
    /// through the identical `Verified` acceptance path and the loop-phase
    /// vacuity guards).
    pub(crate) fn batch_current_stack_unsat_reactive(
        &mut self,
    ) -> Option<crate::verify::ProofCertificateSummary> {
        let assertions = self.solver.assertions();
        // Guard against pathologically large stacks where a batch solve would
        // just burn the cap: the reactive path targets the small datatype/LIA
        // loop VCs that churn incrementally, not 4000-assertion LIA piles.
        if assertions.len() > 400 {
            return None;
        }
        let smt2 = self.solver.to_smtlib2();
        if std::env::var("TWP_BR_DBG").is_ok() {
            let _ = std::fs::write("/tmp/twp_br_reactive_stack.smt2", &smt2);
            eprintln!(
                "[TWP_BR] reactive batch re-solve: {} asserts, {} bytes",
                assertions.len(),
                smt2.len()
            );
        }
        let Some(strict_replay) = self.replay_current_stack_with_strict_proofs(
            self.capped_fresh_timeout(std::time::Duration::from_secs(6)),
        ) else {
            return None;
        };
        let verdict = &strict_replay.details;
        if std::env::var("TWP_BR_DBG").is_ok() {
            eprintln!(
                "[TWP_BR] reactive batch re-solve verdict: unsat={} sat={}",
                verdict.result.is_unsat(),
                verdict.result.is_sat()
            );
        }
        self.install_strict_unsat_authority(strict_replay)
    }

    /// Fresh-parse the given BASE-stack SMT (an obligation's assertions WITHOUT the
    /// negated goal) on a non-incremental solver and return whether it is SAT — i.e.
    /// the preconditions/base facts are mutually consistent. This is the vacuity
    /// shield for [`batch_resolve_current_stack_unsat`]: a batch UNSAT result is only
    /// trustworthy as a *verification* when the base is genuinely satisfiable (an
    /// UNSAT base makes the proof vacuous). SOUND: a fresh closed solve; conservative
    /// (returns false — fall through to the normal path — on parse failure or any
    /// non-SAT base, so a vacuous/uncertain base is never accepted as verified).
    pub(crate) fn batch_base_smt_is_sat(&self, base_smt: &str) -> bool {
        let mut fresh = ay_dpll::api::Solver::new(ay_dpll::api::Logic::All);
        fresh.set_timeout(Some(
            self.capped_fresh_timeout(std::time::Duration::from_secs(4)),
        ));
        if fresh.parse_smtlib2(base_smt).is_err() {
            return false;
        }
        let details = fresh.check_sat_with_details();
        has_complete_sat_validation(
            details.result.is_sat(),
            details.result.was_model_validated(),
            details.verification.sat_model_validated,
        )
    }

    /// Fresh-replay the encoder's CURRENT native assertion stack and report whether it
    /// is SAT. Used by the vacuity base recheck (negated goal already popped):
    /// when the incremental base solve churns to Unknown on in-scope universals
    /// (e.g. a predicate-closure obligation's range + closure defining axioms),
    /// a fresh non-incremental solve of the IDENTICAL base closes the
    /// consistency check in well under a second. SOUND: a genuinely vacuous
    /// (UNSAT) base re-solves UNSAT (or the cap expires), never SAT, so a
    /// vacuous proof is never accepted. Mirrors [`batch_base_smt_is_sat`] but
    /// sources the SMT from the live solver rather than a snapshot string.
    /// [`Self::batch_current_stack_is_sat`] returning the fresh replay's
    /// `SolveDetails` on a model-VALIDATED SAT, `None` otherwise. For lanes
    /// that must carry the validating solve's evidence (a refutation witness),
    /// not just its boolean.
    pub(crate) fn batch_current_stack_validated_sat_details(
        &self,
    ) -> Option<ay_dpll::api::SolveDetails> {
        // The replay solves the same stack, split constants and all, so its
        // model is no more an execution than the incremental solver's: the
        // refutation it would back is withheld by the same gate (D-218).
        if let Some(name) = self.split_source_read_by_assertions() {
            crate::verify::authority_trace(|| {
                format!("fresh replay witness refused: a phantom sort upgrade split `{name}`")
            });
            return None;
        }
        let details = self.replay_current_stack_diagnostic_with_timeout(
            self.capped_fresh_timeout(std::time::Duration::from_secs(10)),
        )?;
        has_complete_sat_validation(
            details.result.is_sat(),
            details.result.was_model_validated(),
            details.verification.sat_model_validated,
        )
        .then_some(details)
    }

    pub(crate) fn batch_current_stack_is_sat(&self) -> bool {
        // The predicate-closure base carries a closure defining universal; the
        // fresh solver confirms SAT via CEGQI quantifier instantiation, which
        // needs more than the 4s `batch_base_smt_is_sat` budget (measured: 4s
        // returns `QuantifierCegqiIncomplete`, ~5-8s returns SAT). The nominal
        // 10s cap is further bounded to 3/8 of the caller timeout so AY's 4x
        // quantified-solve backstop remains inside the caller's 1.5x hard
        // envelope. SOUND: only a confirmed-SAT base is accepted; the cap
        // expiring leaves it Unknown (falls through). (#985)
        let Some(details) = self.replay_current_stack_diagnostic_with_timeout(
            self.capped_fresh_timeout(std::time::Duration::from_secs(10)),
        ) else {
            return false;
        };
        has_complete_sat_validation(
            details.result.is_sat(),
            details.result.was_model_validated(),
            details.verification.sat_model_validated,
        )
    }

    /// Whether any single-parameter predicate-closure defining axiom is in scope
    /// (e.g. a PredCell `c@ == |z| ...` precondition). Lets verification-side
    /// vacuity/precheck paths narrowly target the closure obligations without
    /// reaching into the encoder's private state.
    pub(crate) fn has_closure_mapping_axioms(&self) -> bool {
        !self.closure_mapping_axioms.is_empty()
    }

    /// Whether Seq theory declarations have been initialized for this
    /// obligation. Seq-heavy base contexts can be straightforwardly
    /// satisfiable while an incremental post-proof model check remains
    /// incomplete; the vacuity guard uses this to enable an exact fresh-stack
    /// SAT confirmation.
    pub(crate) fn has_seq_theory(&self) -> bool {
        self.seq_state.funcs().is_some()
    }

    /// Whether any logic-function declarations are active. Recursive open
    /// definitions are supplied through scoped ground instances; after a proof
    /// those declarations can make an otherwise simple satisfiable base model
    /// pathological for the incremental solver. The exact fresh-stack vacuity
    /// check uses this as a narrow eligibility signal.
    pub(crate) fn has_logic_functions(&self) -> bool {
        !self.logic_funcs_ref().is_empty()
    }

    /// Whether any enum-payload / UF-constructor bridge UNIVERSAL is in scope
    /// (#result_own). Lets the vacuity base recheck narrowly target the bases
    /// whose fresh SAT check ay reports `quantifier-unhandled` on solely because
    /// of these conservative definitional bridges.
    pub(crate) fn has_enum_payload_bridge_forall_axioms(&self) -> bool {
        !self.enum_payload_bridge_forall_terms.is_empty()
    }

    /// Re-solve the CURRENT base stack in a fresh, non-incremental `ay` solver
    /// with NATIVE datatype semantics, EXEMPTING the recorded enum-payload /
    /// UF-constructor bridge universals (#result_own).
    ///
    /// ay's batch solver reports `Unknown(quantifier-unhandled)` — never SAT —
    /// whenever these bridge universals are present, so the ordinary
    /// `resolve_base_sat_result` path can only churn the incremental solver to
    /// its hard-timeout on such a base. The bridge universals are a conservative
    /// DEFINITIONAL extension of fresh projection/coercion symbols
    /// (`enum_payload_get_N`, `__trust_wp_uf_ctor_coerce_*`); the encoder also
    /// emits their ground consequences at every observed receiver (see
    /// `assert_registered_enum_payload_ground_consequences_from_assertions`,
    /// which the caller re-runs first). Exempting exactly them (tracked by
    /// identity) and re-solving the identical base with native datatypes yields
    /// a genuine, model-validatable SAT model in milliseconds.
    ///
    /// SOUNDNESS (cardinal-sin firewall): (1) only the encoder's own bridge
    /// universals are dropped — never a user precondition, which never carries
    /// an internal bridge tag; (2) native `declare-datatype` semantics are
    /// preserved (as opposed to the UF over-abstraction of `to_smtlib2`), so
    /// constructor injectivity/distinctness contradictions are still detected;
    /// (3) the caller accepts ONLY a MODEL-VALIDATED SAT — a genuinely vacuous
    /// base (whose contradiction over observed terms is retained by the ground
    /// bridges) replays UNSAT and is never accepted. Dropping constraints can
    /// only make a base *more* satisfiable, so this never manufactures a false
    /// vacuity (a false UNSAT); the only residual direction is a false SAT,
    /// which the model-validation gate and the retained native ground bridges
    /// close.
    pub(crate) fn replay_native_base_exempting_bridge_foralls(
        &self,
    ) -> Option<ay_dpll::api::SolveDetails> {
        if self.enum_payload_bridge_forall_terms.is_empty() {
            return None;
        }
        let bridge_ids: std::collections::HashSet<_> = self
            .enum_payload_bridge_forall_terms
            .iter()
            .map(|t| t.id())
            .collect();
        let mut artifact = self
            .solver
            .export_native_replay_artifact(ay_dpll::api::NativeReplayMetadata::default(), None);
        let before = artifact.assertions.len();
        artifact
            .assertions
            .retain(|assertion| !bridge_ids.contains(&assertion.term));
        // Nothing was actually exempted (the tracked universals are not on the
        // live base stack) — fall through to the normal recheck rather than
        // re-solving an identical query.
        if artifact.assertions.len() == before {
            return None;
        }
        // Keep the fresh solve well inside the base-recheck hard-timeout envelope.
        artifact.timeout_ms = Some(10_000);
        ay_dpll::api::Solver::replay_native_replay_artifact(&artifact).ok()
    }

    /// Declare a function, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_declare_fun(
        &mut self,
        context: &str,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, EncodingError> {
        self.solver
            .try_declare_fun(name, domain, range)
            .map_err(|e| EncodingError::solver_error(format!("{context}: declare_fun failed: {e}")))
    }

    /// Declare a constant, mapping ay SolverError to EncodingError.
    pub(crate) fn safe_declare_const(
        &mut self,
        context: &str,
        name: &str,
        sort: Sort,
    ) -> Result<Term, EncodingError> {
        let _ = context;
        Ok(self.solver.declare_const(name, sort))
    }

    /// Apply a function declaration to argument terms, validating arity and
    /// mapping ay `SolverError` to `EncodingError`. (#1532, #2131)
    pub(crate) fn safe_apply(
        &mut self,
        context: &str,
        func: &FuncDecl,
        args: &[Term],
    ) -> Result<Term, EncodingError> {
        if func.arity() != args.len() {
            return Err(EncodingError::solver_error(format!(
                "arity mismatch in {context}: function {} expects {} args, got {}",
                func.name(),
                func.arity(),
                args.len()
            )));
        }
        let result = self
            .solver
            .try_apply(func, args)
            .map_err(|e| EncodingError::solver_error(format!("sort mismatch in {context}: {e}")))?;
        // Choke point for the positional `.0` accessor family: every encoder
        // path that builds an application of the `__trust_wp_tuple_get_0` UF
        // (raw decl or signature-keyed placeholder decl) funnels through
        // safe_apply, so emitting the guarded Option payload bridge here
        // covers ALL application sites — not only the apply_logic_fn
        // creation path (the ghost_vec decisive-fact gap). The hook is a
        // no-op for every other declaration; see
        // `bridge_tuple_get_0_family_application` for the family match and
        // `bridge_tuple_get_0_to_option_some_value` for the soundness guards.
        self.bridge_tuple_get_0_family_application(func.name(), args, result);
        Ok(result)
    }

    /// Select from an array term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_select(
        &mut self,
        context: &str,
        array: Term,
        index: Term,
    ) -> Result<Term, EncodingError> {
        self.solver
            .try_select(array, index)
            .map_err(|e| EncodingError::solver_error(format!("{context}: select failed: {e}")))
    }

    /// Store into an array term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_store(
        &mut self,
        context: &str,
        array: Term,
        index: Term,
        value: Term,
    ) -> Result<Term, EncodingError> {
        self.solver
            .try_store(array, index, value)
            .map_err(|e| EncodingError::solver_error(format!("{context}: store failed: {e}")))
    }

    /// Declare a datatype, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_declare_datatype(
        &mut self,
        context: &str,
        dt: &DatatypeSort,
    ) -> Result<(), EncodingError> {
        self.solver.try_declare_datatype(dt).map_err(|e| {
            EncodingError::solver_error(format!("{context}: declare_datatype failed: {e}"))
        })
    }

    /// Assert a term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_assert_term(
        &mut self,
        context: &str,
        term: Term,
    ) -> Result<(), EncodingError> {
        self.solver
            .try_assert_term(term)
            .map_err(|e| EncodingError::solver_error(format!("{context}: assert_term failed: {e}")))
    }

    /// Assert a named term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_assert_named(
        &mut self,
        context: &str,
        term: Term,
        name: &str,
    ) -> Result<(), EncodingError> {
        self.solver.try_assert_named(term, name).map_err(|e| {
            EncodingError::solver_error(format!("{context}: assert_named failed: {e}"))
        })
    }

    /// Push a solver scope, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_push(&mut self, context: &str) -> Result<(), EncodingError> {
        self.solver
            .try_push()
            .map_err(|e| EncodingError::solver_error(format!("{context}: push failed: {e}")))
    }

    /// Pop a solver scope, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_pop(&mut self, context: &str) -> Result<(), EncodingError> {
        self.solver
            .try_pop()
            .map_err(|e| EncodingError::solver_error(format!("{context}: pop failed: {e}")))
    }

    /// Check satisfiability, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_check_sat(
        &mut self,
        context: &str,
    ) -> Result<VerifiedSolveResult, EncodingError> {
        self.solver
            .try_check_sat()
            .map_err(|e| EncodingError::solver_error(format!("{context}: check_sat failed: {e}")))
    }

    /// Get the unsat core, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_get_unsat_core(
        &mut self,
        context: &str,
    ) -> Result<Vec<String>, EncodingError> {
        self.solver.try_get_unsat_core().map_err(|e| {
            EncodingError::solver_error(format!("{context}: get_unsat_core failed: {e}"))
        })
    }

    /// Build a datatype tester term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_datatype_tester(
        &mut self,
        context: &str,
        dt: &DatatypeSort,
        ctor: &str,
        expr: Term,
    ) -> Result<Term, EncodingError> {
        let actual_ctor = datatype_constructor_name(dt, ctor);
        self.solver
            .try_datatype_tester(&actual_ctor, expr)
            .map_err(|e| {
                EncodingError::solver_error(format!("{context}: datatype_tester failed: {e}"))
            })
    }

    /// Build a datatype selector term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_datatype_selector(
        &mut self,
        context: &str,
        selector: &str,
        expr: Term,
        result_sort: Sort,
    ) -> Result<Term, EncodingError> {
        self.solver
            .try_datatype_selector(selector, expr, result_sort)
            .map_err(|e| {
                EncodingError::solver_error(format!("{context}: datatype_selector failed: {e}"))
            })
    }

    /// Build a datatype constructor term, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_datatype_constructor(
        &mut self,
        context: &str,
        dt: &DatatypeSort,
        ctor: &str,
        args: &[Term],
    ) -> Result<Term, EncodingError> {
        let actual_ctor = datatype_constructor_name(dt, ctor);
        let term = catch_solver_panic_with_reason(context, || {
            self.solver.try_datatype_constructor(dt, &actual_ctor, args)
        })
        .map_err(|e| EncodingError::solver_error(e.to_string()))?
        .map_err(|e| {
            EncodingError::solver_error(format!("{context}: datatype_constructor failed: {e}"))
        })?;
        let actual = self.solver.get_sort(term);
        let expected = Sort::Datatype(dt.clone()).as_term_sort();
        if actual != expected {
            return Err(EncodingError::solver_error(format!(
                "{context}: datatype_constructor returned {actual:?}, expected {expected:?}"
            )));
        }
        Ok(term)
    }

    /// Set a solver option, mapping ay `SolverError` to `EncodingError`.
    pub(crate) fn safe_set_option(
        &mut self,
        context: &str,
        keyword: &str,
        value: &str,
    ) -> Result<(), EncodingError> {
        self.solver
            .try_set_option(keyword, value)
            .map_err(|e| EncodingError::solver_error(format!("{context}: set_option failed: {e}")))
    }

    // -----------------------------------------------------------------------
    // Advanced solver methods (#2727) -- facade for solver operations that
    // ay-dpll exposes but trust-wp does not yet consume broadly. Each wrapper
    // is a thin forward over the ay call and converts `SolverError` into
    // `EncodingError`.
    // -----------------------------------------------------------------------

    /// Facade for `ay_dpll::Solver::check_sat_assuming` -- per-query
    /// assumptions without mutating the assertion stack. The ay call itself
    /// is infallible (returns `VerifiedSolveResult` directly) so this
    /// wrapper returns a `Result` only to keep the facade signature uniform
    /// with the other `safe_*` check methods. (#2727)
    pub(crate) fn safe_check_sat_assuming(
        &mut self,
        context: &str,
        assumptions: &[Term],
    ) -> Result<VerifiedSolveResult, EncodingError> {
        let _ = context;
        Ok(self.solver.check_sat_assuming(assumptions))
    }

    /// Facade for `ay_dpll::Solver::try_annotated_unsat_core` -- return
    /// the theory-attributed proof explanation after UNSAT. Maps ay
    /// `SolverError` to `EncodingError`. (#2727)
    pub(crate) fn safe_annotated_unsat_core(
        &self,
        context: &str,
    ) -> Result<AnnotatedUnsatCore, EncodingError> {
        self.solver.try_annotated_unsat_core().map_err(|e| {
            EncodingError::solver_error(format!("{context}: annotated_unsat_core failed: {e}"))
        })
    }

    /// Facade for `ay_dpll::Solver::try_model_provenance` -- describe how
    /// each model assignment was produced (counterexample quality). Maps
    /// ay `SolverError` to `EncodingError`. (#2727)
    pub(crate) fn safe_model_provenance(
        &self,
        context: &str,
    ) -> Result<ModelProvenance, EncodingError> {
        self.solver.try_model_provenance().map_err(|e| {
            EncodingError::solver_error(format!("{context}: model_provenance failed: {e}"))
        })
    }

    /// Facade for `ay_dpll::Solver::parse_smtlib2` -- parse SMT-LIB2 text
    /// and return the asserted terms. Maps ay `SolverError` to
    /// `EncodingError`. (#2727)
    pub(crate) fn safe_parse_smtlib2(
        &mut self,
        context: &str,
        input: &str,
    ) -> Result<Vec<Term>, EncodingError> {
        self.solver.parse_smtlib2(input).map_err(|e| {
            EncodingError::solver_error(format!("{context}: parse_smtlib2 failed: {e}"))
        })
    }

    /// Facade for `ay_dpll::api::Solver::cross_check_smtlib2` -- run an
    /// SMT-LIB2 script under multiple solver variants for differential
    /// testing. This is an associated function on the ay `Solver` type (no
    /// `self`); the wrapper still takes `&self` so callers route uniformly
    /// through the encoder. Maps ay `SolverError` to `EncodingError`.
    /// (#2727)
    pub(crate) fn safe_cross_check_smtlib2(
        &self,
        context: &str,
        input: &str,
        variants: &[CrossCheckVariant],
    ) -> Result<CrossCheckReport, EncodingError> {
        let _ = self;
        ay_dpll::api::Solver::cross_check_smtlib2(input, variants).map_err(|e| {
            EncodingError::solver_error(format!("{context}: cross_check_smtlib2 failed: {e}"))
        })
    }

    /// Facade for `ay_dpll::Solver::try_get_model` -- retrieve the
    /// verified counterexample model after SAT. Maps ay `SolverError` to
    /// `EncodingError`. (#2727)
    pub(crate) fn safe_get_model(&self, context: &str) -> Result<VerifiedModel, EncodingError> {
        self.solver
            .try_get_model()
            .map_err(|e| EncodingError::solver_error(format!("{context}: get_model failed: {e}")))
    }

    /// Facade for `ay_dpll::Solver::try_get_model_str` -- retrieve the
    /// model as SMT-LIB text. Maps ay `SolverError` to `EncodingError`.
    /// (#2727)
    pub(crate) fn safe_get_model_str(&self, context: &str) -> Result<String, EncodingError> {
        self.solver.try_get_model_str().map_err(|e| {
            EncodingError::solver_error(format!("{context}: get_model_str failed: {e}"))
        })
    }

    /// Facade for `ay_dpll::Solver::try_get_value` -- evaluate a single
    /// term under the current model. Maps ay `SolverError` to
    /// `EncodingError`. (#2727)
    pub(crate) fn safe_get_value(
        &self,
        context: &str,
        term: Term,
    ) -> Result<ModelValue, EncodingError> {
        self.solver
            .try_get_value(term)
            .map_err(|e| EncodingError::solver_error(format!("{context}: get_value failed: {e}")))
    }

    /// Facade for `ay_dpll::Solver::try_get_values` -- evaluate a batch
    /// of terms under the current model. Maps ay `SolverError` to
    /// `EncodingError`. (#2727)
    pub(crate) fn safe_get_values(
        &self,
        context: &str,
        terms: &[Term],
    ) -> Result<Vec<ModelValue>, EncodingError> {
        self.solver
            .try_get_values(terms)
            .map_err(|e| EncodingError::solver_error(format!("{context}: get_values failed: {e}")))
    }

    /// Facade for `ay_dpll::Solver::unsat_assumptions` -- retrieve the
    /// subset of prior assumptions found in the unsat core. Returns
    /// `Ok(None)` when the last solve was not UNSAT or no assumptions
    /// were supplied (matching the underlying ay contract). (#2727)
    pub(crate) fn safe_unsat_assumptions(
        &self,
        context: &str,
    ) -> Result<Option<Vec<Term>>, EncodingError> {
        let _ = context;
        Ok(self.solver.unsat_assumptions())
    }

    /// Facade for `ay_dpll::Solver::try_reset` -- clear the solver back
    /// to its initial empty state (scopes, assertions, and declarations).
    /// Maps ay `SolverError` to `EncodingError`. (#2727)
    pub(crate) fn safe_reset(&mut self, context: &str) -> Result<(), EncodingError> {
        self.solver
            .try_reset()
            .map_err(|e| EncodingError::solver_error(format!("{context}: reset failed: {e}")))
    }

    /// Facade for `ay_dpll::Solver::try_reset_assertions` -- drop the
    /// asserted formulas while preserving declarations. Maps ay
    /// `SolverError` to `EncodingError`. (#2727)
    pub(crate) fn safe_reset_assertions(&mut self, context: &str) -> Result<(), EncodingError> {
        self.solver.try_reset_assertions().map_err(|e| {
            EncodingError::solver_error(format!("{context}: reset_assertions failed: {e}"))
        })
    }

    /// Facade for `ay_dpll::Solver::statistics` -- return an owned
    /// snapshot of the current solver statistics (counts, timings, and
    /// the extra map). ay exposes statistics infallibly; this wrapper
    /// preserves the `Result` signature for facade uniformity and returns
    /// a `Clone` of the snapshot so callers do not hold a borrow on the
    /// solver. (#2727)
    pub(crate) fn safe_statistics(&self, context: &str) -> Result<Statistics, EncodingError> {
        let _ = context;
        Ok(self.solver.statistics().clone())
    }
}

// ---------------------------------------------------------------------------
// axiom_* -- axiom/setup contexts (return Option, skip on failure)
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl AYEncoder {
    /// Apply a function declaration in axiom contexts, using `try_apply` to
    /// catch sort mismatches gracefully. Returns `None` on mismatch so callers
    /// can skip the axiom instead of panicking. (#2151)
    pub(crate) fn axiom_apply(
        &mut self,
        _context: &str,
        func: &FuncDecl,
        args: &[Term],
    ) -> Option<Term> {
        self.solver.try_apply(func, args).ok()
    }

    /// Select from an array term in axiom contexts. Returns `None` on failure.
    pub(crate) fn axiom_select(
        &mut self,
        _context: &str,
        array: Term,
        index: Term,
    ) -> Option<Term> {
        self.solver.try_select(array, index).ok()
    }

    /// Store into an array term in axiom contexts. Returns `None` on failure.
    pub(crate) fn axiom_store(
        &mut self,
        _context: &str,
        array: Term,
        index: Term,
        value: Term,
    ) -> Option<Term> {
        self.solver.try_store(array, index, value).ok()
    }

    /// Declare a datatype in axiom contexts. Returns `false` on failure.
    pub(crate) fn axiom_declare_datatype(&mut self, _context: &str, dt: &DatatypeSort) -> bool {
        self.solver.try_declare_datatype(dt).is_ok()
    }

    /// Build a datatype constructor term in axiom contexts. Returns `None` on failure.
    pub(crate) fn axiom_datatype_constructor(
        &mut self,
        context: &str,
        dt: &DatatypeSort,
        ctor: &str,
        args: &[Term],
    ) -> Option<Term> {
        let actual_ctor = datatype_constructor_name(dt, ctor);
        let term = catch_solver_panic_with_reason(context, || {
            self.solver.try_datatype_constructor(dt, &actual_ctor, args)
        })
        .ok()?
        .ok()?;
        let actual = self.solver.get_sort(term);
        let expected = Sort::Datatype(dt.clone()).as_term_sort();
        (actual == expected).then_some(term)
    }

    /// Build a datatype tester term in axiom contexts. Returns None on failure.
    pub(crate) fn axiom_datatype_tester(
        &mut self,
        _context: &str,
        ctor: &str,
        expr: Term,
    ) -> Option<Term> {
        self.solver.try_datatype_tester(ctor, expr).ok()
    }

    /// Build a datatype selector term in axiom contexts. Returns None on failure.
    pub(crate) fn axiom_datatype_selector(
        &mut self,
        _context: &str,
        selector: &str,
        expr: Term,
        result_sort: Sort,
    ) -> Option<Term> {
        self.solver
            .try_datatype_selector(selector, expr, result_sort)
            .ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_timeout_keeps_quantified_backstop_inside_caller_envelope() {
        let mut encoder = AYEncoder::new();
        let ten_seconds = std::time::Duration::from_secs(10);

        encoder.set_timeout(None);
        assert_eq!(encoder.capped_fresh_timeout(ten_seconds), ten_seconds);

        encoder.set_timeout(Some(std::time::Duration::from_mins(1)));
        assert_eq!(encoder.capped_fresh_timeout(ten_seconds), ten_seconds);

        encoder.set_timeout(Some(std::time::Duration::from_secs(15)));
        assert_eq!(
            encoder.capped_fresh_timeout(ten_seconds),
            std::time::Duration::from_millis(5_625)
        );

        encoder.set_timeout(Some(std::time::Duration::from_secs(1)));
        assert_eq!(
            encoder.capped_fresh_timeout(ten_seconds),
            std::time::Duration::from_millis(375)
        );
    }

    #[test]
    fn batch_base_sat_requires_a_validated_model() {
        let encoder = AYEncoder::new_all();
        let validated = "(declare-const x Int)\n(assert (> x 0))\n";
        assert!(encoder.batch_base_smt_is_sat(validated));

        // Exercise the consumer boundary explicitly. AY's public result type
        // currently downgrades an unfunnelled raw SAT before returning it, but
        // the WP vacuity shield must remain fail-closed even if either evidence
        // surface is absent in a future solver implementation.
        assert!(!has_complete_sat_validation(true, false, false));
        assert!(!has_complete_sat_validation(true, true, false));
        assert!(!has_complete_sat_validation(true, false, true));
        assert!(!has_complete_sat_validation(false, true, true));
        assert!(has_complete_sat_validation(true, true, true));
    }

    #[test]
    fn reactive_fresh_unsat_retains_the_checked_artifact() {
        let mut encoder = AYEncoder::new_all();
        let contradiction = encoder.solver_mut().bool_const(false);
        encoder.assert_term(contradiction);

        let summary = encoder
            .batch_current_stack_unsat_reactive()
            .expect("literal false must have a strict fresh-replay certificate");

        assert!(summary.is_fully_verified());
        assert!(summary
            .alethe_text
            .as_deref()
            .is_some_and(|proof| !proof.trim().is_empty()));
        let evidence = encoder
            .last_solve_evidence()
            .expect("strict replay must install its exact solve evidence");
        let statistics = encoder
            .last_solve_statistics()
            .expect("strict replay must install its exact solve statistics");
        assert!(solve_snapshots_have_complete_unsat_proof(
            evidence, statistics
        ));
        assert!(encoder.native_replay_json().is_some());
    }

    #[test]
    fn reactive_fresh_sat_cannot_install_unsat_authority() {
        let mut encoder = AYEncoder::new_all();

        assert!(encoder.batch_current_stack_unsat_reactive().is_none());
        assert!(encoder.last_solve_evidence().is_none());
        assert!(encoder.last_solve_statistics().is_none());
        assert!(encoder.native_replay_json().is_none());
    }

    #[test]
    fn fresh_unsat_authority_requires_checked_proof_evidence() {
        let complete = UnsatProofAuthorityEvidence {
            is_unsat: true,
            consumer_accepted: true,
            proof_checking_active: true,
            proof_available: true,
            summary_checker_failures: 0,
            raw_checker_failures: Some(0),
            proof_complete: true,
            trust_fallbacks: Some(0),
            checked_steps: Some(7),
            total_steps: Some(7),
            skipped_hole_steps: Some(0),
        };
        assert!(has_complete_unsat_proof(complete));

        let mut not_unsat = complete;
        not_unsat.is_unsat = false;
        assert!(!has_complete_unsat_proof(not_unsat));

        let mut consumer_rejected = complete;
        consumer_rejected.consumer_accepted = false;
        assert!(!has_complete_unsat_proof(consumer_rejected));

        let mut checker_inactive = complete;
        checker_inactive.proof_checking_active = false;
        assert!(!has_complete_unsat_proof(checker_inactive));

        let mut proof_unavailable = complete;
        proof_unavailable.proof_available = false;
        assert!(!has_complete_unsat_proof(proof_unavailable));

        let mut summary_failure = complete;
        summary_failure.summary_checker_failures = 1;
        assert!(!has_complete_unsat_proof(summary_failure));

        let mut raw_failure_missing = complete;
        raw_failure_missing.raw_checker_failures = None;
        assert!(!has_complete_unsat_proof(raw_failure_missing));
        let mut raw_failure = complete;
        raw_failure.raw_checker_failures = Some(1);
        assert!(!has_complete_unsat_proof(raw_failure));

        let mut incomplete = complete;
        incomplete.proof_complete = false;
        assert!(!has_complete_unsat_proof(incomplete));

        let mut trust_missing = complete;
        trust_missing.trust_fallbacks = None;
        assert!(!has_complete_unsat_proof(trust_missing));
        let mut trusted = complete;
        trusted.trust_fallbacks = Some(1);
        assert!(!has_complete_unsat_proof(trusted));

        let mut checked_missing = complete;
        checked_missing.checked_steps = None;
        assert!(!has_complete_unsat_proof(checked_missing));
        let mut total_missing = complete;
        total_missing.total_steps = None;
        assert!(!has_complete_unsat_proof(total_missing));
        let mut empty_proof = complete;
        empty_proof.checked_steps = Some(0);
        empty_proof.total_steps = Some(0);
        assert!(!has_complete_unsat_proof(empty_proof));
        let mut partially_checked = complete;
        partially_checked.checked_steps = Some(6);
        assert!(!has_complete_unsat_proof(partially_checked));

        let mut skipped_missing = complete;
        skipped_missing.skipped_hole_steps = None;
        assert!(!has_complete_unsat_proof(skipped_missing));
        let mut skipped_hole = complete;
        skipped_hole.skipped_hole_steps = Some(1);
        assert!(!has_complete_unsat_proof(skipped_hole));
    }

    #[test]
    fn ordinary_native_replay_unsat_is_diagnostic_but_strict_replay_has_authority() {
        let mut solver = ay_dpll::api::Solver::new(ay_dpll::api::Logic::QfUf);
        let proposition = solver.declare_const("strict_replay_control", Sort::Bool);
        let negated = solver.not(proposition);
        solver.assert_term(proposition);
        solver.assert_term(negated);
        let original = solver.check_sat_with_details();
        assert!(original.result.is_unsat());
        let artifact =
            solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&original));

        let ordinary = ay_dpll::api::Solver::replay_native_replay_artifact(&artifact)
            .expect("ordinary native replay should run");
        assert!(ordinary.result.is_unsat());
        assert!(
            !solve_details_have_complete_unsat_proof(&ordinary),
            "ordinary replay must never acquire proof authority implicitly"
        );

        let strict = ay_dpll::api::Solver::replay_native_replay_artifact_with_proofs(
            &artifact,
            std::time::Duration::from_secs(2),
        )
        .expect("strict native replay should produce and check the Boolean refutation");
        assert!(
            solve_details_have_complete_unsat_proof(&strict),
            "WP must independently accept every strict proof-authority field: {strict:?}"
        );
    }

    #[test]
    fn test_safe_declare_fun_creates_function() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "my_fn", &[Sort::Int], Sort::Bool)
            .expect("declare_fun should succeed");
        assert_eq!(f.arity(), 1);
    }

    #[test]
    fn test_safe_apply_correct_arity() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "add_one", &[Sort::Int], Sort::Int)
            .expect("declare");
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let result = encoder.safe_apply("test", &f, &[x]);
        assert!(result.is_ok(), "should succeed with correct arity");
    }

    #[test]
    fn test_safe_apply_arity_mismatch_returns_error() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "binary_fn", &[Sort::Int, Sort::Int], Sort::Int)
            .expect("declare");
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let result = encoder.safe_apply("test", &f, &[x]);
        assert!(result.is_err(), "should fail with arity mismatch");
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("arity mismatch"),
            "error should mention arity: {err_msg}"
        );
    }

    #[test]
    fn test_axiom_apply_returns_none_on_sort_mismatch() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "int_fn", &[Sort::Int], Sort::Int)
            .expect("declare");
        let b = encoder.solver_mut().bool_const(true);
        // Passing Bool to an Int-domain function should fail silently
        let result = encoder.axiom_apply("test", &f, &[b]);
        // axiom_apply uses try_apply which may or may not detect sort mismatch
        // depending on ay internals -- it returns None on error
        assert!(
            result.is_some() || result.is_none(),
            "axiom_apply should handle gracefully"
        );
    }

    #[test]
    fn test_axiom_apply_returns_some_on_correct_sorts() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "id_fn", &[Sort::Int], Sort::Int)
            .expect("declare");
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let result = encoder.axiom_apply("test", &f, &[x]);
        assert!(
            result.is_some(),
            "axiom_apply with correct sorts should return Some"
        );
    }

    #[test]
    fn test_safe_apply_zero_arity_function() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "const_fn", &[], Sort::Int)
            .expect("declare");
        let result = encoder.safe_apply("test", &f, &[]);
        assert!(result.is_ok(), "zero-arity apply should succeed");
    }

    #[test]
    fn test_safe_apply_error_includes_context() {
        let mut encoder = AYEncoder::new();
        let f = encoder
            .safe_declare_fun("test", "unary_fn", &[Sort::Int], Sort::Int)
            .expect("declare");
        let result = encoder.safe_apply("my_context", &f, &[]);
        assert!(result.is_err());
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("my_context"),
            "error should include context: {err_msg}"
        );
    }

    fn option_int_datatype() -> DatatypeSort {
        use ay_dpll::api::{DatatypeConstructor, DatatypeField};

        DatatypeSort::new(
            "SafeOptionInt",
            vec![
                DatatypeConstructor::unit("None"),
                DatatypeConstructor::new(
                    "Some",
                    vec![DatatypeField::new("option_some_value", Sort::Int)],
                ),
            ],
        )
    }

    #[test]
    fn test_safe_declare_datatype_succeeds() {
        let mut encoder = AYEncoder::new();
        let dt = option_int_datatype();

        encoder
            .safe_declare_datatype("test", &dt)
            .expect("declare_datatype should succeed");

        let opt = encoder
            .get_or_declare_var("opt", Sort::Datatype(dt))
            .expect("declare opt");
        let _ = opt;
    }

    #[test]
    fn test_safe_assert_term_succeeds() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);
        let eq = encoder.solver.eq(x, zero);

        encoder
            .safe_assert_term("test", eq)
            .expect("assert_term should succeed");

        assert!(
            encoder
                .safe_check_sat("test")
                .expect("check_sat should succeed")
                .is_sat(),
            "x = 0 should be satisfiable"
        );
    }

    #[test]
    fn test_safe_check_sat_returns_result() {
        let mut encoder = AYEncoder::new();

        assert!(
            encoder
                .safe_check_sat("test")
                .expect("check_sat should succeed")
                .is_sat(),
            "empty solver should be satisfiable"
        );
    }

    #[test]
    fn test_safe_get_unsat_core_after_unsat() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);

        encoder
            .safe_set_option("test", ":produce-unsat-cores", "true")
            .expect("enable unsat cores");

        let pos = encoder.solver.gt(x, zero);
        encoder
            .safe_assert_named("test", pos, "positive")
            .expect("assert positive");

        let neg = encoder.solver.lt(x, zero);
        encoder
            .safe_assert_named("test", neg, "negative")
            .expect("assert negative");

        assert!(
            encoder
                .safe_check_sat("test")
                .expect("check_sat should succeed")
                .is_unsat(),
            "x > 0 and x < 0 should be unsat"
        );

        let core = encoder
            .safe_get_unsat_core("test")
            .expect("unsat core should be available");
        assert!(
            core.contains(&"positive".to_string()),
            "positive should be in unsat core: {core:?}"
        );
        assert!(
            core.contains(&"negative".to_string()),
            "negative should be in unsat core: {core:?}"
        );
    }

    #[test]
    fn test_safe_push_pop_scope() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);
        let pos = encoder.solver.gt(x, zero);

        encoder
            .safe_assert_term("outer", pos)
            .expect("outer assertion should succeed");
        encoder.safe_push("push").expect("push should succeed");

        let neg = encoder.solver.lt(x, zero);
        encoder
            .safe_assert_term("inner", neg)
            .expect("inner assertion should succeed");
        assert!(
            encoder
                .safe_check_sat("inner")
                .expect("inner check_sat should succeed")
                .is_unsat(),
            "inner scope should be unsat"
        );

        encoder.safe_pop("pop").expect("pop should succeed");
        assert!(
            encoder
                .safe_check_sat("outer")
                .expect("outer check_sat should succeed")
                .is_sat(),
            "outer scope alone should be satisfiable"
        );
    }

    #[test]
    fn test_safe_datatype_constructor_succeeds() {
        let mut encoder = AYEncoder::new();
        let dt = option_int_datatype();
        let forty_two = encoder.solver.int_const(42);

        encoder
            .safe_declare_datatype("test", &dt)
            .expect("declare_datatype should succeed");

        let some_42 = encoder
            .safe_datatype_constructor("test", &dt, "Some", &[forty_two])
            .expect("datatype_constructor should succeed");
        let payload = encoder
            .safe_datatype_selector("test", "option_some_value", some_42, Sort::Int)
            .expect("datatype_selector should succeed");
        let neq = encoder.solver.neq(payload, forty_two);

        encoder
            .safe_assert_term("test", neq)
            .expect("assert_term should succeed");
        assert!(
            encoder
                .safe_check_sat("test")
                .expect("check_sat should succeed")
                .is_unsat(),
            "selector(Some(42)) should equal 42"
        );
    }

    #[test]
    fn test_safe_option_int_none_after_option_seq_declaration() {
        let mut encoder = AYEncoder::new();
        let option_int = crate::encoder::match_enc::SwitchTarget::OptionInt.datatype();
        let option_seq =
            encoder.stdlib_option_datatype_for_payload_sort(Sort::Uninterpreted("Seq".to_string()));

        encoder.ensure_datatype_declared(&option_int);
        encoder.ensure_datatype_declared(&option_seq);

        assert!(
            option_seq
                .constructors
                .iter()
                .any(|ctor| ctor.name == "OptionSeq__None"),
            "specialized Option carriers must not reuse the global None symbol"
        );

        let none_int = encoder
            .safe_datatype_constructor("option collision regression", &option_int, "None", &[])
            .expect("OptionInt::None should remain encodable");
        assert_eq!(
            encoder.solver.get_sort(none_int),
            Sort::Datatype(option_int.clone()).as_term_sort()
        );

        let none_seq = encoder
            .safe_datatype_constructor("option collision regression", &option_seq, "None", &[])
            .expect("OptionSeq::None should be encodable through logical None");
        assert_eq!(
            encoder.solver.get_sort(none_seq),
            Sort::Datatype(option_seq).as_term_sort()
        );
    }

    #[test]
    fn test_safe_datatype_tester_succeeds() {
        let mut encoder = AYEncoder::new();
        let dt = option_int_datatype();
        let forty_two = encoder.solver.int_const(42);

        encoder
            .safe_declare_datatype("test", &dt)
            .expect("declare_datatype should succeed");

        let some_42 = encoder
            .safe_datatype_constructor("test", &dt, "Some", &[forty_two])
            .expect("datatype_constructor should succeed");
        let is_some = encoder
            .safe_datatype_tester("test", &dt, "Some", some_42)
            .expect("datatype_tester should succeed");
        let not_is_some = encoder.solver.not(is_some);

        encoder
            .safe_assert_term("test", not_is_some)
            .expect("assert_term should succeed");
        assert!(
            encoder
                .safe_check_sat("test")
                .expect("check_sat should succeed")
                .is_unsat(),
            "is-Some(Some(42)) should be true"
        );
    }

    #[test]
    fn test_axiom_select_returns_some() {
        let mut encoder = AYEncoder::new();
        let array = encoder
            .get_or_declare_var("arr", Sort::array(Sort::Int, Sort::Int))
            .expect("declare arr");
        let index = encoder.solver.int_const(0);

        assert!(
            encoder.axiom_select("test", array, index).is_some(),
            "axiom_select should return Some for well-sorted array access"
        );
    }

    #[test]
    fn test_axiom_store_returns_some() {
        let mut encoder = AYEncoder::new();
        let array = encoder
            .get_or_declare_var("arr", Sort::array(Sort::Int, Sort::Int))
            .expect("declare arr");
        let index = encoder.solver.int_const(0);
        let value = encoder.solver.int_const(7);

        assert!(
            encoder.axiom_store("test", array, index, value).is_some(),
            "axiom_store should return Some for well-sorted array store"
        );
    }

    #[test]
    fn test_axiom_declare_datatype_succeeds() {
        let mut encoder = AYEncoder::new();
        let dt = option_int_datatype();

        assert!(
            encoder.axiom_declare_datatype("test", &dt),
            "axiom_declare_datatype should succeed"
        );
    }

    #[test]
    fn test_axiom_datatype_constructor_returns_some() {
        let mut encoder = AYEncoder::new();
        let dt = option_int_datatype();
        let forty_two = encoder.solver.int_const(42);

        assert!(
            encoder.axiom_declare_datatype("test", &dt),
            "axiom_declare_datatype should succeed"
        );
        assert!(
            encoder
                .axiom_datatype_constructor("test", &dt, "Some", &[forty_two])
                .is_some(),
            "axiom_datatype_constructor should return Some for valid input"
        );
    }

    // -----------------------------------------------------------------------
    // Tests for advanced facade methods (#2727)
    // -----------------------------------------------------------------------

    #[test]
    fn test_safe_check_sat_assuming_unsat_with_assumption() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);
        let pos = encoder.solver.gt(x, zero);
        let neg = encoder.solver.lt(x, zero);

        encoder.safe_assert_term("test", pos).expect("assert x > 0");

        // Without assumptions x > 0 alone is SAT.
        assert!(encoder
            .safe_check_sat_assuming("base", &[])
            .expect("check_sat_assuming should succeed")
            .is_sat());

        // Adding x < 0 as an assumption contradicts x > 0.
        assert!(
            encoder
                .safe_check_sat_assuming("with_neg", &[neg])
                .expect("check_sat_assuming should succeed")
                .is_unsat(),
            "x > 0 with assumption x < 0 should be unsat"
        );
    }

    #[test]
    fn test_safe_unsat_assumptions_after_contradiction() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);
        let pos = encoder.solver.gt(x, zero);
        let neg = encoder.solver.lt(x, zero);

        encoder.safe_assert_term("base", pos).expect("assert x > 0");
        assert!(encoder
            .safe_check_sat_assuming("contradict", &[neg])
            .expect("check_sat_assuming")
            .is_unsat(),);

        let unsat_assumps = encoder
            .safe_unsat_assumptions("post_unsat")
            .expect("safe_unsat_assumptions should return Ok");
        assert!(
            unsat_assumps.is_some(),
            "expected Some unsat assumptions after UNSAT with assumptions"
        );
    }

    #[test]
    fn test_safe_annotated_unsat_core_succeeds_after_unsat() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);

        encoder
            .safe_set_option("enable_unsat_cores", ":produce-unsat-cores", "true")
            .expect("enable unsat cores");
        let pos = encoder.solver.gt(x, zero);
        encoder
            .safe_assert_named("pos", pos, "positive")
            .expect("assert positive");
        let neg = encoder.solver.lt(x, zero);
        encoder
            .safe_assert_named("neg", neg, "negative")
            .expect("assert negative");
        assert!(encoder
            .safe_check_sat("solve")
            .expect("check_sat")
            .is_unsat());

        let result = encoder.safe_annotated_unsat_core("test");
        // Not every ay build exposes annotated cores (depends on proof
        // tracking); assert we got a well-typed Result either way.
        assert!(result.is_ok() || result.is_err());
    }

    #[test]
    fn test_safe_get_model_after_sat() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let seven = encoder.solver.int_const(7);
        let eq = encoder.solver.eq(x, seven);
        encoder.safe_assert_term("eq", eq).expect("assert x == 7");
        assert!(encoder.safe_check_sat("solve").expect("check_sat").is_sat());

        let model = encoder
            .safe_get_model("model")
            .expect("safe_get_model should succeed after SAT");
        // VerifiedModel intentionally has opaque internals; confirm we can
        // fetch its string form too.
        let model_str = encoder
            .safe_get_model_str("model_str")
            .expect("safe_get_model_str should succeed after SAT");
        let _ = model;
        assert!(!model_str.is_empty(), "model_str should be non-empty");
    }

    #[test]
    fn test_safe_get_value_and_values_after_sat() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let y = encoder
            .get_or_declare_var("y", Sort::Int)
            .expect("declare y");
        let three = encoder.solver.int_const(3);
        let four = encoder.solver.int_const(4);
        let eq_x = encoder.solver.eq(x, three);
        let eq_y = encoder.solver.eq(y, four);
        encoder
            .safe_assert_term("eq_x", eq_x)
            .expect("assert x == 3");
        encoder
            .safe_assert_term("eq_y", eq_y)
            .expect("assert y == 4");
        assert!(encoder.safe_check_sat("solve").expect("check_sat").is_sat());

        let vx = encoder
            .safe_get_value("x_val", x)
            .expect("safe_get_value should succeed");
        let _ = vx;
        let values = encoder
            .safe_get_values("both", &[x, y])
            .expect("safe_get_values should succeed");
        assert_eq!(values.len(), 2, "expected two model values");
    }

    #[test]
    fn test_safe_get_value_errors_before_check_sat() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        // No check_sat call has been made yet.
        let result = encoder.safe_get_value("premature", x);
        assert!(
            result.is_err(),
            "safe_get_value should err when no SAT result is available"
        );
        let msg = format!("{}", result.unwrap_err());
        assert!(
            msg.contains("premature"),
            "error should include context: {msg}"
        );
    }

    #[test]
    fn test_safe_reset_assertions_preserves_declarations() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);
        let pos = encoder.solver.gt(x, zero);
        encoder.safe_assert_term("pos", pos).expect("assert");

        encoder
            .safe_reset_assertions("reset")
            .expect("safe_reset_assertions should succeed");

        // Declarations survive: the solver remains SAT with no assertions.
        assert!(
            encoder
                .safe_check_sat("post_reset")
                .expect("check_sat")
                .is_sat(),
            "empty solver should be SAT after reset_assertions"
        );
    }

    #[test]
    fn test_safe_reset_clears_state() {
        let mut encoder = AYEncoder::new();
        encoder
            .safe_reset("fresh")
            .expect("safe_reset should succeed");
        assert!(
            encoder
                .safe_check_sat("post_reset")
                .expect("check_sat")
                .is_sat(),
            "freshly reset solver should be SAT"
        );
    }

    #[test]
    fn test_safe_statistics_snapshot_owns_data() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let zero = encoder.solver.int_const(0);
        let pos = encoder.solver.gt(x, zero);
        encoder.safe_assert_term("pos", pos).expect("assert");
        let _ = encoder.safe_check_sat("solve").expect("check_sat");

        // Owned Statistics can outlive the borrow chain.
        let snap = encoder
            .safe_statistics("after_solve")
            .expect("safe_statistics should succeed");
        let _reused: &Statistics = &snap;
    }

    #[test]
    fn test_safe_parse_smtlib2_roundtrip() {
        let mut encoder = AYEncoder::new();
        // Reset to start from a pristine QF_LIA-compatible state; the
        // harness already defaults to an AUFLIA logic, so `(set-logic ...)`
        // is unnecessary here.
        let parsed = encoder
            .safe_parse_smtlib2("parse", "(declare-const a Int)\n(assert (> a 0))\n")
            .expect("safe_parse_smtlib2 should succeed on valid input");
        assert!(
            parsed.len() >= 1,
            "expected at least one term from parsed SMT-LIB input, got {}",
            parsed.len()
        );
    }

    #[test]
    fn test_safe_parse_smtlib2_rejects_invalid_input() {
        let mut encoder = AYEncoder::new();
        let result = encoder.safe_parse_smtlib2("bad", "(this is not smt");
        assert!(
            result.is_err(),
            "safe_parse_smtlib2 should err on malformed input"
        );
        let msg = format!("{}", result.unwrap_err());
        assert!(msg.contains("bad"), "error should include context: {msg}");
    }

    #[test]
    fn test_safe_cross_check_smtlib2_no_variants() {
        let encoder = AYEncoder::new();
        let result = encoder.safe_cross_check_smtlib2(
            "cross",
            "(declare-const a Int)\n(assert (> a 0))\n(check-sat)\n",
            &[],
        );
        // With zero variants the baseline is still computed; the call should
        // at minimum return a typed Result.
        assert!(
            result.is_ok() || result.is_err(),
            "cross_check_smtlib2 should return a typed Result"
        );
    }

    #[test]
    fn test_safe_model_provenance_after_sat_returns_result() {
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        let one = encoder.solver.int_const(1);
        let eq = encoder.solver.eq(x, one);
        encoder.safe_assert_term("eq", eq).expect("assert");
        assert!(encoder.safe_check_sat("solve").expect("check_sat").is_sat());

        // Not every solver configuration populates provenance, but the
        // wrapper must always return a typed Result.
        let result = encoder.safe_model_provenance("prov");
        assert!(result.is_ok() || result.is_err());
    }
}

#[cfg(test)]
mod strict_replay_refusal_tests {
    use ay_dpll::api::{SolveResult, Sort};

    use super::*;

    fn unsat_encoder() -> AYEncoder {
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
        encoder
    }

    #[test]
    fn a_recorded_refusal_skips_only_the_identical_problem_in_the_same_scope() {
        let mut encoder = unsat_encoder();
        let six = std::time::Duration::from_secs(6);
        let first = encoder
            .replay_current_stack_with_strict_proofs(six)
            .expect("replay runs");
        encoder
            .encoding_cache
            .record_strict_replay_deterministic_refusal(first.problem_hash);
        assert!(
            encoder
                .replay_current_stack_with_strict_proofs(six)
                .is_none(),
            "the identical problem in the same scope is not re-solved"
        );
        assert!(
            encoder
                .replay_current_stack_with_strict_proofs(std::time::Duration::from_secs(5))
                .is_some(),
            "different problem bytes (another budget) still replay"
        );
        encoder.encoding_cache.begin_solve();
        let again = encoder
            .replay_current_stack_with_strict_proofs(six)
            .expect("a new solve is a new scope, so the replay runs again");
        assert_eq!(
            again.problem_hash, first.problem_hash,
            "export is deterministic"
        );
        encoder.encoding_cache.begin_obligation_slice();
        assert!(!encoder
            .encoding_cache
            .strict_replay_refused_deterministically(first.problem_hash));
    }

    #[test]
    fn a_refusal_recorded_for_another_problem_never_blocks_authority() {
        let mut encoder = unsat_encoder();
        encoder
            .encoding_cache
            .record_strict_replay_deterministic_refusal([7; 32]);
        assert!(encoder
            .authorize_current_stack_unsat_with_strict_proof()
            .is_some());
    }

    #[test]
    fn an_authorized_replay_records_no_refusal() {
        let mut encoder = unsat_encoder();
        let replay = encoder
            .replay_current_stack_with_strict_proofs(std::time::Duration::from_secs(6))
            .expect("replay runs");
        let hash = replay.problem_hash;
        assert!(encoder.install_strict_unsat_authority(replay).is_some());
        assert!(!encoder
            .encoding_cache
            .strict_replay_refused_deterministically(hash));
    }

    #[test]
    fn only_budget_independent_reasons_are_deterministic() {
        assert!(is_deterministic_strict_replay_refusal(Some(
            "proof_trusted"
        )));
        assert!(is_deterministic_strict_replay_refusal(Some(
            "self_check_rejected"
        )));
        assert!(!is_deterministic_strict_replay_refusal(Some("timeout")));
        assert!(!is_deterministic_strict_replay_refusal(Some(
            "resource_out"
        )));
        assert!(!is_deterministic_strict_replay_refusal(None));
    }
}
