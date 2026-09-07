// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared solver types used by both `encoder` and `verify` modules.
//!
//! These types were moved from `verify/types/mod.rs` to break the
//! encoder→verify bidirectional coupling (#2655). Both modules import
//! from this shared location instead of the encoder depending on verify.

use std::{fmt::Write as _, time::Duration};

/// Canonical AY replay metadata for one proof-assert obligation slice.
///
/// Claim identity is carried inside the exact replay artifact passed to AY,
/// rather than merely beside its content hash in a downstream certificate.
#[must_use]
pub fn proof_assert_native_replay_metadata(
    ordinal: u64,
    prepared_claim_hash: [u8; 32],
    normalized_claim_hash: [u8; 32],
) -> ay_dpll::api::NativeReplayMetadata {
    fn write_hex(output: &mut String, bytes: &[u8; 32]) {
        for byte in bytes {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
        }
    }

    let mut note = "trust-wp.proof-assert-slice-binding.v1;consumer=trust-wp;\
         obligation=proof_assert;ordinal="
        .to_string();
    write!(note, "{ordinal};prepared_sha256=").expect("writing to a String cannot fail");
    write_hex(&mut note, &prepared_claim_hash);
    note.push_str(";normalized_sha256=");
    write_hex(&mut note, &normalized_claim_hash);

    let mut metadata = ay_dpll::api::NativeReplayMetadata::default();
    metadata.consumer = Some("trust-wp".to_string());
    metadata.obligation_kind = Some("proof_assert".to_string());
    metadata.notes = Some(note);
    metadata
}

/// Bounded snapshot of ay-dpll solver statistics captured from a single
/// `check_sat_with_details()` call.
///
/// Maps from ay-dpll's `Statistics` without carrying non-integer
/// `BTreeMap<String, StatValue>` entries, keeping trust-wp's public API
/// independent of ay-dpll's extensible statistics value type while preserving
/// the counters needed to reduce and diagnose solver failures. (#2639)
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveStatisticsSnapshot {
    pub decisions: u64,
    pub conflicts: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub theory_conflicts: u64,
    pub theory_propagations: u64,
    pub theory_unknown_count: u64,
    pub partial_clause_count: u64,
    pub model_validation_skips: u64,
    pub model_validation_failures: u64,
    pub proof_clause_count: u64,
    pub proof_complete: bool,
    pub ematching_rounds_completed: u64,
    pub ematching_instances_created: u64,
    pub term_bytes: u64,
    pub term_count: u64,
    pub refinement_count: u64,
    pub rlimit_count: u64,
    pub num_vars: u64,
    pub num_clauses: u64,
    pub num_assertions: u64,
    pub extra_ints: Vec<(String, u64)>,
}

impl From<&ay_dpll::Statistics> for SolveStatisticsSnapshot {
    fn from(stats: &ay_dpll::Statistics) -> Self {
        Self {
            decisions: stats.decisions,
            conflicts: stats.conflicts,
            propagations: stats.propagations,
            restarts: stats.restarts,
            theory_conflicts: stats.theory_conflicts,
            theory_propagations: stats.theory_propagations,
            theory_unknown_count: stats.theory_unknown_count,
            partial_clause_count: stats.partial_clause_count,
            model_validation_skips: stats.model_validation_skips,
            model_validation_failures: stats.model_validation_failures,
            proof_clause_count: stats.proof_clause_count,
            proof_complete: stats.proof_complete,
            ematching_rounds_completed: stats.ematching_rounds_completed,
            ematching_instances_created: stats.ematching_instances_created,
            term_bytes: stats.term_bytes,
            term_count: stats.term_count,
            refinement_count: stats.refinement_count,
            rlimit_count: stats.rlimit_count,
            num_vars: stats.num_vars,
            num_clauses: stats.num_clauses,
            num_assertions: stats.num_assertions,
            extra_ints: stats
                .extra
                .iter()
                .filter_map(|(key, value)| match value {
                    ay_dpll::StatValue::Int(int_value) => Some((key.clone(), *int_value)),
                    _ => None,
                })
                .collect(),
        }
    }
}

/// Solver verification summary copied out of ay-dpll's solve envelope.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveVerificationSnapshot {
    pub sat_model_validated: bool,
    pub unsat_proof_available: bool,
    pub unsat_proof_checker_failures: u64,
    pub sat_independent_checks: u64,
    pub sat_delegated_checks: u64,
    pub sat_incomplete_checks: u64,
}

impl From<ay_dpll::VerificationSummary> for SolveVerificationSnapshot {
    fn from(summary: ay_dpll::VerificationSummary) -> Self {
        Self {
            sat_model_validated: summary.sat_model_validated,
            unsat_proof_available: summary.unsat_proof_available,
            unsat_proof_checker_failures: summary.unsat_proof_checker_failures,
            sat_independent_checks: summary.sat_independent_checks,
            sat_delegated_checks: summary.sat_delegated_checks,
            sat_incomplete_checks: summary.sat_incomplete_checks,
        }
    }
}

/// Trust level applied by ay-dpll while producing a solve result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolveVerificationLevelSnapshot {
    Trusted,
    DebugChecked,
    ProofChecked,
    FullyVerified,
    Unknown,
}

impl From<ay_dpll::VerificationLevel> for SolveVerificationLevelSnapshot {
    fn from(level: ay_dpll::VerificationLevel) -> Self {
        match level {
            ay_dpll::VerificationLevel::Trusted => Self::Trusted,
            ay_dpll::VerificationLevel::DebugChecked => Self::DebugChecked,
            ay_dpll::VerificationLevel::ProofChecked => Self::ProofChecked,
            ay_dpll::VerificationLevel::FullyVerified => Self::FullyVerified,
            _ => Self::Unknown,
        }
    }
}

/// Caller-set limit that ay-dpll reported for an Unknown result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolveLimitKindSnapshot {
    Timeout,
    MemoryLimit,
    TermMemoryLimit,
    LearnedClauseLimit,
    ClauseDbBytesLimit,
    Interrupted,
    Unknown,
}

impl From<ay_dpll::LimitKind> for SolveLimitKindSnapshot {
    fn from(kind: ay_dpll::LimitKind) -> Self {
        match kind {
            ay_dpll::LimitKind::Timeout => Self::Timeout,
            ay_dpll::LimitKind::MemoryLimit => Self::MemoryLimit,
            ay_dpll::LimitKind::TermMemoryLimit => Self::TermMemoryLimit,
            ay_dpll::LimitKind::LearnedClauseLimit => Self::LearnedClauseLimit,
            ay_dpll::LimitKind::ClauseDbBytesLimit => Self::ClauseDbBytesLimit,
            ay_dpll::LimitKind::Interrupted => Self::Interrupted,
            _ => Self::Unknown,
        }
    }
}

/// Resource counters copied out of ay-dpll's solve envelope.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveResourceSnapshot {
    pub rss_bytes: u64,
    pub term_bytes: u64,
    pub term_count: u64,
    pub learned_clause_count: u64,
    pub wall_time_ms: u64,
    pub limit_hit: Option<SolveLimitKindSnapshot>,
}

impl From<&ay_dpll::ResourceUsage> for SolveResourceSnapshot {
    fn from(usage: &ay_dpll::ResourceUsage) -> Self {
        Self {
            rss_bytes: usage.rss_bytes as u64,
            term_bytes: usage.term_bytes as u64,
            term_count: usage.term_count as u64,
            learned_clause_count: usage.learned_clause_count as u64,
            wall_time_ms: duration_to_millis(usage.wall_time),
            limit_hit: usage.limit_hit.map(SolveLimitKindSnapshot::from),
        }
    }
}

/// Full solve evidence retained from ay-dpll's atomic `SolveDetails` envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveEvidenceSnapshot {
    pub result: String,
    pub model_validated: bool,
    pub accepted_for_consumer: bool,
    pub consumer_rejection: Option<String>,
    pub verification: SolveVerificationSnapshot,
    pub verification_level: SolveVerificationLevelSnapshot,
    pub resource_usage: SolveResourceSnapshot,
}

impl SolveEvidenceSnapshot {
    pub fn from_solve_details(details: &ay_dpll::SolveDetails) -> Self {
        let acceptance = details.accept_for_consumer();
        Self {
            result: details.result.to_string(),
            model_validated: details.result.was_model_validated(),
            accepted_for_consumer: acceptance.is_ok(),
            consumer_rejection: acceptance.err().map(|err| err.to_string()),
            verification: SolveVerificationSnapshot::from(details.verification),
            verification_level: SolveVerificationLevelSnapshot::from(details.verification_level),
            resource_usage: SolveResourceSnapshot::from(&details.resource_usage),
        }
    }
}

/// What the STRICT, proof-producing replay actually MEASURED — recorded whether
/// or not it went on to clear the proof-authority bar.
///
/// # Why this exists (it is an instrument, not a verdict)
///
/// The long-lived incremental encoder is deliberately built with
/// `set_produce_proofs(false)` (`encoder/constructors.rs`, intentional, #2629)
/// and never calls `set_verification_level`. Its `SolveDetails` therefore report
/// `verification_level = Trusted` and `unsat_proof_available = false` as
/// **constants for every query**, whatever the proof machinery did — ay's own
/// `VerificationSummary::unsat_proof_available` docs call this out as a
/// presentation flag, not a statement about whether a derivation could be built.
///
/// On the `Unknown(ProofTrusted)` lane — the certification-blocked case a
/// proof-authority census most needs to see — the strict replay's own
/// `SolveDetails` used to be discarded by `install_strict_unsat_authority` the
/// moment the authority check failed, leaving provenance holding the incremental
/// encoder's constants. Reading those constants as a measurement produced three
/// separate wrong census results ("N obligations have no proof object"): the
/// figure was counting the encoder's configuration, not ay's behaviour. A
/// control replaying a genuine `Unsat` reported `level=Trusted
/// available=false` — indistinguishable from a real refusal.
///
/// This snapshot closes that hole by keeping the replay's measurement. It is
/// populated **iff a strict proof-producing replay actually ran**, so absence is
/// itself honest ("no replay happened here"), never a fabricated `false`.
///
/// # Strictly observation-only
///
/// No gate, predicate, or acceptance path reads this. It is deliberately a
/// SEPARATE field from `VerificationProvenance::solve_evidence` /
/// `solver_statistics` rather than an overwrite of them: that pair is what the
/// mandatory proof-authority boundary judges, and several engine-side consumers
/// (`function::legacy_result_from_outcome`, `loops`, `mut_borrow`,
/// `obligation_slices`) demote a `Verified` outcome to `Unknown` precisely when
/// its `solve_evidence` is not `accepted_for_consumer`. A declined strict replay
/// is by construction not accepted, and on this lane the result is still
/// `Verified(None)` when those predicates run (the `ProofTrusted` demotion
/// happens later, at the driver's `apply_strict_trust` boundary). Overwriting
/// the pair would therefore feed a non-accepted snapshot straight into live
/// demotion predicates and move verdicts. Extending leaves them untouched.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct StrictProofReplayObservation {
    /// Evidence as the strict proof-producing replay reported it.
    pub evidence: SolveEvidenceSnapshot,
    /// Statistics from that same replay, read at the same instant.
    pub statistics: SolveStatisticsSnapshot,
    /// Whether this replay went on to be installed as proof authority. `false`
    /// is the certification-blocked case: ay built a derivation and then refused
    /// to certify it.
    pub authority_accepted: bool,
    /// `ay_dpll::ProofDeclineMechanism::tag()` when ay actively declined to
    /// record a derivation.
    ///
    /// Read it WITH `evidence.verification.unsat_proof_available`, per ay's
    /// documented table: `(true, None)` = proof built and exposed;
    /// `(false, Some(m))` = machinery ran and declined via `m`; `(false, None)`
    /// = proof output was never requested. That last row is exactly the
    /// ambiguity that caused the wrong censuses.
    ///
    /// Expect `None` from us today: ay's decline vocabulary is currently
    /// text/parsed-source-centric (`authored-source-*`,
    /// `preprocessor-fold-to-false`) and does not yet cover the native-API path
    /// this replay uses. Carried for future-proofing — it is not the answer, and
    /// a `None` here must NOT be read as "nothing was declined".
    pub unsat_proof_decline: Option<String>,
    /// `ay_dpll::UnknownReason::code()` for this replay — the stable reason ay
    /// recorded for withholding a verdict.
    ///
    /// # This is the field `unsat_proof_decline` is not
    ///
    /// `unsat_proof_decline` answers "why is there NO derivation" and is
    /// `None` on every native-API solve (its four mechanisms are reachable only
    /// through a parsed-SMT-LIB surface AST this path never builds). Reading
    /// that `None` as "ay refused and recorded no reason" was wrong twice: ay
    /// records an instance-specific reason on *every* withheld solve, on this
    /// same object, in a different field. This carries it.
    ///
    /// Read it WITH `statistics.proof_complete`, because the codes partition a
    /// population that was previously conflated:
    ///
    /// * `self_check_rejected` / `proof_trusted` — a verdict WAS computed and a
    ///   soundness gate took it away. This is the certification-blocked lane.
    /// * `quantifier_*` — no verdict was ever reached, so nothing was withheld
    ///   and no refusal occurred. `checked == total > 0 && holes == 0` does NOT
    ///   exclude this case: those counters can be fully satisfied while
    ///   `proof_complete` is `false`.
    ///
    /// A census keying only on the step counters therefore mixes the two, and
    /// ay's own docs warn twice never to fold `ProofTrusted` or
    /// `SelfCheckRejected` back into `Incomplete` for exactly this reason.
    pub unknown_reason: Option<String>,
    /// `ay_dpll::UnknownDiagnostic::detail` for this replay — the human-readable
    /// detail recorded alongside [`Self::unknown_reason`], e.g. `"computed UNSAT
    /// rejected by mandatory strict certification: step t0 uses unverified trust
    /// rule"`.
    ///
    /// Instance-specific where the reason code is categorical, so this is what
    /// names the offending step. Note it degrades to a static per-reason default
    /// for the terminal-trust exit, which records no diagnostic of its own — a
    /// byte-identical detail across obligations means that exit, not a lost
    /// message.
    pub unknown_detail: Option<String>,
}

/// The authority path used to discharge one retained `proof_assert` slice.
///
/// `NativeEncoded` means the replay artifact contains the encoded negation of
/// the normalized slice. The two derived variants are deliberately narrower:
/// the consumer must independently recover the same fact from the original
/// prepared AST, while the attached AY artifact proves only the trust-free
/// Boolean kernel used to authorize that derivation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofAssertSliceDerivation {
    /// AY checked the native encoding of the normalized obligation slice.
    NativeEncoded,
    /// The original prepared obligation slice is exactly `true`.
    SyntacticTruth,
    /// The original prepared obligation slice exactly equals a precondition.
    ExactPreparedPremise,
}

impl ProofAssertSliceDerivation {
    /// Stable domain-separated tag used by the certificate-set hash.
    #[must_use]
    pub const fn certificate_hash_tag(self) -> &'static [u8] {
        match self {
            Self::NativeEncoded => b"native-encoded",
            Self::SyntacticTruth => b"syntactic-truth",
            Self::ExactPreparedPremise => b"exact-prepared-premise",
        }
    }
}

/// Proof authority retained for one exact `proof_assert` obligation slice.
///
/// A function-level proof assertion can contain several independently solved
/// obligations. Retaining only the final solve would let one sibling slice
/// masquerade as authority for another, so every slice carries its own claim,
/// native problem, evidence, and statistics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ProofAssertSliceCertificate {
    pub ordinal: u64,
    pub derivation: ProofAssertSliceDerivation,
    pub prepared_claim: String,
    pub prepared_claim_hash: [u8; 32],
    pub normalized_claim: String,
    pub normalized_claim_hash: [u8; 32],
    pub native_problem_json: String,
    pub problem_hash: [u8; 32],
    pub solve_evidence: SolveEvidenceSnapshot,
    pub solver_statistics: SolveStatisticsSnapshot,
}

impl ProofAssertSliceCertificate {
    /// Construct an exact per-slice proof-authority certificate.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        ordinal: u64,
        derivation: ProofAssertSliceDerivation,
        prepared_claim: String,
        prepared_claim_hash: [u8; 32],
        normalized_claim: String,
        normalized_claim_hash: [u8; 32],
        native_problem_json: String,
        problem_hash: [u8; 32],
        solve_evidence: SolveEvidenceSnapshot,
        solver_statistics: SolveStatisticsSnapshot,
    ) -> Self {
        Self {
            ordinal,
            derivation,
            prepared_claim,
            prepared_claim_hash,
            normalized_claim,
            normalized_claim_hash,
            native_problem_json,
            problem_hash,
            solve_evidence,
            solver_statistics,
        }
    }
}

fn duration_to_millis(duration: Duration) -> u64 {
    duration.as_millis().try_into().unwrap_or(u64::MAX)
}

/// Typed reason for an `Unknown` verification result.
///
/// Replaces raw `Option<String>` payloads with structured variants so that
/// consumers can match on reason categories without fragile string comparison.
/// Use [`UnknownReason::from_solver_reason`] to parse solver output strings,
/// or [`UnknownReason::from_ay_unknown_reason`] to map directly from ay-dpll's
/// typed enum without lossy string round-tripping. (#2639)
///
/// `VerificationResult::Unknown` holds `UnknownReason` directly (#1751).
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownReason {
    /// Solver exceeded the configured timeout.
    Timeout,
    /// Solver exceeded a deterministic or caller-specified resource budget.
    ResourceOut,
    /// Solver returned "incomplete" — the logic fragment exceeds its decision procedure.
    Incomplete,
    /// Quantifier instantiation could not be resolved by E-matching.
    Quantifiers,
    /// E-matching round budget or per-round instantiation limit exhausted. (#2639)
    QuantifierRoundLimit,
    /// Deferred quantifier instantiations remain that could invalidate the model. (#2639)
    QuantifierDeferred,
    /// Triggerless quantifiers that neither E-matching nor CEGQI could handle. (#2639)
    QuantifierUnhandled,
    /// CEGQI-specific incompleteness. (#2639)
    QuantifierCegqiIncomplete,
    /// E-matching processed an exists quantifier but added instances as
    /// conjunctive assertions — UNSAT from the conjunction is unreliable. (#2639)
    QuantifierEmatchingExistsIncomplete,
    /// Solver found a SAT model for the negated VC but it may be spurious.
    SatModel,
    /// Solver ran out of memory.
    MemoryOut,
    /// Solver was interrupted externally.
    Interrupted,
    /// The query used a feature ay-dpll does not support.
    Unsupported,
    /// The query used arithmetic outside the supported fragment.
    UnsupportedArithmetic,
    /// The query mixed collection and datatype fragments that ay-dpll does
    /// not currently combine.
    UnsupportedMixedCollection,
    /// ay-dpll reported an internal solver error.
    InternalError,
    /// ay-dpll computed a verdict that its fail-closed self-check rejected.
    ///
    /// This is a caught wrong answer, not solver incompleteness or a trusted
    /// proof step, and must remain distinguishable from both.
    SelfCheckRejected,
    /// **Soundness gate (#8759).** An UNSAT verdict was withheld because its
    /// terminal derivation chain is not trust-free — it reaches the empty
    /// clause through an unverified `trust`/`hole` step, or through an `assume`
    /// leaf no problem assertion backs.
    ///
    /// This is a trust-wp-OWNED variant with no counterpart on ay's
    /// `UnknownReason`. It is produced from two places, both of which stayed
    /// live across the ay 0.5 -> 0.6 bump:
    ///
    /// * [`VerificationResult::apply_strict_trust`] — trust-wp's own gate,
    ///   from a [`ProofCertificateSummary`] that is not fully verified.
    /// * [`UnknownReason::from_solver_reason`] — the `ay` driver publishes the
    ///   rejection as the reason string `(incomplete proof-trusted)`.
    ///
    /// It is deliberately NOT reconstructed from ay's typed enum. ay 0.5
    /// declared `ay_dpll::UnknownReason::ProofTrusted` but **never produced
    /// it**: the driver's downgrade (`ay/src/run.rs`) calls
    /// `Executor::reject_last_unsat_as_unknown()`, which installs the generic
    /// `Incomplete` in *both* 0.5 and 0.6, and the distinguishing evidence is
    /// the transcript string, not a typed value. ay 0.6 (66538b006) then
    /// removed the dead variant.
    ///
    /// Do not route `AYReason::SelfCheckRejected` here to "restore" it. That is
    /// ay's mandatory verdict-certification gate: `unsat_cert.rs` routes
    /// trust-kind rejections *away* from it for independent re-discharge, and
    /// it fires on missing-proof / epoch-mismatch / structural failures that
    /// are not trust at all — so it is broader and narrower than this gate at
    /// the same time. (trust-vc's `unknown_category.rs` calls it "`ProofTrusted`
    /// renamed"; that prose is convenient but not what the ay sources show, and
    /// trust-vc's *behaviour* — a non-failure soft Unknown — is unaffected
    /// either way.)
    ///
    /// Control: `tests/strict_proof_trust_gate.rs`.
    ///
    /// [`VerificationResult::apply_strict_trust`]: crate::VerificationResult::apply_strict_trust
    /// [`ProofCertificateSummary`]: crate::ProofCertificateSummary
    ProofTrusted,
    /// Encoding approximation triggered soundness demotion.
    Demoted(String),
    /// Solver panicked internally.
    SolverPanic(String),
    /// Solver returned a reason string not covered by other variants.
    SolverMessage(String),
    /// No reason was provided by the solver.
    Unspecified,
}

impl UnknownReason {
    /// Map directly from ay-dpll's typed `UnknownReason` enum without lossy
    /// string round-tripping. (#2639)
    pub fn from_ay_unknown_reason(reason: &ay_dpll::UnknownReason) -> Self {
        use ay_dpll::UnknownReason as AYReason;
        match reason {
            AYReason::Timeout => Self::Timeout,
            AYReason::ResourceLimit => Self::ResourceOut,
            AYReason::MemoryLimit => Self::MemoryOut,
            AYReason::Interrupted => Self::Interrupted,
            AYReason::Incomplete => Self::Incomplete,
            AYReason::QuantifierRoundLimit => Self::QuantifierRoundLimit,
            AYReason::QuantifierDeferred => Self::QuantifierDeferred,
            AYReason::QuantifierUnhandled => Self::QuantifierUnhandled,
            AYReason::QuantifierCegqiIncomplete => Self::QuantifierCegqiIncomplete,
            AYReason::QuantifierEmatchingExistsIncomplete => {
                Self::QuantifierEmatchingExistsIncomplete
            }
            AYReason::SplitLimit => Self::Incomplete,
            AYReason::ExpressionSplit => Self::Incomplete,
            AYReason::Unsupported => Self::Unsupported,
            AYReason::UnsupportedArithmetic => Self::UnsupportedArithmetic,
            AYReason::UnsupportedMixedCollection => Self::UnsupportedMixedCollection,
            AYReason::InternalError => Self::InternalError,
            AYReason::SelfCheckRejected => Self::SelfCheckRejected,
            AYReason::Unknown => Self::Unspecified,
            // NO ARM FOR THE STRICT-PROOF TRUST GATE, DELIBERATELY.
            // DO NOT "RESTORE" ONE — READ THE RETRY HAZARD BELOW FIRST.
            //
            // History. ay 0.5 had `AYReason::ProofTrusted` with no producer;
            // ay 0.6 deleted it (66538b006); **ay 0.7 restored it, and this
            // time it HAS a producer** — `UnknownOrigin::TerminalTrust =>
            // UnknownReason::ProofTrusted` in ay-dpll's `executor_types`, it is
            // listed in `UnknownReason::ALL`, and ay-dpll's own
            // `strict_proof_terminal_trust_library_gate` tests assert on it.
            // The earlier justification for this missing arm ("never produced,
            // so it never fired") is therefore NO LONGER TRUE and must not be
            // used to reason about it.
            //
            // Why the arm still must not exist. `AYReason::ProofTrusted` means
            // ay computed an UNSAT and its soundness gate WITHHELD it. Mapping
            // it onto `Self::ProofTrusted` would make it satisfy
            // `is_retryable_proof_unknown` (encoder/solver.rs), whose only
            // caller responds by running `retry_check_sat_without_proofs()` —
            // which does `set_produce_proofs(false)` and re-solves. With proof
            // production off, the strict-proof gate cannot fire on the retry,
            // so the very UNSAT ay refused to stand behind comes back clean and
            // lands as `Verified(None)`, i.e. a PASS. The obvious-looking
            // "faithful" mapping is a false-accept path, not a fidelity fix.
            //
            // Falling through to `SolverMessage` keeps the fact (ay's Display
            // is `(incomplete proof-trusted)`) while staying non-retryable,
            // which is the fail-closed direction. This is currently latent
            // besides: trust-wp never enables ay's strict-proof gate, so ay
            // does not hand us this variant today. It is pinned by
            // `ay_proof_trusted_must_not_become_the_retryable_gate_verdict`.
            //
            // The gate reaches trust-wp by the two live paths documented on
            // `Self::ProofTrusted`: `apply_strict_trust` (proof summary) and
            // `from_solver_reason` (the `(incomplete proof-trusted)` string) —
            // neither of which feeds `last_unknown_reason()`, so neither arms
            // the retry.
            // Do NOT route `AYReason::SelfCheckRejected` to `ProofTrusted`:
            // it would widen the gate into unrelated certification failures and
            // narrow it out of the trust-kind ones ay explicitly excludes from
            // that path. See `ay_typed_reasons_never_synthesize_proof_trusted`.
            //
            // ay's UnknownReason is #[non_exhaustive]
            _ => Self::SolverMessage(reason.to_string()),
        }
    }

    /// Parse an optional solver reason string into a typed reason.
    pub fn from_solver_reason(reason: Option<String>) -> Self {
        match reason {
            None => Self::Unspecified,
            Some(s) => match s.as_str() {
                "timeout" => Self::Timeout,
                "resourceout" => Self::ResourceOut,
                "incomplete" => Self::Incomplete,
                "quantifiers" => Self::Quantifiers,
                "sat" => Self::SatModel,
                "memout" => Self::MemoryOut,
                "interrupted" => Self::Interrupted,
                "unsupported" => Self::Unsupported,
                "unsupported-arithmetic" | "(unsupported arithmetic)" => {
                    Self::UnsupportedArithmetic
                }
                "unsupported-mixed-collection" | "(unsupported mixed-collection)" => {
                    Self::UnsupportedMixedCollection
                }
                "internal-error" => Self::InternalError,
                "self-check-rejected" | "(incomplete self-check-rejected)" => {
                    Self::SelfCheckRejected
                }
                "proof-trusted" | "(incomplete proof-trusted)" => Self::ProofTrusted,
                _ => Self::SolverMessage(s),
            },
        }
    }

    /// Parse an optional solver reason string reference into a typed reason.
    pub fn from_solver_reason_ref(reason: Option<&str>) -> Self {
        match reason {
            None => Self::Unspecified,
            Some("timeout") => Self::Timeout,
            Some("resourceout") => Self::ResourceOut,
            Some("incomplete") => Self::Incomplete,
            Some("quantifiers") => Self::Quantifiers,
            Some("sat") => Self::SatModel,
            Some("memout") => Self::MemoryOut,
            Some("interrupted") => Self::Interrupted,
            Some("unsupported") => Self::Unsupported,
            Some("unsupported-arithmetic") | Some("(unsupported arithmetic)") => {
                Self::UnsupportedArithmetic
            }
            Some("unsupported-mixed-collection") | Some("(unsupported mixed-collection)") => {
                Self::UnsupportedMixedCollection
            }
            Some("internal-error") => Self::InternalError,
            Some("self-check-rejected") | Some("(incomplete self-check-rejected)") => {
                Self::SelfCheckRejected
            }
            Some("proof-trusted") | Some("(incomplete proof-trusted)") => Self::ProofTrusted,
            Some(other) => Self::SolverMessage(other.to_string()),
        }
    }

    /// Returns `true` if this reason is any quantifier-related incompleteness.
    pub fn is_quantifier(&self) -> bool {
        matches!(
            self,
            Self::Quantifiers
                | Self::QuantifierRoundLimit
                | Self::QuantifierDeferred
                | Self::QuantifierUnhandled
                | Self::QuantifierCegqiIncomplete
                | Self::QuantifierEmatchingExistsIncomplete
        )
    }

    /// Returns `true` if this is a timeout reason (for retry logic).
    pub fn is_timeout(&self) -> bool {
        matches!(self, Self::Timeout)
    }

    /// Return a human-readable reason string.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Timeout => "timeout",
            Self::ResourceOut => "resourceout",
            Self::Incomplete => "incomplete",
            Self::Quantifiers => "quantifiers",
            Self::QuantifierRoundLimit => "quantifier-round-limit",
            Self::QuantifierDeferred => "quantifier-deferred",
            Self::QuantifierUnhandled => "quantifier-unhandled",
            Self::QuantifierCegqiIncomplete => "quantifier-cegqi-incomplete",
            Self::QuantifierEmatchingExistsIncomplete => "quantifier-ematching-exists-incomplete",
            Self::SatModel => "sat",
            Self::MemoryOut => "memout",
            Self::Interrupted => "interrupted",
            Self::Unsupported => "unsupported",
            Self::UnsupportedArithmetic => "unsupported-arithmetic",
            Self::UnsupportedMixedCollection => "unsupported-mixed-collection",
            Self::InternalError => "internal-error",
            Self::SelfCheckRejected => "self-check-rejected",
            Self::ProofTrusted => "proof-trusted",
            Self::Demoted(detail) => detail.as_str(),
            Self::SolverPanic(detail) => detail.as_str(),
            Self::SolverMessage(msg) => msg.as_str(),
            Self::Unspecified => "unknown",
        }
    }

    /// Convert back to `Option<String>` for compatibility with existing code.
    pub fn to_option_string(&self) -> Option<String> {
        match self {
            Self::Unspecified => None,
            other => Some(other.as_str().to_string()),
        }
    }
}

impl std::fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn statistics_snapshot_preserves_diagnostic_counters() {
        let mut stats = ay_dpll::Statistics::default();
        stats.decisions = 7;
        stats.restarts = 2;
        stats.theory_unknown_count = 3;
        stats.partial_clause_count = 4;
        stats.model_validation_skips = 5;
        stats.model_validation_failures = 6;
        stats.proof_clause_count = 11;
        stats.proof_complete = true;
        stats.ematching_rounds_completed = 13;
        stats.ematching_instances_created = 17;
        stats.term_bytes = 19;
        stats.term_count = 23;
        stats.refinement_count = 29;
        stats.rlimit_count = 31;
        stats.extra.insert(
            "trust-wp.extra.counter".to_string(),
            ay_dpll::StatValue::Int(37),
        );
        stats.extra.insert(
            "trust-wp.extra.label".to_string(),
            ay_dpll::StatValue::String("ignored".to_string()),
        );

        let snapshot = SolveStatisticsSnapshot::from(&stats);

        assert_eq!(snapshot.decisions, 7);
        assert_eq!(snapshot.restarts, 2);
        assert_eq!(snapshot.theory_unknown_count, 3);
        assert_eq!(snapshot.partial_clause_count, 4);
        assert_eq!(snapshot.model_validation_skips, 5);
        assert_eq!(snapshot.model_validation_failures, 6);
        assert_eq!(snapshot.proof_clause_count, 11);
        assert!(snapshot.proof_complete);
        assert_eq!(snapshot.ematching_rounds_completed, 13);
        assert_eq!(snapshot.ematching_instances_created, 17);
        assert_eq!(snapshot.term_bytes, 19);
        assert_eq!(snapshot.term_count, 23);
        assert_eq!(snapshot.refinement_count, 29);
        assert_eq!(snapshot.rlimit_count, 31);
        assert_eq!(
            snapshot.extra_ints,
            vec![("trust-wp.extra.counter".to_string(), 37)]
        );
    }

    #[test]
    fn unknown_reason_maps_ay_structured_reasons() {
        assert_eq!(
            UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::UnsupportedArithmetic),
            UnknownReason::UnsupportedArithmetic
        );
        assert_eq!(
            UnknownReason::from_ay_unknown_reason(
                &ay_dpll::UnknownReason::UnsupportedMixedCollection
            ),
            UnknownReason::UnsupportedMixedCollection
        );
        assert_eq!(
            UnknownReason::from_solver_reason(Some("proof-trusted".to_string())),
            UnknownReason::ProofTrusted
        );
        assert_eq!(
            UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::ResourceLimit),
            UnknownReason::ResourceOut
        );
        assert_eq!(
            UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::SelfCheckRejected),
            UnknownReason::SelfCheckRejected
        );
    }

    /// The strict-proof trust gate does NOT travel on ay's typed enum, and no
    /// ay variant may be silently promoted into [`UnknownReason::ProofTrusted`].
    ///
    /// ay 0.6 removed the (never-produced) `ProofTrusted` variant. The nearest
    /// looking successor, `SelfCheckRejected`, is ay's mandatory
    /// verdict-certification gate — it routes trust-kind rejections away for
    /// independent re-discharge, and covers missing-proof / epoch-mismatch /
    /// structural failures that are not trust at all. Mapping it onto
    /// `ProofTrusted` would widen the gate into unrelated cases and narrow it
    /// out of the cases it exists for, simultaneously.
    ///
    /// The gate's live carriers are asserted in
    /// `tests/strict_proof_trust_gate.rs`.
    #[test]
    fn ay_typed_reasons_never_synthesize_proof_trusted() {
        for reason in [
            ay_dpll::UnknownReason::SelfCheckRejected,
            ay_dpll::UnknownReason::Incomplete,
            ay_dpll::UnknownReason::InternalError,
            ay_dpll::UnknownReason::Unknown,
            ay_dpll::UnknownReason::Unsupported,
        ] {
            let mapped = UnknownReason::from_ay_unknown_reason(&reason);
            assert_ne!(
                mapped,
                UnknownReason::ProofTrusted,
                "ay's `{reason:?}` must not be laundered into the strict-proof \
                 trust-gate verdict; that gate is carried by \
                 `apply_strict_trust` and the `(incomplete proof-trusted)` \
                 reason string, not by ay's typed enum"
            );
        }
    }

    /// ay 0.7 RESTORED `AYReason::ProofTrusted` and gave it a real producer
    /// (`UnknownOrigin::TerminalTrust`), so the 0.6-era reasoning that the
    /// variant "is never produced" no longer holds. This pins that the obvious
    /// follow-up — mapping it onto trust-wp's own `ProofTrusted` — stays out.
    ///
    /// `AYReason::ProofTrusted` means ay computed an UNSAT and WITHHELD it.
    /// trust-wp's `ProofTrusted` is the one reason that satisfies
    /// `is_retryable_proof_unknown`, and its only caller answers by running
    /// `retry_check_sat_without_proofs()` — `set_produce_proofs(false)` plus a
    /// re-solve. With proofs off the strict-proof gate cannot fire, so the
    /// withheld UNSAT returns clean as `Verified(None)`: a PASS on the exact
    /// verdict ay's soundness gate took away. Keep it non-retryable.
    #[test]
    fn ay_proof_trusted_must_not_become_the_retryable_gate_verdict() {
        let mapped = UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::ProofTrusted);

        assert_ne!(
            mapped,
            UnknownReason::ProofTrusted,
            "ay's withheld-UNSAT reason must not be mapped onto trust-wp's \
             `ProofTrusted`: that is the sole reason `is_retryable_proof_unknown` \
             accepts, and the retry disables proof production, which would turn \
             a soundness-gated UNSAT into `Verified(None)`"
        );

        // It must still carry the fact rather than vanish into a generic reason.
        assert_eq!(
            mapped,
            UnknownReason::SolverMessage(ay_dpll::UnknownReason::ProofTrusted.to_string()),
            "the withheld-UNSAT fact must survive as the reason text even though \
             it is deliberately not the typed gate verdict"
        );
    }
}
