// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public types for verification results and counterexamples.
//!
//! - [`VerificationResult`]: Result of a verification attempt (Verified, Failed, Unknown)
//! - [`Counterexample`]: Witness values when verification fails
//! - [`CounterexampleValue`]: Individual value in a counterexample
//! - [`CounterexampleType`]: Type of counterexample (integer, boolean, etc.)
//! - [`VarOrigin`]: Tracks where counterexample variables originated
//! - [`PostconditionInfo`]: Information about violated postconditions
//! - [`LoopVerificationResult`]: Detailed result for loop invariant verification

mod counterexample;
mod loop_result;
mod request;

pub use counterexample::{
    Counterexample, CounterexampleType, CounterexampleValue, PostconditionInfo, VarOrigin,
};
pub use loop_result::{LoopVerificationOutcome, LoopVerificationResult};
pub(crate) use request::VerificationBase;
pub use request::{MutBorrowRequest, VerificationRequest};

// Re-export shared types so existing `crate::verify::ClosureCaptureInfo` paths still resolve.
// CaptureKind is re-exported from lib.rs directly; verify/mod.rs no longer re-exports it.
pub(crate) use crate::shared_types::ClosureCaptureInfo;
// Re-export from shared_types to preserve existing `crate::verify::*` import paths.
// Definitions moved to `shared_types/solve_types.rs` to break encoder→verify coupling (#2655).
pub use crate::shared_types::{
    ProofAssertSliceCertificate, ProofAssertSliceDerivation, SolveEvidenceSnapshot,
    SolveLimitKindSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
    SolveVerificationLevelSnapshot, SolveVerificationSnapshot, UnknownReason,
    VerificationProvenance,
};

/// Complete verification outcome bundling the result with provenance metadata.
///
/// Wraps a [`VerificationResult`] together with optional
/// [`VerificationProvenance`] for caching, reproducibility, and determinism
/// tracking. Consumers that only need the result can destructure or call
/// `.result` directly; consumers that need provenance (e.g., the tRust
/// compiler integration, caching layers) access `.provenance`.
///
/// # Example
///
/// ```text
/// let outcome = VerificationOutcome::new(result, Some(provenance));
/// if matches!(outcome.result, VerificationResult::Verified(_)) {
///     println!("solve time: {:?}", outcome.provenance.map(|p| p.solve_time));
/// }
/// ```
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationOutcome {
    /// The verification result (verified, failed, unknown, assumed).
    pub result: VerificationResult,
    /// Provenance metadata for caching and reproducibility.
    ///
    /// `None` when provenance capture is not enabled or when the result
    /// was produced without invoking the solver (e.g., `Assumed`).
    pub provenance: Option<VerificationProvenance>,
}

impl VerificationOutcome {
    /// Create a new outcome with provenance.
    #[must_use]
    pub fn new(result: VerificationResult, provenance: Option<VerificationProvenance>) -> Self {
        Self { result, provenance }
    }

    /// Create an outcome without provenance (for backward compatibility).
    #[must_use]
    pub fn without_provenance(result: VerificationResult) -> Self {
        Self {
            result,
            provenance: None,
        }
    }

    /// Enforce proof authority at a public verification boundary while
    /// retaining provenance for diagnostics.
    #[must_use]
    pub fn apply_mandatory_proof_authority(mut self) -> Self {
        self.result = self.result.apply_strict_trust(true);
        self
    }
}

/// Summary of proof certificate quality from the ay solver.
///
/// Captures the key quality signals from the solver's UNSAT proof artifact.
/// Used to provide evidence that `VerificationResult::Verified(_)` was backed
/// by a valid proof, and to drive mandatory proof-authority rejection. (#2629)
#[derive(Debug, Clone)]
pub struct ProofCertificateSummary {
    /// Whether strict semantic proof validation succeeded.
    pub strict_verified: bool,
    /// Whether the proof is in the clean-supported subset.
    pub restricted_rule_subset: bool,
    /// Number of trust steps (unverified fallbacks). Zero is ideal.
    pub trust_count: u32,
    /// Number of trust steps with premises (SAT hint reconstruction fallbacks).
    pub trust_fallback_count: u32,
    /// Number of placeholder/incomplete proof steps. Zero is required for
    /// verified authority.
    pub hole_count: u32,
    /// Number of theory lemma steps (treated as axioms by the checker).
    pub theory_lemma_count: u32,
    /// Number of resolution steps (indicates proof complexity).
    pub resolution_count: u32,
    /// Number of Farkas certificates exported for LRA UNSAT lemmas.
    pub farkas_certificate_count: u32,
    /// Whether a serialized LRAT certificate for the SAT backbone is present.
    pub lrat_present: bool,
    /// Rendered Alethe proof text from the solver, when proof production is
    /// enabled and the artifact was successfully exported.
    ///
    /// Captured from `UnsatProofArtifact::alethe`. This is the full
    /// downstream-checkable proof — independent Alethe checkers (e.g. Carcara)
    /// can consume this text to re-verify the UNSAT certificate without
    /// re-running the solver. `None` indicates either proof production was
    /// off or no proof artifact was available.
    pub alethe_text: Option<String>,
}

impl ProofCertificateSummary {
    /// True when the proof has no unverified fallbacks — every step is
    /// semantically validated. Equivalent to ay's strict verdict combined
    /// with the absence of trust/hole steps.
    ///
    /// This intentionally ignores `alethe_text` — the *presence* of rendered
    /// proof text does not change the semantic verdict (e.g. a trusted proof
    /// stays trusted whether or not we captured its textual form). Strict-trust
    /// mode keys off the verdict, not the artifact.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.strict_verified
            && self.trust_count == 0
            && self.trust_fallback_count == 0
            && self.hole_count == 0
    }

    /// Builder: attach the rendered Alethe proof text to the summary.
    ///
    /// Used by tests and by callers that capture the proof after constructing
    /// the summary skeleton. Returns `self` for chaining.
    #[must_use]
    pub fn with_alethe_text(mut self, text: String) -> Self {
        self.alethe_text = Some(text);
        self
    }
}

/// Result of verification attempt
#[derive(Debug, Clone)]
#[non_exhaustive]
#[allow(clippy::large_enum_variant)] // Counterexample is intentionally included for detailed failure info
pub enum VerificationResult {
    /// Postcondition proved to hold.
    ///
    /// Contains optional proof certificate summary when proof production
    /// is enabled and the solver produced a valid proof. (#2629)
    Verified(Option<ProofCertificateSummary>),
    /// Postcondition assumed correct without SMT proof.
    ///
    /// This is returned for axiom-only functions where the postcondition
    /// defines an algebraic property rather than a provable consequence of
    /// the function body. The contained string describes the assumption
    /// reason (e.g., `"axiom-only function: universal postcondition with
    /// trivial body"`).
    ///
    /// Unlike `Verified`, callers should count these separately and report
    /// them as assumptions rather than proven properties. An `Assumed` result
    /// does NOT mean the postcondition is correct — it means the verifier
    /// chose to trust it without proof.
    Assumed(String),
    /// Found counterexample violating postcondition
    Failed(Counterexample),
    /// Solver could not determine result.
    ///
    /// Contains a typed reason describing why the solver returned unknown.
    /// See [`UnknownReason`] for the possible categories.
    Unknown(UnknownReason),
}

impl VerificationResult {
    /// Construct a verified result with no proof certificate.
    pub fn verified() -> Self {
        Self::Verified(None)
    }

    /// Construct a verified result with a proof certificate summary.
    pub fn verified_with_proof(summary: ProofCertificateSummary) -> Self {
        Self::Verified(Some(summary))
    }

    /// Construct an unknown result with a typed reason.
    pub fn unknown(reason: UnknownReason) -> Self {
        Self::Unknown(reason)
    }

    /// Construct an unknown result from an optional solver reason string.
    ///
    /// Convenience wrapper around [`UnknownReason::from_solver_reason`].
    pub fn unknown_from_solver(reason: Option<String>) -> Self {
        Self::Unknown(UnknownReason::from_solver_reason(reason))
    }

    /// Return the unknown reason when this is an Unknown result.
    pub fn unknown_reason(&self) -> Option<&UnknownReason> {
        match self {
            Self::Unknown(reason) => Some(reason),
            _ => None,
        }
    }

    /// Return the unknown reason as a string when this is an Unknown result.
    pub fn unknown_reason_str(&self) -> Option<&str> {
        match self {
            Self::Unknown(reason) => Some(reason.as_str()),
            _ => None,
        }
    }

    /// Attach violated-postcondition metadata to a `Failed` counterexample.
    ///
    /// Phase 8a: callers that drive a per-obligation solver have the clause
    /// text and index already in hand; threading that through every early
    /// return path is brittle, so this consumer-side helper performs the
    /// attachment when (and only when) the result is `Failed` and the
    /// counterexample does not already carry violated-postcondition info.
    /// Calls on `Verified`, `Assumed`, or `Unknown` are no-ops.
    #[must_use]
    pub fn tag_violated_postcondition(mut self, info: PostconditionInfo) -> Self {
        if let Self::Failed(ref mut cex) = self {
            if cex.violated_postcondition.is_none() {
                cex.set_violated_postcondition(info);
            }
        }
        self
    }

    /// Apply the mandatory proof-authority soundness gate.
    ///
    /// A `Verified` result has authority only when it carries a fully replayed
    /// certificate. Missing certificates and certificates containing trust,
    /// holes, or fallback steps are downgraded to
    /// `Unknown(UnknownReason::ProofTrusted)`.
    ///
    /// The boolean argument is retained for source compatibility with callers
    /// that still pass the retired `--[no-]strict-trust` setting. It cannot
    /// disable the gate.
    #[must_use]
    pub fn apply_strict_trust(self, _strict_trust: bool) -> Self {
        match self {
            Self::Verified(None) => Self::Unknown(UnknownReason::ProofTrusted),
            Self::Verified(Some(ref summary)) if !summary.is_fully_verified() => {
                Self::Unknown(UnknownReason::ProofTrusted)
            }
            other => other,
        }
    }
}
