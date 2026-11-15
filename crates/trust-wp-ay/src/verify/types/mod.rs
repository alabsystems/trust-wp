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

use std::sync::Arc;

pub use counterexample::{
    Counterexample, CounterexampleType, CounterexampleValue, PostconditionInfo, VarOrigin,
};
pub use loop_result::{LoopVerificationOutcome, LoopVerificationResult};
pub(crate) use request::VerificationBase;
pub use request::{MutBorrowRequest, VerificationRequest};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

// Re-export shared types so existing `crate::verify::ClosureCaptureInfo` paths still resolve.
// CaptureKind is re-exported from lib.rs directly, not from here.
pub(crate) use crate::shared_types::ClosureCaptureInfo;
// Re-export from shared_types to preserve existing `crate::verify::*` import paths.
// The definitions live in `shared_types/solve_types.rs` so the encoder does not depend on `verify` (#2655).
pub use crate::shared_types::{
    ProofAssertSliceCertificate, ProofAssertSliceDerivation, SolveEvidenceSnapshot,
    SolveLimitKindSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
    SolveVerificationLevelSnapshot, SolveVerificationSnapshot, StrictProofReplayObservation,
    UnknownReason, VerificationProvenance,
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

    /// Enforce VERDICT authority at a public verification boundary while
    /// retaining provenance for diagnostics.
    ///
    /// Two gates, one in each direction, and neither may be skipped:
    ///
    /// * a `Verified` must carry a strictly checked proof certificate
    ///   ([`VerificationResult::apply_strict_trust`]);
    /// * a `Failed` must carry a VALIDATED counterexample model
    ///   ([`Self::apply_mandatory_refutation_authority`]).
    ///
    /// The second gate is the newer one. Publishing `FAILED (counterexample)`
    /// for an obligation whose model was never computed or never validated is
    /// the same class of error as publishing `verified` for an obligation whose
    /// proof was never checked: it asserts a fact about the program that
    /// nothing in this run establishes. Both directions fail closed to
    /// `Unknown`, which keeps a non-zero exit.
    #[must_use]
    pub fn apply_mandatory_proof_authority(mut self) -> Self {
        self.result = self.result.apply_strict_trust(true);
        self.apply_mandatory_refutation_authority()
    }

    /// Withhold a `Failed` verdict whose goal set carries a driver-injected
    /// fail-closed `false`.
    ///
    /// The SECOND half of the one rule (the first is
    /// [`Self::apply_mandatory_refutation_authority`]): a refutation is
    /// publishable only when the state the solver found violates a clause
    /// SOMEBODY WROTE. Every extractor lane that cannot model a construct
    /// pushes `PureExpr::Bool(false)` into the obligation set — an unspecified
    /// callee (`handle_opaque_call`), a dropped spec clause, an exhausted walk,
    /// a by-value-parameter loop, an unmodelled loop exit. That marker is
    /// CORRECT and must never be dropped: it makes the VC unprovable by
    /// construction, which is exactly the fail-closed reading. But `false` is
    /// refutable in every model, so the solver always answers SAT, and
    /// publishing that as `FAILED \u{2717} (counterexample)` tells the user
    /// their correct program is broken when the truth is that trust-wp could
    /// not model it.
    ///
    /// Same destination and the same message prefix as the evidence gate, so
    /// there is ONE spelling of "a refutation was withheld here" for
    /// [`is_withheld_refutation`], the wire line, the counters and the #3771
    /// fail-fast to key on. Idempotent and strictly narrowing.
    ///
    /// # What the marker suppresses, and what it does not
    ///
    /// The marker suppresses the refutation it MANUFACTURED, not every
    /// refutation in a function that happens to contain one. A function can
    /// carry an unmodelled call AND a clause its own text violates, and the
    /// user's clause must still refute. The permission is
    /// narrow and fail-closed, and needs BOTH halves:
    ///
    /// * the refuted goal is not itself a marker ([`is_fail_closed_marker`]) —
    ///   a `false` goal is refutable in every model, and one behind path
    ///   guards in every model of the guards, so a SAT answer over one says
    ///   nothing about the program; and
    /// * a structural refutation shape ALSO refuted that goal
    ///   ([`crate::VerificationProvenance::refutation_structural_shape`]): a
    ///   determination read off the clause, the return expression and the
    ///   preconditions, which therefore does not rest on any value trust-wp
    ///   manufactured to stand in for the construct it could not model.
    ///
    /// The same program shape with the unmodelled call's result RETURNED has
    /// its user clause refuted too, by a model that picks an arbitrary value
    /// for that result — no shape fires, and the refutation stays withheld.
    /// That is the case this whole gate exists for (D-27).
    #[must_use]
    pub fn apply_injected_goal_refutation_authority(
        mut self,
        injected_fail_closed_goal: bool,
        goals: &[PureExpr],
    ) -> Self {
        if !injected_fail_closed_goal || !matches!(self.result, VerificationResult::Failed(_)) {
            return self;
        }
        if let Some(shape) = self.refutation_independent_of_injected_goals(goals) {
            crate::verify::authority_trace(|| {
                format!(
                    "injected-goal gate: refutation published, structural shape `{shape}` \
                     refuted a goal somebody wrote"
                )
            });
            return self;
        }
        self.result = VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "{REFUTATION_AUTHORITY_MESSAGE}: {INJECTED_FAIL_CLOSED_GOAL_REASON}"
        )));
        self
    }

    /// The structural refutation shape that makes this `Failed` a statement
    /// about the PROGRAM rather than about a goal trust-wp manufactured, if
    /// there is one. See
    /// [`Self::apply_injected_goal_refutation_authority`] for the rule.
    fn refutation_independent_of_injected_goals(&self, goals: &[PureExpr]) -> Option<&str> {
        let VerificationResult::Failed(counterexample) = &self.result else {
            return None;
        };
        // Which goal did the model violate? Unattributed means unattributable:
        // fail closed.
        let clause_idx = counterexample.violated_postcondition.as_ref()?.clause_idx;
        // A `false` goal is refutable in every model, and one behind path
        // guards in every model of its guards. Whether it was injected or
        // written, a SAT answer over it is not evidence, and the written ones
        // are already subtracted by the caller before the flag is raised.
        if goals.get(clause_idx).is_none_or(is_fail_closed_marker) {
            return None;
        }
        self.provenance
            .as_ref()?
            .refutation_structural_shape
            .as_deref()
    }

    /// Withhold a `Failed` verdict whose violated goal states a type
    /// parameter's invariant.
    ///
    /// `inv_T` is opaque: it has no definition, and the only facts about it
    /// are the premises a caller paid for (D-141). A model that makes it false
    /// on a value refutes the missing fact, not the program — a `T` handed on
    /// from a call result holds `inv_T` in Creusot because every result does,
    /// and trust-wp grants no call result that premise. The refutation is
    /// therefore not published; the obligation stays, so the verdict is
    /// `Unknown` and never `verified`.
    ///
    /// A goal that states no type-parameter invariant keeps its refutation: a
    /// premise `inv_T(t)` is true in every model, so its interpretation
    /// cannot be what falsified a clause that does not mention it. An
    /// unattributed refutation is withheld when ANY goal states one, since it
    /// may be that goal the model broke. Idempotent and strictly narrowing.
    #[must_use]
    pub fn apply_opaque_type_param_goal_refutation_authority(mut self, goals: &[PureExpr]) -> Self {
        let VerificationResult::Failed(counterexample) = &self.result else {
            return self;
        };
        let violated = counterexample
            .violated_postcondition
            .as_ref()
            .and_then(|info| goals.get(info.clause_idx));
        let rests_on_opaque_predicate = match violated {
            Some(goal) => trust_wp_core::logic::mentions_type_param_invariant(goal),
            None => goals
                .iter()
                .any(trust_wp_core::logic::mentions_type_param_invariant),
        };
        if rests_on_opaque_predicate {
            self.result = VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
                "{REFUTATION_AUTHORITY_MESSAGE}: {OPAQUE_TYPE_PARAM_INVARIANT_GOAL_REASON}"
            )));
        }
        self
    }

    /// Withhold a `Failed` verdict that carries no validated counterexample.
    ///
    /// See [`refutation_evidence_gap_reason`] for what counts as one. A verdict
    /// that does not clear the bar becomes
    /// `Unknown(SolverMessage("<REFUTATION_AUTHORITY_MESSAGE>: <reason>"))`;
    /// every other verdict is returned untouched. Idempotent, and strictly
    /// narrowing: it can only remove refutations, never create or widen an
    /// accept.
    #[must_use]
    pub fn apply_mandatory_refutation_authority(mut self) -> Self {
        if let Some(reason) = refutation_evidence_gap_reason(&self) {
            self.result = VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
                "{REFUTATION_AUTHORITY_MESSAGE}: {reason}"
            )));
        }
        self
    }
}

/// Prefix of the `Unknown` reason a withheld refutation carries.
///
/// Stable text: the harness `should_fail` classifier and the campaign triage
/// both key on it to tell "trust-wp reached an honest inconclusive" apart from
/// "trust-wp refuted the program".
pub const REFUTATION_AUTHORITY_MESSAGE: &str = "refutation withheld";

/// Why a refutation over a driver-injected fail-closed goal is not one.
pub const INJECTED_FAIL_CLOSED_GOAL_REASON: &str =
    "goal set carries a fail-closed `false` trust-wp injected for a construct it could not model";

/// Why a refutation of a type parameter's invariant is not one.
pub const OPAQUE_TYPE_PARAM_INVARIANT_GOAL_REASON: &str =
    "the violated goal is a type parameter's \
     invariant, an opaque predicate only a caller's premise establishes";

/// Does this goal set carry a fail-closed `false` obligation that no goal
/// beside it already states ([`unpaired_fail_closed_marker_count`])?
///
/// ONE definition, in the crate that owns the verdict gate, so the driver
/// lanes that pass the flag and the gate that acts on it cannot drift. The
/// marker is spelled `PureExpr::Bool(false)` at every extractor site that
/// fails closed; callers must pass only goals they INJECTED, never a user's
/// own `#[ensures(false)]`, which is a clause the program really can violate.
#[must_use]
pub fn goals_carry_fail_closed_marker(goals: &[PureExpr]) -> bool {
    unpaired_fail_closed_marker_count(goals) > 0
}

/// How many fail-closed `false` markers this goal set carries.
///
/// The count matters because ONE `false` goal is not a marker at all: a body
/// that can never return carries the literal goal "this Abort is unreachable",
/// which Creusot states the same way and which trust-wp really can refute.
/// A caller that injects such a goal subtracts it before asking the question,
/// so an unconditionally panicking body keeps its FAILED.
#[must_use]
pub fn fail_closed_marker_count(goals: &[PureExpr]) -> usize {
    goals
        .iter()
        .filter(|goal| is_fail_closed_marker(goal))
        .count()
}

/// Is this goal a fail-closed marker: the literal `false`, or one behind the
/// path guards an extractor wraps a branch arm's obligations in
/// (`g ==> false`)?
///
/// The guard is the arm's, not a clause anybody wrote about the marker, so it
/// does not make the marker evidence: `g ==> false` is refuted by every model
/// of `g`, and such a model shows only that the construct trust-wp could not
/// model is REACHABLE. A panic arm's own goal is stated as `!g`, never as a
/// guarded `false`, and a callee's written `#[requires(false)]` is counted
/// where it is substituted, before any guard wraps it, so neither is mistaken
/// for one. A marker that sits beside its arm's `!g` restates that goal and is
/// not counted ([`unpaired_fail_closed_marker_count`]).
#[must_use]
pub fn is_fail_closed_marker(goal: &PureExpr) -> bool {
    match goal {
        PureExpr::Bool(false) => true,
        PureExpr::BinOp(_, BinOp::Implies, conclusion) => is_fail_closed_marker(conclusion),
        _ => false,
    }
}

/// How many fail-closed markers this goal set carries that no other goal in
/// it already states.
///
/// A guarded marker `g ==> false` beside the goal `!g` (or `x`, when `g` is
/// `!x`; under the same outer guards when nested) adds no obligation and no
/// model: the two are one formula, and `!g` is a goal of the program — a
/// panic arm's "this arm is unreachable", which Creusot states too. Every
/// model in which the unmodelled construct under `g` runs makes `g` true and
/// so refutes that goal, and every other model never runs the construct; the
/// guard reads only values fixed before the arm, so the construct cannot
/// decide it. A marker is therefore not counted when it is paired, which is
/// what keeps `panic!("msg")` in a reachable arm FAILED: its message lowers
/// through a call with no spec, whose marker sits under the arm's guard beside
/// the arm's own unreachability goal. A marker with no such partner — a bare
/// `false`, or one whose arm goes on — is counted as before.
#[must_use]
pub fn unpaired_fail_closed_marker_count(goals: &[PureExpr]) -> usize {
    goals
        .iter()
        .filter(|goal| {
            is_fail_closed_marker(goal)
                && !unreachability_forms(goal)
                    .iter()
                    .any(|form| goals.contains(form))
        })
        .count()
}

/// The unreachability goals one formula with the guarded marker
/// `g1 ==> .. ==> gk ==> false`: `g1 ==> .. ==> !gk`, and `g1 ==> .. ==> x`
/// when `gk` is `!x`. None for a bare `false`, which has no guard to negate.
fn unreachability_forms(marker: &PureExpr) -> Vec<PureExpr> {
    let PureExpr::BinOp(guard, BinOp::Implies, conclusion) = marker else {
        return Vec::new();
    };
    if matches!(conclusion.as_ref(), PureExpr::Bool(false)) {
        let mut forms = vec![PureExpr::UnOp(UnOp::Not, guard.clone())];
        if let PureExpr::UnOp(UnOp::Not, negated) = guard.as_ref() {
            forms.push(negated.as_ref().clone());
        }
        return forms;
    }
    unreachability_forms(conclusion)
        .into_iter()
        .map(|form| PureExpr::BinOp(guard.clone(), BinOp::Implies, Arc::new(form)))
        .collect()
}

/// Is this the verdict [`VerificationOutcome::apply_mandatory_refutation_authority`]
/// leaves behind when it withholds a refutation?
///
/// One definition of "this rejection was delivered without a validated
/// counterexample", so the wire line, the driver's dispositions and the
/// #3771 fail-fast policy cannot drift apart. NARROW on purpose: an ordinary
/// `Unknown` — a timeout, a vacuity demotion, an incompleteness — is NOT a
/// withheld refutation, and a caller that treats one as a rejection would be
/// crediting an obligation nothing decided.
#[must_use]
pub fn is_withheld_refutation(result: &VerificationResult) -> bool {
    matches!(
        result,
        VerificationResult::Unknown(UnknownReason::SolverMessage(message))
            if message.starts_with(REFUTATION_AUTHORITY_MESSAGE)
    )
}

/// Name the reason a `Failed` outcome carries no VALIDATED counterexample, or
/// `None` when the refutation is backed by one.
///
/// A refutation is honest exactly when the solve that produced it returned a
/// satisfying assignment for the negated obligation, ay VALIDATED that
/// assignment against the assertion set (`model_validated`), and ay's own
/// consumer gate accepted the evidence (`accepted_for_consumer`). Anything
/// else -- no provenance at all, synthesized structural provenance, a shortcut
/// SAT that never ran model validation, or (worse) an `unsat`/`unknown`
/// evidence snapshot under a `Failed` verdict -- is an obligation that was NOT
/// refuted, and saying "counterexample" about it is a false statement.
///
/// This is the mirror of the driver's `verified_evidence_gap_reason`: same
/// shape, opposite verdict. Non-`Failed` results return `None` -- this function
/// judges refutations only.
#[must_use]
pub fn refutation_evidence_gap_reason(outcome: &VerificationOutcome) -> Option<String> {
    if !matches!(outcome.result, VerificationResult::Failed(_)) {
        return None;
    }
    let Some(provenance) = outcome.provenance.as_ref() else {
        return Some("missing solver provenance".to_string());
    };
    let Some(evidence) = provenance.solve_evidence.as_ref() else {
        return Some("missing solver evidence".to_string());
    };
    if !solve_evidence_result_is_sat(&evidence.result) {
        return Some(format!(
            "solver evidence was {}, not a satisfying counterexample model",
            evidence.result
        ));
    }
    if !evidence.model_validated {
        return Some("solver model was never validated".to_string());
    }
    if !evidence.accepted_for_consumer {
        return Some(
            evidence
                .consumer_rejection
                .clone()
                .unwrap_or_else(|| "solver evidence rejected by consumer".to_string()),
        );
    }
    None
}

/// True for a `SolveEvidenceSnapshot::result` string that reports SAT.
///
/// Mirrors the `solve_evidence_result_is_unsat` helpers elsewhere in this
/// crate: ay renders the verdict either as the bare word or as `Sat(..)`.
/// `"unsat"` must not match, which is why this is a prefix/equality test and
/// never a substring one.
pub(crate) fn solve_evidence_result_is_sat(result: &str) -> bool {
    result.eq_ignore_ascii_case("sat")
        || result
            .strip_prefix("Sat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
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
    /// Postcondition assumed correct without SMT proof; the contained string
    /// describes the assumption reason.
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
    /// Callers that drive a per-obligation solver have the clause
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
