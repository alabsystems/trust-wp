// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant verification result type.
//!
//! [`LoopVerificationResult`] aggregates the five verification conditions
//! for a loop invariant: initialization, preservation, postcondition,
//! and optional variant non-negativity / decrease checks.

use super::{ProofCertificateSummary, UnknownReason, VerificationOutcome, VerificationResult};
use crate::verify::obligation_slices::combine_proof_summaries;

/// Result of loop invariant verification
#[derive(Debug, Clone)]
pub struct LoopVerificationResult {
    /// Initialization check: precondition => invariant
    pub initialization: VerificationResult,
    /// Preservation check: invariant ∧ condition => invariant'
    pub preservation: VerificationResult,
    /// Postcondition check: invariant ∧ ¬condition => postcondition
    pub postcondition: VerificationResult,
    /// Variant non-negative check: invariant ∧ condition => variant >= 0
    /// Only present when variant is provided to `verify_loop_invariant`
    pub variant_nonneg: Option<VerificationResult>,
    /// Variant decrease check: invariant ∧ condition => variant' < variant
    /// Only present when variant is provided to `verify_loop_invariant`
    pub variant_decrease: Option<VerificationResult>,
}

/// Provenance-preserving result of loop invariant verification.
///
/// Mirrors [`LoopVerificationResult`] while retaining per-phase
/// [`VerificationOutcome`] payloads for diagnostics and replay handoff.
#[derive(Debug, Clone)]
pub struct LoopVerificationOutcome {
    /// Initialization check: precondition => invariant.
    pub initialization: VerificationOutcome,
    /// Preservation check: invariant ∧ condition => invariant'.
    pub preservation: VerificationOutcome,
    /// Postcondition check: invariant ∧ ¬condition => postcondition.
    pub postcondition: VerificationOutcome,
    /// Variant non-negative check, when a variant is present.
    pub variant_nonneg: Option<VerificationOutcome>,
    /// Variant decrease check, when a variant is present.
    pub variant_decrease: Option<VerificationOutcome>,
    /// Loop-entry reachability probe used to skip vacuous variant checks.
    pub entry_may_execute: Option<VerificationOutcome>,
}

impl LoopVerificationOutcome {
    /// Enforce certificate-backed authority on every proof-bearing loop phase.
    #[must_use]
    pub fn apply_mandatory_proof_authority(mut self) -> Self {
        self.initialization = self.initialization.apply_mandatory_proof_authority();
        self.preservation = self.preservation.apply_mandatory_proof_authority();
        self.postcondition = self.postcondition.apply_mandatory_proof_authority();
        self.variant_nonneg = self
            .variant_nonneg
            .map(VerificationOutcome::apply_mandatory_proof_authority);
        self.variant_decrease = self
            .variant_decrease
            .map(VerificationOutcome::apply_mandatory_proof_authority);
        self.entry_may_execute = self
            .entry_may_execute
            .map(VerificationOutcome::apply_mandatory_proof_authority);
        self
    }

    /// Drop phase provenance and return the legacy result shape.
    #[must_use]
    pub fn as_result(&self) -> LoopVerificationResult {
        LoopVerificationResult {
            initialization: self.initialization.result.clone(),
            preservation: self.preservation.result.clone(),
            postcondition: self.postcondition.result.clone(),
            variant_nonneg: self
                .variant_nonneg
                .as_ref()
                .map(|outcome| outcome.result.clone()),
            variant_decrease: self
                .variant_decrease
                .as_ref()
                .map(|outcome| outcome.result.clone()),
        }
    }

    /// Returns true if the inductive loop proof passed.
    #[must_use]
    pub fn induction_passed(&self) -> bool {
        self.as_result().induction_passed()
    }

    /// Returns true if all verification conditions passed.
    #[must_use]
    pub fn all_passed(&self) -> bool {
        self.as_result().all_passed()
    }

    /// Returns true only if all conditions were proven.
    #[must_use]
    pub fn all_verified(&self) -> bool {
        self.as_result().all_verified()
    }

    /// Get the overall legacy result.
    #[must_use]
    pub fn overall(&self) -> VerificationResult {
        self.as_result().overall()
    }
}

impl LoopVerificationResult {
    /// Returns true if the inductive loop proof was proven (init +
    /// preservation), ignoring the loop-local postcondition check.
    ///
    /// This is used by the compositional verification path (#2085): when the
    /// induction proof is actually verified but the loop-local postcondition
    /// fails (because the function has post-loop code that the loop-local check
    /// can't see), the driver should continue to the function-level
    /// verification path with loop-exit assumptions injected. Assumed
    /// induction is not sufficient to justify injecting loop-exit assumptions.
    #[must_use]
    pub fn induction_passed(&self) -> bool {
        let init_preservation_passed = matches!(
            (&self.initialization, &self.preservation),
            (
                VerificationResult::Verified(_),
                VerificationResult::Verified(_),
            )
        );

        let variant_passed = match (&self.variant_nonneg, &self.variant_decrease) {
            (Some(nonneg), Some(decrease)) => {
                matches!(nonneg, VerificationResult::Verified(_))
                    && matches!(decrease, VerificationResult::Verified(_))
            }
            (None, None) => true,
            _ => false,
        };

        init_preservation_passed && variant_passed
    }

    /// Returns true if all verification conditions passed (proven or assumed).
    #[must_use]
    pub fn all_passed(&self) -> bool {
        let base_passed = matches!(
            (
                &self.initialization,
                &self.preservation,
                &self.postcondition
            ),
            (
                VerificationResult::Verified(_) | VerificationResult::Assumed(_),
                VerificationResult::Verified(_) | VerificationResult::Assumed(_),
                VerificationResult::Verified(_) | VerificationResult::Assumed(_),
            )
        );

        // Check variant conditions if present
        let variant_passed = match (&self.variant_nonneg, &self.variant_decrease) {
            (Some(nonneg), Some(decrease)) => {
                matches!(
                    nonneg,
                    VerificationResult::Verified(_) | VerificationResult::Assumed(_)
                ) && matches!(
                    decrease,
                    VerificationResult::Verified(_) | VerificationResult::Assumed(_)
                )
            }
            (None, None) => true, // No variant conditions - vacuously verified
            _ => false,           // Inconsistent state - should not happen
        };

        base_passed && variant_passed
    }

    /// Returns true only if all conditions were actually proven (no assumptions).
    #[must_use]
    pub fn all_verified(&self) -> bool {
        let base_verified = matches!(
            (
                &self.initialization,
                &self.preservation,
                &self.postcondition
            ),
            (
                VerificationResult::Verified(_),
                VerificationResult::Verified(_),
                VerificationResult::Verified(_),
            )
        );

        let variant_verified = match (&self.variant_nonneg, &self.variant_decrease) {
            (Some(nonneg), Some(decrease)) => {
                matches!(nonneg, VerificationResult::Verified(_))
                    && matches!(decrease, VerificationResult::Verified(_))
            }
            (None, None) => true,
            _ => false,
        };

        base_verified && variant_verified
    }

    /// Conjunctive proof certificate for the loop as a whole.
    ///
    /// The loop verdict is the CONJUNCTION of its phases, each an independent
    /// obligation discharged by its own solve. The aggregate may therefore
    /// carry proof authority only when every phase carried its own, so this
    /// returns `Some` only when each present phase is
    /// `Verified(Some(summary))` AND that summary is itself fully verified
    /// (`strict_verified`, no trust steps, no trust fallbacks, no holes).
    ///
    /// Any phase that is missing a summary, or carries one with a trust step or
    /// a hole, yields `None` — the aggregate then stays `Verified(None)` and is
    /// demoted to `Unknown(ProofTrusted)` by the mandatory proof-authority gate
    /// exactly as before. This never manufactures authority and never upgrades
    /// a weaker certificate: it only stops discarding authority that every
    /// phase had already established and that the gate had already accepted.
    fn combined_phase_certificate(&self) -> Option<ProofCertificateSummary> {
        let phases: [Option<&VerificationResult>; 5] = [
            Some(&self.initialization),
            Some(&self.preservation),
            Some(&self.postcondition),
            self.variant_nonneg.as_ref(),
            self.variant_decrease.as_ref(),
        ];

        let mut combined: Option<ProofCertificateSummary> = None;
        for phase in phases.into_iter().flatten() {
            let VerificationResult::Verified(Some(summary)) = phase else {
                return None;
            };
            if !summary.is_fully_verified() {
                return None;
            }
            combined = Some(match combined {
                Some(accumulated) => combine_proof_summaries(accumulated, summary.clone()),
                None => summary.clone(),
            });
        }
        combined
    }

    /// Get the overall result - fails if any condition fails
    #[must_use]
    pub fn overall(&self) -> VerificationResult {
        // Check base conditions for failures first (highest precedence)
        if matches!(self.initialization, VerificationResult::Failed(_)) {
            return self.initialization.clone();
        }
        if matches!(self.preservation, VerificationResult::Failed(_)) {
            return self.preservation.clone();
        }
        if matches!(self.postcondition, VerificationResult::Failed(_)) {
            return self.postcondition.clone();
        }

        // Check variant conditions if present
        if let Some(ref nonneg) = self.variant_nonneg {
            if matches!(nonneg, VerificationResult::Failed(_)) {
                return nonneg.clone();
            }
        }
        if let Some(ref decrease) = self.variant_decrease {
            if matches!(decrease, VerificationResult::Failed(_)) {
                return decrease.clone();
            }
        }

        // Asymmetric variant state (one present, one absent) is an internal
        // inconsistency — both checks should be Some or both None.  Fail safe
        // rather than falling through to Verified.
        let variant_asymmetric = matches!(
            (&self.variant_nonneg, &self.variant_decrease),
            (Some(_), None) | (None, Some(_))
        );
        if variant_asymmetric {
            return VerificationResult::Unknown(UnknownReason::SolverMessage(
                "internal bug: inconsistent loop variant state".to_string(),
            ));
        }

        // No failures — check if all truly verified (no assumptions)
        if self.all_verified() {
            // Carry the phases' own certificates instead of discarding them.
            // `combined_phase_certificate` returns `None` unless EVERY phase
            // supplied a fully verified one, so this still fails closed.
            return VerificationResult::Verified(self.combined_phase_certificate());
        }

        // Collect all sub-results for precedence scanning (Unknown > Assumed).
        let all_conditions: [Option<&VerificationResult>; 5] = [
            Some(&self.initialization),
            Some(&self.preservation),
            Some(&self.postcondition),
            self.variant_nonneg.as_ref(),
            self.variant_decrease.as_ref(),
        ];

        // Unknown has next precedence after Failed.
        if let Some(unknown) = all_conditions
            .iter()
            .flatten()
            .find(|r| matches!(r, VerificationResult::Unknown(_)))
        {
            return (*unknown).clone();
        }

        // All passed but some were Assumed — propagate the first Assumed reason
        // instead of silently promoting to Verified (#1889).
        for result in all_conditions.into_iter().flatten() {
            if let VerificationResult::Assumed(reason) = result {
                return VerificationResult::Assumed(reason.clone());
            }
        }

        // Fallback (should not be reachable if all_passed && !all_verified
        // implies some Assumed exists)
        VerificationResult::Verified(None)
    }
}
