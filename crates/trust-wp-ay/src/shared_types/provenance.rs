// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification provenance metadata for caching, reproducibility, and
//! determinism tracking.
//!
//! [`VerificationProvenance`] captures the solver state and configuration
//! at the time of a verification result, enabling:
//! - **Caching**: skip re-verification when VC hash + solver config unchanged
//! - **Reproducibility**: record exact solver state for debugging flaky results
//! - **Determinism tracking**: same VC + same config = same result
//!
//! Part of the ay deep integration roadmap (#2712, #2729).

use std::time::Duration;

use super::solve_types::{
    ProofAssertSliceCertificate, SolveEvidenceSnapshot, SolveStatisticsSnapshot,
    StrictProofReplayObservation, UnknownReason,
};

/// Provenance metadata attached to verification results.
///
/// Every ay introspection result flows through this structured type so that
/// tRust (and other consumers) can access solver state programmatically.
///
/// # Caching
///
/// When `vc_hash` and `solver_config_hash` are both non-zero, a consumer can
/// skip re-verification if a cached result exists with matching hashes.
///
/// # Reproducibility
///
/// The `random_seed` and `solver_timeout_ms` fields record the exact solver
/// configuration used, so flaky results can be reproduced by replaying with
/// the same configuration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct VerificationProvenance {
    /// SHA-256 hash of the verification condition (assertion set).
    ///
    /// When two verification runs produce the same `vc_hash` with the same
    /// solver configuration, the result should be identical (determinism).
    /// Zero-filled when hashing is not yet implemented.
    pub vc_hash: [u8; 32],

    /// Wall-clock time spent in the solver for this verification.
    pub solve_time: Duration,

    /// Number of assertions sent to the solver.
    pub assertion_count: u64,

    /// Configured solver timeout in milliseconds, if any.
    pub solver_timeout_ms: Option<u64>,

    /// Random seed used by the solver, if explicitly set.
    pub random_seed: Option<u64>,

    /// Solver statistics snapshot from the last `check_sat` call.
    pub solver_statistics: Option<SolveStatisticsSnapshot>,

    /// Full solve evidence from ay-dpll's atomic `SolveDetails` envelope.
    pub solve_evidence: Option<SolveEvidenceSnapshot>,

    /// Structured reason for an Unknown result from the same solve call.
    pub unknown_reason: Option<UnknownReason>,

    /// Executor error detail captured from the same solve call.
    pub executor_error: Option<String>,

    /// Stable-text replay artifact for the solver-facing trace, when captured.
    pub replay_artifact: Option<String>,

    /// Native AY replay JSON for the active solver state, when captured.
    ///
    /// This is the reducer-facing artifact produced by ay-dpll itself. It is
    /// distinct from `replay_artifact`, which is trust-wp's stable-text trace.
    pub native_replay_json: Option<String>,

    /// Ordered strict proof-authority certificates for `proof_assert` slices.
    pub proof_assert_slice_certificates: Vec<ProofAssertSliceCertificate>,

    /// What the strict proof-producing replay MEASURED, when one ran.
    ///
    /// Diagnostics only — see [`StrictProofReplayObservation`] for why this is a
    /// separate field rather than an overwrite of `solve_evidence` /
    /// `solver_statistics`. Read this, not those, when asking "did ay build a
    /// derivation for this obligation?": on lanes where the long-lived
    /// incremental encoder supplied the pair, those two report the encoder's
    /// proof-production CONFIGURATION (`Trusted` / `false`) rather than any
    /// measurement of ay.
    ///
    /// `None` means no strict replay ran on this obligation — it never means
    /// "no proof was built".
    pub strict_proof_replay: Option<StrictProofReplayObservation>,

    /// How many strict-replay observations were refused because they belonged to
    /// a DIFFERENT obligation slice than the one this provenance reports.
    ///
    /// `strict_proof_replay = None` with a non-zero count here means "a strict
    /// replay ran nearby, but not on this obligation" — a materially different
    /// statement from "no strict replay ran" (count zero). Keeping the two apart
    /// is the point: reporting a sibling slice's accepted certificate on a
    /// blocked obligation is what manufactured a phantom "certified but blocked"
    /// class. Diagnostics only.
    pub strict_proof_replay_unbound: u32,
}

impl VerificationProvenance {
    /// Create a provenance record with only the solve time filled in.
    ///
    /// Other fields default to zero/None. Use the builder-style setters
    /// to populate additional fields.
    #[must_use]
    pub fn with_solve_time(solve_time: Duration) -> Self {
        Self {
            vc_hash: [0u8; 32],
            solve_time,
            assertion_count: 0,
            solver_timeout_ms: None,
            random_seed: None,
            solver_statistics: None,
            solve_evidence: None,
            unknown_reason: None,
            executor_error: None,
            replay_artifact: None,
            native_replay_json: None,
            proof_assert_slice_certificates: Vec::new(),
            strict_proof_replay: None,
            strict_proof_replay_unbound: 0,
        }
    }

    /// Set the assertion count.
    #[must_use]
    pub fn with_assertion_count(mut self, count: u64) -> Self {
        self.assertion_count = count;
        self
    }

    /// Set the solver timeout.
    #[must_use]
    pub fn with_solver_timeout(mut self, timeout: Option<Duration>) -> Self {
        self.solver_timeout_ms = timeout.map(|d| d.as_millis() as u64);
        self
    }

    /// Set the random seed.
    #[must_use]
    pub fn with_random_seed(mut self, seed: Option<u64>) -> Self {
        self.random_seed = seed;
        self
    }

    /// Set the solver statistics snapshot.
    #[must_use]
    pub fn with_solver_statistics(mut self, stats: Option<SolveStatisticsSnapshot>) -> Self {
        self.solver_statistics = stats;
        self
    }

    /// Set the full solve evidence snapshot.
    #[must_use]
    pub fn with_solve_evidence(mut self, evidence: Option<SolveEvidenceSnapshot>) -> Self {
        self.solve_evidence = evidence;
        self
    }

    /// Set the structured unknown reason.
    #[must_use]
    pub fn with_unknown_reason(mut self, reason: Option<UnknownReason>) -> Self {
        self.unknown_reason = reason;
        self
    }

    /// Set the executor error detail.
    #[must_use]
    pub fn with_executor_error(mut self, error: Option<String>) -> Self {
        self.executor_error = error;
        self
    }

    /// Set the stable replay artifact text.
    #[must_use]
    pub fn with_replay_artifact(mut self, replay_artifact: Option<String>) -> Self {
        self.replay_artifact = replay_artifact;
        self
    }

    /// Set the native AY replay JSON artifact.
    #[must_use]
    pub fn with_native_replay_json(mut self, native_replay_json: Option<String>) -> Self {
        self.native_replay_json = native_replay_json;
        self
    }

    /// Set the ordered proof-assert slice certificates.
    #[must_use]
    pub fn with_proof_assert_slice_certificates(
        mut self,
        certificates: Vec<ProofAssertSliceCertificate>,
    ) -> Self {
        self.proof_assert_slice_certificates = certificates;
        self
    }

    /// Set the strict proof-producing replay's observation.
    ///
    /// Diagnostics only: nothing on the verdict, gate, or acceptance path reads
    /// this field.
    #[must_use]
    pub fn with_strict_proof_replay(
        mut self,
        observation: Option<StrictProofReplayObservation>,
    ) -> Self {
        self.strict_proof_replay = observation;
        self
    }

    /// Set the count of strict-replay observations refused for scope mismatch.
    ///
    /// Diagnostics only: nothing on the verdict, gate, or acceptance path reads
    /// this field.
    #[must_use]
    pub fn with_strict_proof_replay_unbound(mut self, unbound: u32) -> Self {
        self.strict_proof_replay_unbound = unbound;
        self
    }

    /// Set the VC hash.
    #[must_use]
    pub fn with_vc_hash(mut self, hash: [u8; 32]) -> Self {
        self.vc_hash = hash;
        self
    }
}

impl Default for VerificationProvenance {
    fn default() -> Self {
        Self {
            vc_hash: [0u8; 32],
            solve_time: Duration::ZERO,
            assertion_count: 0,
            solver_timeout_ms: None,
            random_seed: None,
            solver_statistics: None,
            solve_evidence: None,
            unknown_reason: None,
            executor_error: None,
            replay_artifact: None,
            native_replay_json: None,
            proof_assert_slice_certificates: Vec::new(),
            strict_proof_replay: None,
            strict_proof_replay_unbound: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_provenance_default_has_zero_fields() {
        let prov = VerificationProvenance::default();
        assert_eq!(prov.vc_hash, [0u8; 32]);
        assert_eq!(prov.solve_time, Duration::ZERO);
        assert_eq!(prov.assertion_count, 0);
        assert!(prov.solver_timeout_ms.is_none());
        assert!(prov.random_seed.is_none());
        assert!(prov.solver_statistics.is_none());
        assert!(prov.solve_evidence.is_none());
        assert!(prov.unknown_reason.is_none());
        assert!(prov.executor_error.is_none());
        assert!(prov.replay_artifact.is_none());
        assert!(prov.native_replay_json.is_none());
        assert!(prov.proof_assert_slice_certificates.is_empty());
    }

    #[test]
    fn test_provenance_with_solve_time() {
        let prov = VerificationProvenance::with_solve_time(Duration::from_millis(42));
        assert_eq!(prov.solve_time, Duration::from_millis(42));
        assert_eq!(prov.assertion_count, 0);
    }

    #[test]
    fn test_provenance_builder_chain() {
        let stats = SolveStatisticsSnapshot {
            decisions: 10,
            conflicts: 2,
            propagations: 50,
            ..Default::default()
        };
        let prov = VerificationProvenance::with_solve_time(Duration::from_secs(1))
            .with_assertion_count(42)
            .with_solver_timeout(Some(Duration::from_mins(1)))
            .with_random_seed(Some(12345))
            .with_solver_statistics(Some(stats.clone()))
            .with_unknown_reason(Some(UnknownReason::Timeout))
            .with_executor_error(Some("executor detail".to_string()))
            .with_replay_artifact(Some("schema=trust-wp-ay-replay-artifact-v1\n".to_string()))
            .with_native_replay_json(Some("{\"schema\":\"ay.native-replay.v1\"}".to_string()))
            .with_vc_hash([0xAB; 32]);

        assert_eq!(prov.solve_time, Duration::from_secs(1));
        assert_eq!(prov.assertion_count, 42);
        assert_eq!(prov.solver_timeout_ms, Some(60_000));
        assert_eq!(prov.random_seed, Some(12345));
        assert_eq!(prov.solver_statistics, Some(stats));
        assert_eq!(prov.unknown_reason, Some(UnknownReason::Timeout));
        assert_eq!(prov.executor_error.as_deref(), Some("executor detail"));
        assert_eq!(
            prov.replay_artifact.as_deref(),
            Some("schema=trust-wp-ay-replay-artifact-v1\n")
        );
        assert_eq!(
            prov.native_replay_json.as_deref(),
            Some("{\"schema\":\"ay.native-replay.v1\"}")
        );
        assert_eq!(prov.vc_hash, [0xAB; 32]);
    }

    #[test]
    fn test_provenance_clone_eq() {
        let prov = VerificationProvenance::with_solve_time(Duration::from_millis(100))
            .with_assertion_count(10);
        let cloned = prov.clone();
        assert_eq!(prov, cloned);
    }

    #[test]
    fn test_provenance_debug_format() {
        let prov = VerificationProvenance::default();
        let debug = format!("{prov:?}");
        assert!(debug.contains("VerificationProvenance"));
        assert!(debug.contains("vc_hash"));
        assert!(debug.contains("solve_time"));
    }

    #[test]
    fn test_provenance_with_solver_timeout_none() {
        let prov =
            VerificationProvenance::with_solve_time(Duration::ZERO).with_solver_timeout(None);
        assert!(prov.solver_timeout_ms.is_none());
    }
}
