// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native request/result API for tRust-style bundle verification.
//!
//! This module is intentionally backend-neutral. It defines the shape of a
//! bundle verification request, the per-obligation result surface, and
//! fail-closed aggregation rules. The default [`FailClosedBundleVerifier`]
//! remains conservative, while [`NativeTrustWpBundleVerifier`] covers the first
//! replayable trust-wp-owned pure-predicate fragment.

mod claim;
mod engine;
mod metadata;
mod proof;
mod result;
mod trust_formula;
mod trust_tmir;
mod types;

/// Stable schema tag for the first trust-wp-owned tRust bundle API.
pub const VERIFY_BUNDLE_API_VERSION: &str = "trust-wp.verify-bundle.v1";

/// Stable schema tag for proof evidence envelopes.
pub const PROOF_EVIDENCE_SCHEMA_VERSION: &str = "trust-wp.proof-evidence.v1";

/// Wire prefix for canonical proof evidence serialization.
pub const PROOF_EVIDENCE_WIRE_PREFIX: &str = "TRUST_WP_PROOF_EVIDENCE:v1";

/// Stable schema tag for the native trust-wp pure-predicate replay format.
// Trust: `trust_wp.` (underscore) — matching every sibling schema
// (`trust_wp.proof-evidence.v1`, `trust_wp.trust-formula.v1`, ...) and the
// compiler-side adapter's expectation; the previous hyphenated spelling made
// the adapter reject otherwise-valid native-pure-replay evidence (2 ny-cert
// postconditions stuck at Unknown on a string mismatch).
pub const TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION: &str = "trust_wp.native-pure-replay.v1";

/// Stable schema tag for aggregate verify-bundle proof manifests.
pub const TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION: &str =
    "trust-wp.verify-bundle-aggregate.v1";

/// Stable schema tag for structured tRust TrustFormulaV1 claim payloads.
pub const TRUST_FORMULA_CLAIM_SCHEMA_VERSION: &str = "trust-wp.trust-formula.v1";

/// Required schema prefix for native tMIR origin metadata
/// (`tmir.native-verification-bundle.v{N}`).
// Trust: the STRICT fail-closed native-origin validation in
// `validate_tmir_native_origin_metadata` (placeholder-solver rejection,
// atom-binding checks, lineage/digest requirements) only engages for origin
// schemas carrying this exact prefix. Producers MUST build their schema tag
// from this constant: the historical drifts (`trust_ir.` rename artifact and
// `trust-ir.` in trust-wp-lib) silently bypassed the whole gate.
pub const TMIR_NATIVE_ORIGIN_SCHEMA_PREFIX: &str = "tmir.native-verification-bundle.";

pub use claim::{native_predicate_for_obligation, NativeBundlePredicate, NativeClaimFormat};
pub use engine::{FailClosedBundleVerifier, NativeTrustWpBundleVerifier, VerifyBundleEngine};
pub use metadata::{
    TrustWpMetadataEntry, TrustWpNativeReplayEvidenceInput, TrustWpNativeReplayMetadataError,
    TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
    TRUST_WP_NATIVE_REPLAY_METADATA_KEY, TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
    TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY, TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
    TRUST_WP_PROOF_CONTEXT_METADATA_KEY, TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
    TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
};
pub use proof::{
    create_native_pure_replay_evidence, create_native_pure_replay_result,
    replay_native_pure_evidence, replay_verify_bundle_result_evidence, ProofReplayError,
};
pub use result::{
    BundleDiagnostic, BundleDiagnosticSeverity, BundleEvidenceMetadata, BundleObligationResult,
    BundleObligationStatus, BundleResultMetadata, BundleSolverMetadata, EvidenceArtifact,
    EvidenceArtifactBytes, EvidenceArtifactBytesEncoding, EvidenceArtifactKind, ProofEvidence,
    ProofEvidenceFormat, ProofEvidenceWireError, ProofStrength, VerifyBundleResult,
    VerifyBundleStatus,
};
pub use trust_formula::{decode_trust_formula_v1_claim, TrustFormulaDecodeError};
pub use trust_tmir::{
    compile_trust_tmir_proof_call_vcs, trust_tmir_to_verify_bundle,
    trust_tmir_to_verify_bundle_with_budget, TrustTmirAdapterBudget, TrustTmirAdapterError,
    TrustTmirAdapterMetrics, TrustTmirBinOp, TrustTmirBinding, TrustTmirBundle, TrustTmirExpr,
    TrustTmirFormula, TrustTmirObligation, TrustTmirProofCall, TrustTmirSort, TrustTmirUnaryOp,
    TRUST_TMIR_ADAPTER_SCHEMA_VERSION,
};
pub use types::{
    BundleClaim, BundleClaimFormat, BundleDigest, BundleNativeOrigin, BundleNativeReplayIdentity,
    BundleNativeToolIdentity, BundleNativeVerificationMode, BundleObligation, BundleObligationKind,
    BundleObligationMetadata, BundleProducer, BundleProofAtom, BundleProofAtomRole,
    BundleProofContext, BundleSourceSpan, BundleSummaryFact, BundleSummaryFactKind, BundleTarget,
    BundleTmirCompilerFactKind, BundleTmirCompilerFactRef, BundleTmirObligationCause,
    BundleTmirObligationSource, BundleTmirSourceSpan, VerifyBundleOptions, VerifyBundleRequest,
};

#[cfg(test)]
mod tests;
