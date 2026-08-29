// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct typed tMIR native-bundle consumption for trust-wp requests.
//!
//! This bridge depends on tMIR's `NativeVerificationRequest::TrustWp` variant
//! and `TrustWpVerificationMode` enum instead of adapter-name strings. Formula
//! payload schemas are still honored: trust-wp-owned formulas verify natively,
//! while opaque formulas are preserved into the fail-closed verify-bundle
//! result.

use std::{fmt, fmt::Write};

use serde_json::{Map, Value};
use trust_wp_core::{
    contract_parser::parse_contract,
    formula::{BinOp, PureExpr},
    verify_bundle::{
        BundleNativeOrigin, BundleNativeReplayIdentity, BundleNativeToolIdentity,
        BundleNativeVerificationMode, BundleProofAtom, BundleProofAtomRole, BundleProofContext,
        BundleTmirCompilerFactRef, BundleTmirObligationCause, BundleTmirObligationSource,
        BundleTmirSourceSpan, EvidenceArtifact, EvidenceArtifactKind,
        TMIR_NATIVE_ORIGIN_SCHEMA_PREFIX, TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
    },
};

use crate::{
    verify_bundle, BundleClaim, BundleClaimFormat, BundleDigest, BundleObligation,
    BundleObligationKind, BundleObligationStatus, BundleProducer, BundleSourceSpan, BundleTarget,
    TrustWpLibError, VerifyBundleRequest, VerifyBundleResult, VerifyBundleStatus,
};

/// tMIR formula schema for trust-wp pure-expression claims.
pub const TRUST_WP_PURE_EXPR_FORMULA_SCHEMA_VERSION: &str = "trust-wp.pure-expr.v1";
const TRUST_WP_EXPECTED_VERIFIER_NAME: &str = "trust-wp";

/// Error returned before native trust-wp verification can run.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TrustIrNativeBundleError {
    /// The tMIR bundle failed its own structural validation.
    #[error("tMIR native bundle validation failed: {errors:?}")]
    InvalidNativeBundle { errors: Vec<String> },

    /// No typed trust-wp requests were present.
    #[error("tMIR native bundle contains no trust-wp requests")]
    NoTrustWpRequests,

    /// This trust-wp mode is not implemented by the direct native replay path.
    #[error("tMIR trust-wp request {request_id} uses unsupported mode `{mode}`: {reason}")]
    UnsupportedTrustWpMode {
        request_id: u32,
        mode: TrustIrTrustWpMode,
        reason: TrustIrUnsupportedModeReason,
    },

    /// The selected lineage root does not anchor the current tMIR module.
    #[error(
        "tMIR trust-wp request {request_id} lineage root {lineage_root_id} targets {found}, expected current tMIR module digest {expected}"
    )]
    MismatchedLineageRootDigest {
        request_id: u32,
        lineage_root_id: u32,
        expected: BundleDigest,
        found: BundleDigest,
    },

    /// The request referenced a function missing from the tMIR module.
    #[error("tMIR trust-wp request {request_id} references missing function {function_id}")]
    MissingFunction { request_id: u32, function_id: u32 },

    /// The request referenced an obligation missing from the tMIR module.
    #[error("tMIR trust-wp request {request_id} references missing obligation {obligation_id}")]
    MissingObligation { request_id: u32, obligation_id: u32 },

    /// The request referenced an obligation without a verifier-facing formula.
    #[error("tMIR trust-wp request {request_id} obligation {obligation_id} has no formula")]
    MissingFormula { request_id: u32, obligation_id: u32 },

    /// The request referenced an obligation without compiler source metadata.
    #[error(
        "tMIR trust-wp request {request_id} obligation {obligation_id} has no tMIR obligation source"
    )]
    MissingObligationSource { request_id: u32, obligation_id: u32 },

    /// The obligation source map omits the trust-wp request function binding.
    #[error(
        "tMIR trust-wp request {request_id} obligation {obligation_id} has no source function binding for request function {expected_function_id}"
    )]
    MissingObligationSourceFunction {
        request_id: u32,
        obligation_id: u32,
        expected_function_id: u32,
    },

    /// The obligation source map disagrees with the trust-wp request function.
    #[error(
        "tMIR trust-wp request {request_id} obligation {obligation_id} source maps function {found_function_id}, expected request function {expected_function_id}"
    )]
    MismatchedObligationSourceFunction {
        request_id: u32,
        obligation_id: u32,
        expected_function_id: u32,
        found_function_id: u32,
    },

    /// The obligation source map omits a typed source span for replay evidence.
    #[error(
        "tMIR trust-wp request {request_id} obligation {obligation_id} has no typed source span"
    )]
    MissingObligationSourceSpan { request_id: u32, obligation_id: u32 },

    /// The obligation source cause disagrees with the verifier-facing obligation kind.
    #[error(
        "tMIR trust-wp request {request_id} obligation {obligation_id} source cause `{source_cause}` does not match obligation kind `{obligation_kind}`"
    )]
    MismatchedObligationSourceCause {
        request_id: u32,
        obligation_id: u32,
        obligation_kind: &'static str,
        source_cause: &'static str,
    },

    /// The obligation source names a monomorphization without digest-bound fact evidence.
    #[error(
        "tMIR trust-wp request {request_id} obligation {obligation_id} monomorphization {monomorphization_id} is not bound by a matching compiler fact digest"
    )]
    MissingDigestBoundMonomorphizationFact {
        request_id: u32,
        obligation_id: u32,
        monomorphization_id: u32,
    },

    /// The request expected a verifier other than trust-wp.
    #[error(
        "tMIR trust-wp request {request_id} expected verifier identity `{found}`, expected `{expected}`"
    )]
    MismatchedExpectedVerifierIdentity {
        request_id: u32,
        expected: &'static str,
        found: String,
    },

    /// A trust-wp request did not declare any solver/prover identities.
    #[error("tMIR trust-wp request {request_id} contains no solver identities")]
    MissingSolverIdentities { request_id: u32 },

    /// A trust-wp request carried an empty placeholder solver identity.
    #[error("tMIR trust-wp request {request_id} solver identity {solver_index} is empty")]
    EmptySolverIdentity {
        request_id: u32,
        solver_index: usize,
    },

    /// A trust-wp request did not carry a native replay identity.
    #[error("tMIR trust-wp request {request_id} contains no native replay identity")]
    MissingReplayIdentity { request_id: u32 },

    /// A trust-wp request carried an incomplete native replay identity.
    #[error("tMIR trust-wp request {request_id} native replay identity field `{field}` is empty")]
    EmptyReplayIdentity {
        request_id: u32,
        field: &'static str,
    },

    /// A trust-wp request did not bind replay to a transcript digest.
    #[error("tMIR trust-wp request {request_id} contains no native replay transcript digest")]
    MissingReplayTranscriptDigest { request_id: u32 },

    /// trust-wp produced a verified result that could not be recorded as typed
    /// tMIR native evidence.
    #[error("tMIR trust-wp request {request_id} response evidence is invalid: {reason}")]
    InvalidResponseEvidence { request_id: u32, reason: String },
}

/// Typed tMIR trust-wp mode preserved in fail-closed diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustIrTrustWpMode {
    WeakestPrecondition,
    StrongestPostcondition,
    Abduction,
}

impl TrustIrTrustWpMode {
    const fn as_str(self) -> &'static str {
        match self {
            Self::WeakestPrecondition => "weakest_precondition",
            Self::StrongestPostcondition => "strongest_postcondition",
            Self::Abduction => "abduction",
        }
    }
}

impl fmt::Display for TrustIrTrustWpMode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// Typed reason why a tMIR trust-wp mode cannot enter native replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustIrUnsupportedModeReason {
    RequiresSynthesizerResult,
}

impl fmt::Display for TrustIrUnsupportedModeReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RequiresSynthesizerResult => formatter.write_str(
                "mode requires a typed synthesizer result, not replay-only proof evidence",
            ),
        }
    }
}

/// Convert every typed tMIR trust-wp request into trust-wp verify-bundle requests.
///
/// trust-vc and trust-mc requests are ignored. Each trust-wp request becomes one
/// [`VerifyBundleRequest`] whose obligations preserve the referenced tMIR proof
/// payload schemas. Opaque schemas are intentionally carried through as
/// fail-closed native verifier input rather than routed through adapter names.
/// Weakest-precondition and strongest-postcondition modes both consume already
/// lowered proof obligations. Abduction remains unsupported because it needs a
/// distinct synthesizer result shape, not a replay-only verifier result.
pub fn trust_ir_native_bundle_to_verify_requests(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<Vec<VerifyBundleRequest>, TrustIrNativeBundleError> {
    validate_tmir_bundle(bundle)?;

    let mut requests = Vec::new();
    for native_request in &bundle.requests {
        if let trust_ir::NativeVerificationRequest::TrustWp(trust_wp_request) = native_request {
            requests.push(tmir_trust_wp_request_to_verify_bundle(
                bundle,
                native_request,
                trust_wp_request,
            )?);
        }
    }

    if requests.is_empty() {
        return Err(TrustIrNativeBundleError::NoTrustWpRequests);
    }

    Ok(requests)
}

/// Verify all typed trust-wp requests in a tMIR native verification bundle.
///
/// The returned vector preserves tMIR request order after filtering to trust-wp
/// variants. Individual verify-bundle results remain fail-closed: unsupported
/// or opaque obligations return `Invalid` or `Unsupported` rather than success.
pub fn verify_trust_ir_native_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<Vec<VerifyBundleResult>, TrustWpLibError> {
    let requests = trust_ir_native_bundle_to_verify_requests(bundle)?;
    Ok(requests.into_iter().map(verify_bundle).collect())
}

/// trust-wp verification results plus typed tMIR response evidence.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct TrustIrNativeVerificationEvidenceOutput {
    pub results: Vec<VerifyBundleResult>,
    pub evidence_bundles: Vec<trust_ir::NativeEvidenceBundle>,
    pub artifact_attachments: Vec<trust_ir::NativeEvidenceArtifactAttachment>,
}

/// Verify all typed trust-wp requests and emit tMIR-native evidence descriptors
/// plus digest-checked artifact byte attachments for verified results.
///
/// Failed, unknown, unsupported, or invalid trust-wp results are returned as
/// fail-closed [`VerifyBundleResult`] values and do not receive fabricated
/// native evidence bundles.
pub fn verify_trust_ir_native_bundle_with_evidence(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<TrustIrNativeVerificationEvidenceOutput, TrustWpLibError> {
    let verify_requests = trust_ir_native_bundle_to_verify_requests(bundle)?;
    let native_requests = bundle
        .requests
        .iter()
        .filter(|request| matches!(request, trust_ir::NativeVerificationRequest::TrustWp(_)))
        .collect::<Vec<_>>();

    let mut results = Vec::with_capacity(verify_requests.len());
    let mut evidence_bundles = Vec::new();
    let mut artifact_attachments = Vec::new();

    for (native_request, verify_request) in native_requests.into_iter().zip(verify_requests) {
        let result = verify_bundle(verify_request);
        if result.status == VerifyBundleStatus::Verified {
            let (evidence_bundle, attachments) =
                tmir_response_evidence_for_result(bundle, native_request, &result)?;
            evidence_bundles.push(evidence_bundle);
            artifact_attachments.extend(attachments);
        }
        results.push(result);
    }

    Ok(TrustIrNativeVerificationEvidenceOutput {
        results,
        evidence_bundles,
        artifact_attachments,
    })
}

/// Verify typed trust-wp requests and record the resulting native evidence
/// descriptors into the supplied tMIR bundle.
///
/// The returned sidecar attachments carry the concrete bytes for the recorded
/// descriptors; tMIR keeps those bytes out of the bundle itself and resolves
/// them by request/kind/digest.
pub fn verify_trust_ir_native_bundle_and_record_evidence(
    bundle: &mut trust_ir::NativeVerificationBundle,
) -> Result<TrustIrNativeVerificationEvidenceOutput, TrustWpLibError> {
    let output = verify_trust_ir_native_bundle_with_evidence(bundle)?;
    let recorded_requests = output
        .evidence_bundles
        .iter()
        .map(trust_ir::NativeEvidenceBundle::request)
        .collect::<std::collections::BTreeSet<_>>();
    bundle
        .evidence_bundles
        .retain(|evidence| !recorded_requests.contains(&evidence.request()));
    bundle
        .evidence_bundles
        .extend(output.evidence_bundles.iter().cloned());
    Ok(output)
}

fn tmir_response_evidence_for_result(
    bundle: &trust_ir::NativeVerificationBundle,
    native_request: &trust_ir::NativeVerificationRequest,
    result: &VerifyBundleResult,
) -> Result<
    (
        trust_ir::NativeEvidenceBundle,
        Vec<trust_ir::NativeEvidenceArtifactAttachment>,
    ),
    TrustIrNativeBundleError,
> {
    let request_id = native_request.id();
    let mode = trust_wp_mode_for_native_request(native_request);
    let mut artifacts = Vec::new();
    let mut attachments = Vec::new();

    for obligation_result in &result.obligation_results {
        let BundleObligationStatus::Verified { evidence } = &obligation_result.status else {
            continue;
        };
        push_tmir_response_artifacts(
            request_id,
            mode,
            &result.bundle_id,
            &obligation_result.obligation_id,
            evidence,
            &mut artifacts,
            &mut attachments,
        )?;
    }

    if let Some(aggregate_evidence) = &result.aggregate_evidence {
        push_tmir_response_artifacts(
            request_id,
            mode,
            &result.bundle_id,
            "aggregate",
            aggregate_evidence,
            &mut artifacts,
            &mut attachments,
        )?;
    }

    bundle
        .evidence_bundle_for_request(native_request, artifacts)
        .map(|evidence_bundle| (evidence_bundle, attachments))
        .map_err(|err| TrustIrNativeBundleError::InvalidResponseEvidence {
            request_id: request_id.index(),
            reason: err.to_string(),
        })
}

fn push_tmir_response_artifacts(
    request_id: trust_ir::NativeRequestId,
    mode: trust_ir::TrustWpVerificationMode,
    bundle_id: &str,
    obligation_id: &str,
    evidence: &crate::ProofEvidence,
    artifacts: &mut Vec<trust_ir::NativeEvidenceArtifact>,
    attachments: &mut Vec<trust_ir::NativeEvidenceArtifactAttachment>,
) -> Result<(), TrustIrNativeBundleError> {
    for (artifact_index, artifact) in evidence.artifacts.iter().enumerate() {
        let bytes = checked_artifact_bytes(request_id, artifact)?;
        let declared_digest = proof_digest_from_bundle_digest(request_id, &artifact.digest)?;
        let actual_digest = trust_ir::NativeEvidenceArtifactAttachment::digest_for_bytes(
            trust_ir::ProofDigestAlgorithm::Sha256,
            &bytes,
        );
        if declared_digest != actual_digest {
            return Err(TrustIrNativeBundleError::InvalidResponseEvidence {
                request_id: request_id.index(),
                reason: format!(
                    "artifact `{}` digest {} does not match actual byte digest {}",
                    artifact.id, declared_digest, actual_digest
                ),
            });
        }

        let kind = tmir_response_artifact_kind(mode, &artifact.kind);
        if artifacts
            .iter()
            .any(|existing| existing.kind == kind && existing.digest == actual_digest)
        {
            continue;
        }

        let name = tmir_response_artifact_name(
            request_id,
            obligation_id,
            artifact_index,
            kind,
            actual_digest,
        );
        let native_artifact = trust_ir::NativeEvidenceArtifact::new(name, kind, actual_digest);
        let source_identity = format!(
            "trust-wp://verify-bundle/{bundle_id}/{obligation_id}/{}",
            artifact.kind.as_str()
        );
        attachments.push(trust_ir::NativeEvidenceArtifactAttachment::for_artifact(
            request_id,
            trust_ir::NativeVerifierSuite::TrustWp,
            &native_artifact,
            source_identity,
            bytes,
        ));
        artifacts.push(native_artifact);
    }

    Ok(())
}

fn checked_artifact_bytes(
    request_id: trust_ir::NativeRequestId,
    artifact: &EvidenceArtifact,
) -> Result<Vec<u8>, TrustIrNativeBundleError> {
    let inline_bytes = artifact.inline_bytes.as_ref().ok_or_else(|| {
        TrustIrNativeBundleError::InvalidResponseEvidence {
            request_id: request_id.index(),
            reason: format!(
                "artifact `{}` has no concrete inline bytes for native evidence attachment",
                artifact.id
            ),
        }
    })?;

    inline_bytes
        .decoded_bytes()
        .map_err(|err| TrustIrNativeBundleError::InvalidResponseEvidence {
            request_id: request_id.index(),
            reason: format!("artifact `{}` bytes are invalid: {err}", artifact.id),
        })
}

fn proof_digest_from_bundle_digest(
    request_id: trust_ir::NativeRequestId,
    digest: &BundleDigest,
) -> Result<trust_ir::ProofDigest, TrustIrNativeBundleError> {
    if digest.algorithm != "sha256" {
        return Err(TrustIrNativeBundleError::InvalidResponseEvidence {
            request_id: request_id.index(),
            reason: format!(
                "artifact digest algorithm `{}` is not supported for tMIR response evidence",
                digest.algorithm
            ),
        });
    }

    let bytes = decode_sha256_hex(request_id, &digest.value)?;
    Ok(trust_ir::ProofDigest::sha256(bytes))
}

fn decode_sha256_hex(
    request_id: trust_ir::NativeRequestId,
    value: &str,
) -> Result<[u8; 32], TrustIrNativeBundleError> {
    if value.len() != 64 {
        return Err(TrustIrNativeBundleError::InvalidResponseEvidence {
            request_id: request_id.index(),
            reason: format!("artifact digest `{value}` is not 64 hex characters"),
        });
    }

    let mut bytes = [0_u8; 32];
    for (index, chunk) in value.as_bytes().chunks_exact(2).enumerate() {
        let high = decode_hex_nibble(chunk[0]).ok_or_else(|| {
            TrustIrNativeBundleError::InvalidResponseEvidence {
                request_id: request_id.index(),
                reason: format!("artifact digest `{value}` contains non-hex bytes"),
            }
        })?;
        let low = decode_hex_nibble(chunk[1]).ok_or_else(|| {
            TrustIrNativeBundleError::InvalidResponseEvidence {
                request_id: request_id.index(),
                reason: format!("artifact digest `{value}` contains non-hex bytes"),
            }
        })?;
        bytes[index] = (high << 4) | low;
    }
    Ok(bytes)
}

const fn decode_hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn trust_wp_mode_for_native_request(
    native_request: &trust_ir::NativeVerificationRequest,
) -> trust_ir::TrustWpVerificationMode {
    let trust_ir::NativeVerificationRequest::TrustWp(request) = native_request else {
        unreachable!("caller filtered to trust-wp native requests");
    };
    request.mode
}

fn tmir_response_artifact_kind(
    mode: trust_ir::TrustWpVerificationMode,
    kind: &EvidenceArtifactKind,
) -> trust_ir::NativeEvidenceArtifactKind {
    match kind {
        EvidenceArtifactKind::NormalizedObligation => {
            trust_ir::NativeEvidenceArtifactKind::TrustWpVerificationCondition
        }
        EvidenceArtifactKind::ReplayLog
            if mode == trust_ir::TrustWpVerificationMode::StrongestPostcondition =>
        {
            trust_ir::NativeEvidenceArtifactKind::TrustWpReplayTrace
        }
        EvidenceArtifactKind::ReplayLog | EvidenceArtifactKind::SolverTranscript => {
            trust_ir::NativeEvidenceArtifactKind::ReplayTranscript
        }
        EvidenceArtifactKind::SummaryEvidence => {
            trust_ir::NativeEvidenceArtifactKind::BackendCapabilityMetadata
        }
        EvidenceArtifactKind::RequestDigest
        | EvidenceArtifactKind::AggregateProofManifest
        | EvidenceArtifactKind::ProofCertificate
        | EvidenceArtifactKind::Counterexample
        | EvidenceArtifactKind::Model
        | EvidenceArtifactKind::DiagnosticTrace => trust_ir::NativeEvidenceArtifactKind::Other,
        _ => trust_ir::NativeEvidenceArtifactKind::Other,
    }
}

fn tmir_response_artifact_name(
    request_id: trust_ir::NativeRequestId,
    obligation_id: &str,
    artifact_index: usize,
    kind: trust_ir::NativeEvidenceArtifactKind,
    digest: trust_ir::ProofDigest,
) -> String {
    let digest_hex = tmir_digest_hex(digest);
    format!(
        "trust-wp-r{}-{}-{}-{}-{}",
        request_id.index(),
        stable_name_fragment(obligation_id),
        artifact_index,
        kind.code(),
        &digest_hex[..12],
    )
}

fn stable_name_fragment(value: &str) -> String {
    let mut output = String::new();
    let mut pending_separator = false;
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() {
            if pending_separator && !output.is_empty() {
                output.push('-');
            }
            output.push(byte.to_ascii_lowercase() as char);
            pending_separator = false;
        } else if !output.is_empty() {
            pending_separator = true;
        }
    }
    if output.is_empty() {
        "artifact".to_string()
    } else {
        output
    }
}

fn tmir_digest_hex(digest: trust_ir::ProofDigest) -> String {
    hex_digest(&digest.bytes)
}

fn validate_tmir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<(), TrustIrNativeBundleError> {
    validate_trust_wp_request_provenance(bundle)?;

    bundle
        .validate()
        .map_err(|errors| TrustIrNativeBundleError::InvalidNativeBundle {
            errors: errors.into_iter().map(|error| error.to_string()).collect(),
        })?;

    validate_trust_wp_lineage_roots(bundle)
}

fn validate_trust_wp_request_provenance(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<(), TrustIrNativeBundleError> {
    for native_request in &bundle.requests {
        let trust_ir::NativeVerificationRequest::TrustWp(_) = native_request else {
            continue;
        };
        let request_id = native_request.id().index();

        trust_wp_expected_verifier_identity(
            request_id,
            native_request.expected_verifier_identity(),
        )?;
        trust_wp_solver_identities(request_id, native_request.solver_identities())?;
        let trust_ir::NativeVerificationRequest::TrustWp(trust_wp_request) = native_request else {
            continue;
        };
        trust_wp_replay_identity(request_id, trust_wp_request.provenance.replay_identity())?;
    }

    Ok(())
}

fn validate_trust_wp_lineage_roots(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<(), TrustIrNativeBundleError> {
    for request in &bundle.requests {
        let trust_ir::NativeVerificationRequest::TrustWp(trust_wp_request) = request else {
            continue;
        };

        for root in &trust_wp_request.lineage_roots {
            if let Some(node) = bundle
                .lineage
                .nodes
                .iter()
                .find(|candidate| candidate.id == *root)
            {
                if node.target_module != bundle.trust_ir_module_digest {
                    return Err(TrustIrNativeBundleError::MismatchedLineageRootDigest {
                        request_id: trust_wp_request.id.index(),
                        lineage_root_id: root.index(),
                        expected: bundle_digest_from_tmir(bundle.trust_ir_module_digest),
                        found: bundle_digest_from_tmir(node.target_module),
                    });
                }
            }
        }
    }

    Ok(())
}

fn tmir_trust_wp_request_to_verify_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    native_request: &trust_ir::NativeVerificationRequest,
    request: &trust_ir::TrustWpNativeRequest,
) -> Result<VerifyBundleRequest, TrustIrNativeBundleError> {
    if !is_supported_trust_wp_mode(request.mode) {
        return Err(TrustIrNativeBundleError::UnsupportedTrustWpMode {
            request_id: request.id.index(),
            mode: tmir_trust_wp_mode(request.mode),
            reason: TrustIrUnsupportedModeReason::RequiresSynthesizerResult,
        });
    }

    let native_verifier = trust_wp_expected_verifier_identity(
        request.id.index(),
        native_request.expected_verifier_identity(),
    )?;
    let native_solvers =
        trust_wp_solver_identities(request.id.index(), native_request.solver_identities())?;
    let native_replay =
        trust_wp_replay_identity(request.id.index(), request.provenance.replay_identity())?;

    let function = bundle.module.function_by_id(request.function).ok_or(
        TrustIrNativeBundleError::MissingFunction {
            request_id: request.id.index(),
            function_id: request.function.index(),
        },
    )?;

    let bundle_id = {
        let module_name = bundle.module.name.as_str();
        let request_id = request.id.index();
        format!("trust-ir-native:{module_name}:trust-wp:{request_id}")
    };
    let producer = BundleProducer::new(producer_name(bundle.producer))
        .with_version(format!("trust-ir-native-schema-{}", bundle.schema_version))
        .with_revision(tmir_digest_label(bundle.trust_ir_module_digest));
    let mut target = BundleTarget::new(bundle.module.name.clone());
    if let Some(target_info) = &bundle.module.target_info {
        target = target.with_target_triple(target_info.triple.clone());
    }

    let mut verify_request = VerifyBundleRequest::new(bundle_id, producer, target);
    for obligation_id in &request.obligations {
        let obligation = bundle
            .module
            .proof_obligations
            .iter()
            .find(|candidate| candidate.id == *obligation_id)
            .ok_or(TrustIrNativeBundleError::MissingObligation {
                request_id: request.id.index(),
                obligation_id: obligation_id.index(),
            })?;
        let formula =
            obligation
                .formula
                .as_ref()
                .ok_or(TrustIrNativeBundleError::MissingFormula {
                    request_id: request.id.index(),
                    obligation_id: obligation_id.index(),
                })?;
        let claim_format = claim_format_for_tmir_schema(formula.schema.as_str());
        let claim = BundleClaim::new(claim_format.clone(), formula.payload.clone());
        let mut bundle_obligation = BundleObligation::new(
            {
                let request_id = request.id.index();
                let obligation_id = obligation_id.index();
                format!("trust-ir-r{request_id}-proof-{obligation_id}")
            },
            obligation_kind_from_tmir(&obligation.kind, function.name.as_str()),
            function.name.clone(),
            claim,
        )
        .with_native_origin(
            BundleNativeOrigin::new(
                // Trust: the origin schema MUST carry trust-wp-core's canonical
                // `tmir.native-verification-bundle.` prefix — core's STRICT
                // fail-closed native-origin validation
                // (`validate_tmir_native_origin_metadata`: placeholder-solver
                // rejection, atom-binding checks, lineage/digest requirements)
                // only engages on that prefix. The previous `trust-ir.`
                // spelling silently bypassed the whole gate.
                format!(
                    "{TMIR_NATIVE_ORIGIN_SCHEMA_PREFIX}v{}",
                    bundle.schema_version
                ),
                bundle_native_mode(request.mode),
                request.id.index(),
                request.function.index(),
                obligation_id.index(),
            )
            .with_lineage_roots(request.lineage_roots.iter().map(|root| root.index()))
            .with_tmir_module_digest(bundle_digest_from_tmir(bundle.trust_ir_module_digest)),
        );

        bundle_obligation = attach_trust_ir_native_metadata(
            bundle,
            request,
            obligation,
            &native_verifier,
            &native_replay,
            &native_solvers,
            bundle_obligation,
        )?;

        if let Some(context) = proof_context_from_native_replay_context(request, *obligation_id) {
            bundle_obligation = bundle_obligation.with_proof_context(context);
        } else if request.mode == trust_ir::TrustWpVerificationMode::StrongestPostcondition {
            bundle_obligation = bundle_obligation
                .with_proof_context(proof_context_for_formula(&claim_format, formula));
        }

        verify_request = verify_request.with_obligation(bundle_obligation);
    }

    Ok(verify_request)
}

fn attach_trust_ir_native_metadata(
    bundle: &trust_ir::NativeVerificationBundle,
    request: &trust_ir::TrustWpNativeRequest,
    tmir_obligation: &trust_ir::ProofObligation,
    native_verifier: &BundleNativeToolIdentity,
    native_replay: &BundleNativeReplayIdentity,
    native_solvers: &[BundleNativeToolIdentity],
    mut obligation: BundleObligation,
) -> Result<BundleObligation, TrustIrNativeBundleError> {
    obligation = obligation
        .with_native_verifier(native_verifier.clone())
        .with_native_replay(native_replay.clone())
        .with_native_solvers(native_solvers.iter().cloned());

    let obligation_id = tmir_obligation.id;
    let source = tmir_obligation_source_for(bundle, obligation_id).ok_or(
        TrustIrNativeBundleError::MissingObligationSource {
            request_id: request.id.index(),
            obligation_id: obligation_id.index(),
        },
    )?;
    let Some(source_function) = source.function else {
        return Err(TrustIrNativeBundleError::MissingObligationSourceFunction {
            request_id: request.id.index(),
            obligation_id: obligation_id.index(),
            expected_function_id: request.function.index(),
        });
    };
    if source_function != request.function {
        return Err(
            TrustIrNativeBundleError::MismatchedObligationSourceFunction {
                request_id: request.id.index(),
                obligation_id: obligation_id.index(),
                expected_function_id: request.function.index(),
                found_function_id: source_function.index(),
            },
        );
    }
    validate_tmir_obligation_source_cause(
        request,
        obligation_id,
        &tmir_obligation.kind,
        source.cause,
    )?;
    validate_digest_bound_monomorphization_source(bundle, request, obligation_id, source)?;
    obligation = obligation
        .with_tmir_obligation_source(bundle_tmir_obligation_source_from_tmir(bundle, source));

    let span = source
        .span
        .ok_or(TrustIrNativeBundleError::MissingObligationSourceSpan {
            request_id: request.id.index(),
            obligation_id: obligation_id.index(),
        })?;
    obligation = obligation
        .with_location(bundle_source_span_from_tmir(span))
        .with_tmir_source_span(BundleTmirSourceSpan::new(span.file, span.line, span.col));

    Ok(obligation)
}

fn validate_tmir_obligation_source_cause(
    request: &trust_ir::TrustWpNativeRequest,
    obligation_id: trust_ir::ProofId,
    obligation_kind: &trust_ir::ObligationKind,
    source_cause: trust_ir::NativeObligationCause,
) -> Result<(), TrustIrNativeBundleError> {
    if tmir_obligation_source_cause_matches_kind(obligation_kind, source_cause) {
        return Ok(());
    }

    Err(TrustIrNativeBundleError::MismatchedObligationSourceCause {
        request_id: request.id.index(),
        obligation_id: obligation_id.index(),
        obligation_kind: tmir_obligation_kind_label(obligation_kind),
        source_cause: tmir_obligation_source_cause_label(source_cause),
    })
}

fn tmir_obligation_source_cause_matches_kind(
    obligation_kind: &trust_ir::ObligationKind,
    source_cause: trust_ir::NativeObligationCause,
) -> bool {
    match obligation_kind {
        trust_ir::ObligationKind::Precondition => {
            matches!(source_cause, trust_ir::NativeObligationCause::Precondition)
        }
        trust_ir::ObligationKind::Postcondition => {
            matches!(source_cause, trust_ir::NativeObligationCause::Postcondition)
        }
        trust_ir::ObligationKind::TranslationValidation => {
            matches!(source_cause, trust_ir::NativeObligationCause::Translation)
        }
        trust_ir::ObligationKind::MemorySafety => matches!(
            source_cause,
            trust_ir::NativeObligationCause::BoundsCheck
                | trust_ir::NativeObligationCause::LayoutCheck
                | trust_ir::NativeObligationCause::CastCheck
                | trust_ir::NativeObligationCause::PointerOffset
                | trust_ir::NativeObligationCause::BorrowCheck
        ),
        // Trust (trust-ir-spine item T1): the new routing-grade panic-class
        // kinds (`ArithmeticSafety`, `BoundsCheck`) are panic-freedom
        // obligations — they pair with the `Panic` source cause exactly like
        // `PanicFreedom`.
        trust_ir::ObligationKind::PanicFreedom
        | trust_ir::ObligationKind::ArithmeticSafety
        | trust_ir::ObligationKind::BoundsCheck => {
            matches!(source_cause, trust_ir::NativeObligationCause::Panic)
        }
        trust_ir::ObligationKind::LoopInvariant
        | trust_ir::ObligationKind::TypeInvariant
        | trust_ir::ObligationKind::RefinementType => true,
        trust_ir::ObligationKind::TemporalSafety | trust_ir::ObligationKind::Liveness => {
            matches!(source_cause, trust_ir::NativeObligationCause::Temporal)
        }
        // `ObligationKind` is `#[non_exhaustive]`; accept an unknown future kind
        // conservatively (do not reject a well-formed bundle on a new kind).
        _ => true,
    }
}

fn validate_digest_bound_monomorphization_source(
    bundle: &trust_ir::NativeVerificationBundle,
    request: &trust_ir::TrustWpNativeRequest,
    obligation_id: trust_ir::ProofId,
    source: &trust_ir::NativeObligationSource,
) -> Result<(), TrustIrNativeBundleError> {
    let Some(monomorphization_id) = source.monomorphization else {
        return Ok(());
    };

    let has_digest_bound_fact = source.facts.iter().any(|fact| {
        matches!(fact, trust_ir::NativeCompilerFactRef::Monomorphization(id) if *id == monomorphization_id)
            && bundle
                .compiler_facts
                .monomorphizations
                .iter()
                .any(|fact| fact.id == monomorphization_id)
    });
    if has_digest_bound_fact {
        return Ok(());
    }

    Err(
        TrustIrNativeBundleError::MissingDigestBoundMonomorphizationFact {
            request_id: request.id.index(),
            obligation_id: obligation_id.index(),
            monomorphization_id: monomorphization_id.index(),
        },
    )
}

fn claim_format_for_tmir_schema(schema: &str) -> BundleClaimFormat {
    // Compare separator-canonically: the compiler-side envelope spells the
    // namespace token `trust_wp.…` (identifier) while these constants use
    // `trust-wp.…` (crate). Same format, only `_`↔`-` differs — normalize so the
    // underscore spelling routes to the right format instead of `Other`.
    match schema.replace('_', "-").as_str() {
        TRUST_WP_PURE_EXPR_FORMULA_SCHEMA_VERSION => BundleClaimFormat::TrustWpPureExprV1,
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION => BundleClaimFormat::TrustFormulaV1,
        "smtlib2" => BundleClaimFormat::SmtLib2,
        _ => BundleClaimFormat::Other(schema.to_string()),
    }
}

const fn is_supported_trust_wp_mode(mode: trust_ir::TrustWpVerificationMode) -> bool {
    matches!(
        mode,
        trust_ir::TrustWpVerificationMode::WeakestPrecondition
            | trust_ir::TrustWpVerificationMode::StrongestPostcondition
    )
}

fn bundle_native_mode(mode: trust_ir::TrustWpVerificationMode) -> BundleNativeVerificationMode {
    match mode {
        trust_ir::TrustWpVerificationMode::WeakestPrecondition => {
            BundleNativeVerificationMode::WeakestPrecondition
        }
        trust_ir::TrustWpVerificationMode::StrongestPostcondition => {
            BundleNativeVerificationMode::StrongestPostcondition
        }
        trust_ir::TrustWpVerificationMode::Abduction => BundleNativeVerificationMode::Abduction,
    }
}

const fn tmir_trust_wp_mode(mode: trust_ir::TrustWpVerificationMode) -> TrustIrTrustWpMode {
    match mode {
        trust_ir::TrustWpVerificationMode::WeakestPrecondition => {
            TrustIrTrustWpMode::WeakestPrecondition
        }
        trust_ir::TrustWpVerificationMode::StrongestPostcondition => {
            TrustIrTrustWpMode::StrongestPostcondition
        }
        trust_ir::TrustWpVerificationMode::Abduction => TrustIrTrustWpMode::Abduction,
    }
}

fn obligation_kind_from_tmir(
    kind: &trust_ir::ObligationKind,
    function_name: &str,
) -> BundleObligationKind {
    match kind {
        trust_ir::ObligationKind::Precondition => BundleObligationKind::Precondition {
            callee: function_name.to_string(),
        },
        trust_ir::ObligationKind::Postcondition => BundleObligationKind::Postcondition,
        trust_ir::ObligationKind::LoopInvariant => BundleObligationKind::LoopInvariant,
        trust_ir::ObligationKind::TranslationValidation => {
            BundleObligationKind::TranslationValidation {
                pass: "trust-ir-native".to_string(),
            }
        }
        trust_ir::ObligationKind::MemorySafety => BundleObligationKind::MemorySafety,
        trust_ir::ObligationKind::PanicFreedom => {
            BundleObligationKind::Other("panic_freedom".to_string())
        }
        trust_ir::ObligationKind::TypeInvariant => {
            BundleObligationKind::Other("type_invariant".to_string())
        }
        trust_ir::ObligationKind::RefinementType => {
            BundleObligationKind::Other("refinement_type".to_string())
        }
        trust_ir::ObligationKind::TemporalSafety => {
            BundleObligationKind::Other("temporal_safety".to_string())
        }
        trust_ir::ObligationKind::Liveness => BundleObligationKind::Other("liveness".to_string()),
        // Trust (trust-ir-spine item T1): the new routing-grade panic-class
        // kinds carry their faithful label, mirroring how `PanicFreedom` maps to
        // `Other("panic_freedom")` — they are panic-class and route identically.
        trust_ir::ObligationKind::ArithmeticSafety => {
            BundleObligationKind::Other("arithmetic_safety".to_string())
        }
        trust_ir::ObligationKind::BoundsCheck => {
            BundleObligationKind::Other("bounds_check".to_string())
        }
        // `ObligationKind` is `#[non_exhaustive]`; an unknown future kind is
        // labeled generically rather than panicking.
        _ => BundleObligationKind::Other("unknown".to_string()),
    }
}

fn tmir_obligation_kind_label(kind: &trust_ir::ObligationKind) -> &'static str {
    match kind {
        trust_ir::ObligationKind::Precondition => "precondition",
        trust_ir::ObligationKind::Postcondition => "postcondition",
        trust_ir::ObligationKind::LoopInvariant => "loop_invariant",
        trust_ir::ObligationKind::TypeInvariant => "type_invariant",
        trust_ir::ObligationKind::RefinementType => "refinement_type",
        trust_ir::ObligationKind::TranslationValidation => "translation_validation",
        trust_ir::ObligationKind::MemorySafety => "memory_safety",
        trust_ir::ObligationKind::PanicFreedom => "panic_freedom",
        trust_ir::ObligationKind::TemporalSafety => "temporal_safety",
        trust_ir::ObligationKind::Liveness => "liveness",
        // Trust (trust-ir-spine item T1): faithful labels for the new
        // panic-class kinds.
        trust_ir::ObligationKind::ArithmeticSafety => "arithmetic_safety",
        trust_ir::ObligationKind::BoundsCheck => "bounds_check",
        // `ObligationKind` is `#[non_exhaustive]`; unknown future kinds.
        _ => "unknown",
    }
}

fn tmir_obligation_source_cause_label(cause: trust_ir::NativeObligationCause) -> &'static str {
    match cause {
        trust_ir::NativeObligationCause::Precondition => "precondition",
        trust_ir::NativeObligationCause::Postcondition => "postcondition",
        trust_ir::NativeObligationCause::Assert => "assert",
        trust_ir::NativeObligationCause::BoundsCheck => "bounds_check",
        trust_ir::NativeObligationCause::OverflowCheck => "overflow_check",
        trust_ir::NativeObligationCause::LayoutCheck => "layout_check",
        trust_ir::NativeObligationCause::CastCheck => "cast_check",
        trust_ir::NativeObligationCause::PointerOffset => "pointer_offset",
        trust_ir::NativeObligationCause::BorrowCheck => "borrow_check",
        trust_ir::NativeObligationCause::Translation => "translation",
        trust_ir::NativeObligationCause::Panic => "panic",
        trust_ir::NativeObligationCause::Temporal => "temporal",
        trust_ir::NativeObligationCause::Other => "other",
    }
}

const fn producer_name(producer: trust_ir::NativeBundleProducer) -> &'static str {
    match producer {
        trust_ir::NativeBundleProducer::TRust => "tRust",
        trust_ir::NativeBundleProducer::TSwift => "tSwift",
        trust_ir::NativeBundleProducer::TC => "tC",
        trust_ir::NativeBundleProducer::TrustIr => "TrustIr",
    }
}

fn tmir_digest_label(digest: trust_ir::ProofDigest) -> String {
    let algorithm = digest.algorithm.to_string();
    let value = hex_digest(&digest.bytes);
    format!("{algorithm}:{value}")
}

fn bundle_digest_from_tmir(digest: trust_ir::ProofDigest) -> BundleDigest {
    BundleDigest::new(digest.algorithm.to_string(), hex_digest(&digest.bytes))
}

fn bundle_source_span_from_tmir(span: trust_ir::SourceSpan) -> BundleSourceSpan {
    BundleSourceSpan::new(
        format!("trust-ir://file/{}", span.file),
        span.line,
        span.col,
    )
}

fn tmir_obligation_source_for(
    bundle: &trust_ir::NativeVerificationBundle,
    obligation_id: trust_ir::ProofId,
) -> Option<&trust_ir::NativeObligationSource> {
    bundle
        .compiler_facts
        .obligation_sources
        .iter()
        .find(|source| source.obligation == obligation_id)
}

fn trust_wp_expected_verifier_identity(
    request_id: u32,
    verifier: &trust_ir::NativeToolIdentity,
) -> Result<BundleNativeToolIdentity, TrustIrNativeBundleError> {
    // Normalize `_`↔`-`: the trust-ir bridge stamps the request's expected verifier
    // as `trust_wp` (its `NativeToolIdentity` convention) while this crate's canonical
    // name is `trust-wp`. A pure spelling mismatch must not reject a correctly-routed
    // trust-wp request (the Precondition path); a genuinely foreign identity still
    // differs after normalization and is rejected (fail-closed).
    if verifier.name.replace('_', "-") != TRUST_WP_EXPECTED_VERIFIER_NAME.replace('_', "-") {
        return Err(
            TrustIrNativeBundleError::MismatchedExpectedVerifierIdentity {
                request_id,
                expected: TRUST_WP_EXPECTED_VERIFIER_NAME,
                found: tmir_tool_identity_label(verifier),
            },
        );
    }

    Ok(native_tool_identity_from_tmir(verifier))
}

fn trust_wp_solver_identities(
    request_id: u32,
    solvers: &[trust_ir::NativeToolIdentity],
) -> Result<Vec<BundleNativeToolIdentity>, TrustIrNativeBundleError> {
    if solvers.is_empty() {
        return Err(TrustIrNativeBundleError::MissingSolverIdentities { request_id });
    }

    solvers
        .iter()
        .enumerate()
        .map(|(solver_index, solver)| {
            if is_empty_tmir_tool_identity(solver) {
                return Err(TrustIrNativeBundleError::EmptySolverIdentity {
                    request_id,
                    solver_index,
                });
            }
            Ok(native_tool_identity_from_tmir(solver))
        })
        .collect()
}

fn trust_wp_replay_identity(
    request_id: u32,
    replay: Option<&trust_ir::ProofReplayIdentity>,
) -> Result<BundleNativeReplayIdentity, TrustIrNativeBundleError> {
    let replay = replay.ok_or(TrustIrNativeBundleError::MissingReplayIdentity { request_id })?;
    if replay.engine.trim().is_empty() {
        return Err(TrustIrNativeBundleError::EmptyReplayIdentity {
            request_id,
            field: "engine",
        });
    }
    if replay.invocation.trim().is_empty() {
        return Err(TrustIrNativeBundleError::EmptyReplayIdentity {
            request_id,
            field: "invocation",
        });
    }
    let transcript_digest = replay
        .transcript_digest
        .ok_or(TrustIrNativeBundleError::MissingReplayTranscriptDigest { request_id })?;
    Ok(BundleNativeReplayIdentity::new(
        replay.engine.clone(),
        replay.invocation.clone(),
        bundle_digest_from_tmir(transcript_digest),
    ))
}

fn native_tool_identity_from_tmir(tool: &trust_ir::NativeToolIdentity) -> BundleNativeToolIdentity {
    let mut identity = BundleNativeToolIdentity::new(tool.name.clone());
    if let Some(version) = &tool.version {
        identity = identity.with_version(version.clone());
    }
    if let Some(revision) = &tool.revision {
        identity = identity.with_revision(revision.clone());
    }
    if let Some(digest) = tool.digest {
        identity = identity.with_digest(bundle_digest_from_tmir(digest));
    }
    identity
}

fn is_empty_tmir_tool_identity(tool: &trust_ir::NativeToolIdentity) -> bool {
    tool.name == "unknown"
        && tool.version.is_none()
        && tool.revision.is_none()
        && tool.digest.is_none()
}

fn tmir_tool_identity_label(tool: &trust_ir::NativeToolIdentity) -> String {
    let mut label = if tool.name.trim().is_empty() {
        "<empty>".to_string()
    } else {
        tool.name.clone()
    };
    if let Some(version) = &tool.version {
        let _ = write!(label, "@{version}");
    }
    if let Some(revision) = &tool.revision {
        let _ = write!(label, " rev={revision}");
    }
    if let Some(digest) = tool.digest {
        let _ = write!(label, " digest={}", tmir_digest_label(digest));
    }
    label
}

fn bundle_tmir_obligation_source_from_tmir(
    bundle: &trust_ir::NativeVerificationBundle,
    source: &trust_ir::NativeObligationSource,
) -> BundleTmirObligationSource {
    let mut mapped = BundleTmirObligationSource::new(bundle_tmir_obligation_cause(source.cause));
    if let Some(function_id) = source.function {
        mapped = mapped.with_function_id(function_id.index());
    }
    if let Some(assertion_id) = source.assertion_id {
        mapped = mapped.with_assertion_id(assertion_id.index());
    }
    if let Some(monomorphization_id) = source.monomorphization {
        mapped = mapped.with_monomorphization_id(monomorphization_id.index());
    }
    let compiler_facts_digest = bundle_digest_from_tmir(bundle.compiler_facts.stable_digest());
    mapped.with_compiler_fact_refs(
        source
            .facts
            .iter()
            .copied()
            .map(|fact| bundle_tmir_compiler_fact_ref(bundle, fact, &compiler_facts_digest)),
    )
}

fn bundle_tmir_obligation_cause(
    cause: trust_ir::NativeObligationCause,
) -> BundleTmirObligationCause {
    match cause {
        trust_ir::NativeObligationCause::Precondition => BundleTmirObligationCause::Precondition,
        trust_ir::NativeObligationCause::Postcondition => BundleTmirObligationCause::Postcondition,
        trust_ir::NativeObligationCause::Assert => BundleTmirObligationCause::Assert,
        trust_ir::NativeObligationCause::BoundsCheck => BundleTmirObligationCause::BoundsCheck,
        trust_ir::NativeObligationCause::OverflowCheck => BundleTmirObligationCause::OverflowCheck,
        trust_ir::NativeObligationCause::LayoutCheck => BundleTmirObligationCause::LayoutCheck,
        trust_ir::NativeObligationCause::CastCheck => BundleTmirObligationCause::CastCheck,
        trust_ir::NativeObligationCause::PointerOffset => {
            BundleTmirObligationCause::Other("pointer_offset".to_string())
        }
        trust_ir::NativeObligationCause::BorrowCheck => BundleTmirObligationCause::BorrowCheck,
        trust_ir::NativeObligationCause::Translation => BundleTmirObligationCause::Translation,
        trust_ir::NativeObligationCause::Panic => BundleTmirObligationCause::Panic,
        trust_ir::NativeObligationCause::Temporal => {
            BundleTmirObligationCause::Other("temporal".to_string())
        }
        trust_ir::NativeObligationCause::Other => {
            BundleTmirObligationCause::Other("other".to_string())
        }
    }
}

fn bundle_tmir_compiler_fact_ref(
    bundle: &trust_ir::NativeVerificationBundle,
    fact: trust_ir::NativeCompilerFactRef,
    compiler_facts_digest: &BundleDigest,
) -> BundleTmirCompilerFactRef {
    match fact {
        trust_ir::NativeCompilerFactRef::AdtLayout(id) => {
            let mut fact_ref = BundleTmirCompilerFactRef::adt_layout(id.index());
            if bundle
                .compiler_facts
                .adt_layouts
                .iter()
                .any(|candidate| candidate.id == id)
            {
                fact_ref = fact_ref.with_digest(compiler_facts_digest.clone());
            }
            fact_ref
        }
        trust_ir::NativeCompilerFactRef::FatPointer(id) => {
            let mut fact_ref = BundleTmirCompilerFactRef::fat_pointer(id.index());
            if bundle
                .compiler_facts
                .fat_pointers
                .iter()
                .any(|candidate| candidate.id == id)
            {
                fact_ref = fact_ref.with_digest(compiler_facts_digest.clone());
            }
            fact_ref
        }
        trust_ir::NativeCompilerFactRef::TraitObjectMetadata(id) => {
            let mut fact_ref =
                bundle_tmir_other_compiler_fact_ref("trait_object_metadata", id.index());
            if bundle
                .compiler_facts
                .trait_object_metadata
                .iter()
                .any(|candidate| candidate.id == id)
            {
                fact_ref = fact_ref.with_digest(compiler_facts_digest.clone());
            }
            fact_ref
        }
        trust_ir::NativeCompilerFactRef::PointerOffset(id) => {
            let mut fact_ref = bundle_tmir_other_compiler_fact_ref("pointer_offset", id.index());
            if bundle
                .compiler_facts
                .pointer_offsets
                .iter()
                .any(|candidate| candidate.id == id)
            {
                fact_ref = fact_ref.with_digest(compiler_facts_digest.clone());
            }
            fact_ref
        }
        trust_ir::NativeCompilerFactRef::Cast(id) => {
            let mut fact_ref = BundleTmirCompilerFactRef::cast(id.index());
            if bundle
                .compiler_facts
                .casts
                .iter()
                .any(|candidate| candidate.id == id)
            {
                fact_ref = fact_ref.with_digest(compiler_facts_digest.clone());
            }
            fact_ref
        }
        trust_ir::NativeCompilerFactRef::Monomorphization(id) => {
            let mut fact_ref = BundleTmirCompilerFactRef::monomorphization(id.index());
            if let Some(fact) = bundle
                .compiler_facts
                .monomorphizations
                .iter()
                .find(|candidate| candidate.id == id)
            {
                fact_ref = fact_ref.with_digest(bundle_digest_from_tmir(fact.stable_digest));
            }
            fact_ref
        }
    }
}

fn bundle_tmir_other_compiler_fact_ref(
    kind: impl Into<String>,
    id: u32,
) -> BundleTmirCompilerFactRef {
    BundleTmirCompilerFactRef::other(kind, id)
}

fn proof_context_from_native_replay_context(
    request: &trust_ir::TrustWpNativeRequest,
    obligation_id: trust_ir::ProofId,
) -> Option<BundleProofContext> {
    let mut atoms = request
        .provenance
        .replay_context()
        .atoms
        .iter()
        .filter(|atom| match atom.obligation {
            Some(bound_obligation) => bound_obligation == obligation_id,
            None => true,
        })
        .collect::<Vec<_>>();
    if atoms.is_empty() {
        return None;
    }

    atoms.sort_by_key(|atom| atom.id);
    let mut next_index = 0;
    let mut assumptions = Vec::new();
    for atom in atoms
        .iter()
        .copied()
        .filter(|atom| atom.kind == trust_ir::NativeReplayAtomKind::Assumption)
    {
        assumptions.push(bundle_proof_atom_from_tmir(
            atom,
            next_index,
            BundleProofAtomRole::Assumption,
        ));
        next_index += 1;
    }

    let mut assertions = Vec::new();
    for atom in atoms
        .iter()
        .copied()
        .filter(|atom| atom.kind == trust_ir::NativeReplayAtomKind::Assertion)
    {
        assertions.push(bundle_proof_atom_from_tmir(
            atom,
            next_index,
            BundleProofAtomRole::Assertion,
        ));
        next_index += 1;
    }

    Some(BundleProofContext::new(assumptions, assertions))
}

fn bundle_proof_atom_from_tmir(
    atom: &trust_ir::NativeReplayAtom,
    index: u32,
    role: BundleProofAtomRole,
) -> BundleProofAtom {
    let mut proof_atom = BundleProofAtom::new(
        index,
        role,
        BundleClaim::new(
            claim_format_for_tmir_schema(atom.formula.schema.as_str()),
            atom.formula.payload.clone(),
        )
        .with_digest(bundle_digest_from_tmir(atom.payload_digest)),
    )
    .with_native_replay_atom_id(atom.id.index());
    if let Some(obligation) = atom.obligation {
        proof_atom = proof_atom.with_native_obligation_id(obligation.index());
    }
    if let Some(assertion_id) = atom.assertion_id {
        proof_atom = proof_atom.with_native_assertion_id(assertion_id.index());
    }
    if let Some(span) = atom.span {
        proof_atom =
            proof_atom.with_native_span(BundleTmirSourceSpan::new(span.file, span.line, span.col));
    }
    proof_atom
}

fn proof_context_for_formula(
    claim_format: &BundleClaimFormat,
    formula: &trust_ir::ProofFormula,
) -> BundleProofContext {
    match claim_format {
        BundleClaimFormat::TrustFormulaV1 => {
            proof_context_from_trust_formula(formula.payload.as_str()).unwrap_or_default()
        }
        BundleClaimFormat::TrustWpPureExprV1 => {
            proof_context_from_trust_wp_pure_expr(formula.payload.as_str()).unwrap_or_default()
        }
        BundleClaimFormat::SmtLib2 | BundleClaimFormat::Other(_) => BundleProofContext::default(),
        _ => BundleProofContext::default(),
    }
}

fn proof_context_from_trust_formula(payload: &str) -> Option<BundleProofContext> {
    let value: Value = serde_json::from_str(payload).ok()?;
    let envelope = value.as_object()?;
    let body = envelope.get("body")?;
    let (assumptions, assertions) = split_trust_formula_body(body);
    let assertion_index_offset = assumptions.len();

    Some(BundleProofContext::new(
        assumptions
            .into_iter()
            .enumerate()
            .map(|(index, body)| {
                BundleProofAtom::new(
                    proof_atom_index(index),
                    BundleProofAtomRole::Assumption,
                    BundleClaim::new(
                        BundleClaimFormat::TrustFormulaV1,
                        trust_formula_atom_payload(envelope, body),
                    ),
                )
            })
            .collect(),
        assertions
            .into_iter()
            .enumerate()
            .map(|(index, body)| {
                BundleProofAtom::new(
                    proof_atom_index(assertion_index_offset + index),
                    BundleProofAtomRole::Assertion,
                    BundleClaim::new(
                        BundleClaimFormat::TrustFormulaV1,
                        trust_formula_atom_payload(envelope, body),
                    ),
                )
            })
            .collect(),
    ))
}

fn trust_formula_atom_payload(envelope: &Map<String, Value>, body: Value) -> String {
    let mut atom = Map::new();
    atom.insert(
        "schema".to_string(),
        Value::String(TRUST_FORMULA_CLAIM_SCHEMA_VERSION.to_string()),
    );
    if let Some(variables) = envelope.get("variables") {
        atom.insert("variables".to_string(), variables.clone());
    }
    if let Some(result) = envelope.get("result") {
        atom.insert("result".to_string(), result.clone());
    }
    atom.insert("body".to_string(), body);
    Value::Object(atom).to_string()
}

fn split_trust_formula_body(body: &Value) -> (Vec<Value>, Vec<Value>) {
    let Some(object) = body.as_object() else {
        return (Vec::new(), vec![body.clone()]);
    };
    if object.get("op").and_then(Value::as_str) == Some("implies") {
        let assumptions = object
            .get("lhs")
            .map(flatten_trust_formula_conjunction)
            .unwrap_or_default();
        let assertions = object
            .get("rhs")
            .map(flatten_trust_formula_conjunction)
            .unwrap_or_default();
        return (assumptions, assertions);
    }
    (Vec::new(), flatten_trust_formula_conjunction(body))
}

fn flatten_trust_formula_conjunction(value: &Value) -> Vec<Value> {
    let Some(object) = value.as_object() else {
        return vec![value.clone()];
    };
    if object.get("op").and_then(Value::as_str) == Some("and") {
        let mut atoms = Vec::new();
        if let Some(lhs) = object.get("lhs") {
            atoms.extend(flatten_trust_formula_conjunction(lhs));
        }
        if let Some(rhs) = object.get("rhs") {
            atoms.extend(flatten_trust_formula_conjunction(rhs));
        }
        return atoms;
    }
    vec![value.clone()]
}

fn proof_context_from_trust_wp_pure_expr(payload: &str) -> Option<BundleProofContext> {
    let predicate = parse_contract(payload.trim()).ok()?;
    let (assumptions, assertions) = split_trust_wp_pure_predicate(predicate);
    let assertion_index_offset = assumptions.len();
    Some(BundleProofContext::new(
        assumptions
            .into_iter()
            .enumerate()
            .map(|(index, expr)| {
                BundleProofAtom::new(
                    proof_atom_index(index),
                    BundleProofAtomRole::Assumption,
                    BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, expr.to_string()),
                )
            })
            .collect(),
        assertions
            .into_iter()
            .enumerate()
            .map(|(index, expr)| {
                BundleProofAtom::new(
                    proof_atom_index(assertion_index_offset + index),
                    BundleProofAtomRole::Assertion,
                    BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, expr.to_string()),
                )
            })
            .collect(),
    ))
}

fn split_trust_wp_pure_predicate(predicate: PureExpr) -> (Vec<PureExpr>, Vec<PureExpr>) {
    match predicate {
        PureExpr::BinOp(left, BinOp::Implies, right) => (
            flatten_trust_wp_pure_conjunction((*left).clone()),
            flatten_trust_wp_pure_conjunction((*right).clone()),
        ),
        other => (Vec::new(), flatten_trust_wp_pure_conjunction(other)),
    }
}

fn flatten_trust_wp_pure_conjunction(expr: PureExpr) -> Vec<PureExpr> {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            let mut atoms = flatten_trust_wp_pure_conjunction((*left).clone());
            atoms.extend(flatten_trust_wp_pure_conjunction((*right).clone()));
            atoms
        }
        other => vec![other],
    }
}

fn proof_atom_index(index: usize) -> u32 {
    u32::try_from(index).expect("proof context atom index fits in u32")
}

fn hex_digest(bytes: &[u8; 32]) -> String {
    let mut output = String::with_capacity(64);
    for byte in bytes {
        let _ = write!(output, "{byte:02x}");
    }
    output
}
