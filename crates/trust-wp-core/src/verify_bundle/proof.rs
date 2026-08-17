// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{self, Write},
    sync::Arc,
};

use sha2::{Digest, Sha256};

use super::{
    native_predicate_for_obligation, BundleClaimFormat, BundleDigest, BundleEvidenceMetadata,
    BundleNativeToolIdentity, BundleObligation, BundleObligationKind, BundleObligationResult,
    BundleObligationStatus, BundleResultMetadata, BundleSolverMetadata, BundleSummaryFact,
    BundleSummaryFactKind, EvidenceArtifact, EvidenceArtifactKind, NativeBundlePredicate,
    NativeClaimFormat, ProofEvidence, ProofEvidenceFormat, ProofStrength, VerifyBundleRequest,
    VerifyBundleResult, VerifyBundleStatus, PROOF_EVIDENCE_SCHEMA_VERSION,
    TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION, TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
    VERIFY_BUNDLE_API_VERSION,
};
use crate::{
    contract_parser::parse_contract,
    formula::{BinOp, CaptureAvoidingSubstOptions, ExprSort, PureExpr, UnOp},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct NativePureProof {
    normalized_predicate: String,
    steps: Vec<NativeReplayStep>,
}

impl NativePureProof {
    fn replay_step_count(&self) -> usize {
        self.steps.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum NativeReplayStep {
    DecodeClaimFormat(NativeClaimFormat),
    Normalize(String),
    ApplyRule(&'static str),
    Verified,
}

impl NativeReplayStep {
    fn as_wire_line(&self) -> String {
        match self {
            Self::DecodeClaimFormat(format) => format!("decode:{}", format.as_str()),
            Self::Normalize(predicate) => format!("normalize:{predicate}"),
            Self::ApplyRule(rule) => format!("replay-rule:{rule}"),
            Self::Verified => "result:verified".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum NativePureProofOutcome {
    Verified(NativePureProof),
    Failed(String),
    Unsupported(String),
}

/// Native proof replay failure with stable code and human-readable context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofReplayError {
    pub code: String,
    pub message: String,
}

impl ProofReplayError {
    fn new(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ProofReplayError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code, self.message)
    }
}

impl std::error::Error for ProofReplayError {}

pub(super) fn prove_native_pure_predicate(
    predicate: &PureExpr,
    claim_format: NativeClaimFormat,
    summary_facts: &[BundleSummaryFact],
) -> NativePureProofOutcome {
    let normalized_predicate = predicate.to_string();
    let context = NativeReplayContext { summary_facts };
    match prove_bool(predicate, &context) {
        TruthValue::True { rule } => NativePureProofOutcome::Verified(NativePureProof {
            steps: vec![
                NativeReplayStep::DecodeClaimFormat(claim_format),
                NativeReplayStep::Normalize(normalized_predicate.clone()),
                NativeReplayStep::ApplyRule(rule),
                NativeReplayStep::Verified,
            ],
            normalized_predicate,
        }),
        TruthValue::False { rule } => NativePureProofOutcome::Failed(format!(
            "typed predicate is false by native pure replay rule `{rule}`"
        )),
        TruthValue::Unknown { reason } => NativePureProofOutcome::Unsupported(format!(
            "native pure replay cannot prove or refute predicate: {reason}"
        )),
    }
}

/// Create checked native pure replay evidence for one obligation.
///
/// This is the public construction side of [`replay_native_pure_evidence`].
/// It validates that the obligation belongs to the request, proves the typed
/// native predicate through trust-wp's replay rules, and returns the canonical
/// proof-grade evidence envelope committed to the request, typed metadata,
/// summary facts, normalized obligation, and replay log.
pub fn create_native_pure_replay_evidence(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> Result<ProofEvidence, ProofReplayError> {
    let (_, proof) = checked_native_pure_proof(request, obligation)?;
    Ok(proof_evidence_for_obligation(request, obligation, &proof))
}

/// Create a verified obligation result with native replay evidence and solver
/// metadata.
///
/// Callers integrating MIR/tMIR directly can use this when they already have a
/// single typed obligation and need the same result surface produced by
/// [`NativeTrustWpBundleVerifier`](super::NativeTrustWpBundleVerifier).
pub fn create_native_pure_replay_result(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> Result<BundleObligationResult, ProofReplayError> {
    let (native_predicate, proof) = checked_native_pure_proof(request, obligation)?;
    let evidence = proof_evidence_for_obligation(request, obligation, &proof);
    let metadata =
        proof_result_metadata_for_obligation(obligation, &native_predicate, &proof, &evidence);
    Ok(BundleObligationResult::verified(obligation.id.clone(), evidence).with_metadata(metadata))
}

/// Replay and validate native trust-wp pure-predicate evidence for one obligation.
///
/// This is intentionally exact for v1: the replayed canonical evidence must
/// match the provided evidence byte-for-byte after stable wire serialization,
/// including artifact order. Missing, duplicated, tampered, or reordered
/// artifacts therefore fail closed.
pub fn replay_native_pure_evidence(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    evidence: &ProofEvidence,
) -> Result<(), ProofReplayError> {
    if !request
        .obligations
        .iter()
        .any(|candidate| candidate == obligation)
    {
        return Err(ProofReplayError::new(
            "proof_replay.obligation",
            format!(
                "obligation `{}` is not present in bundle `{}`",
                obligation.id, request.bundle_id
            ),
        ));
    }

    if let Some(diagnostic) = request.validation_diagnostics().into_iter().next() {
        return Err(ProofReplayError::new(diagnostic.code, diagnostic.message));
    }

    if evidence.format != ProofEvidenceFormat::TrustWpNativePureReplayV1 {
        return Err(ProofReplayError::new(
            "proof_replay.format",
            format!(
                "native pure replay requires `{}` evidence, got `{}`",
                TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
                evidence.format.as_str()
            ),
        ));
    }

    if !evidence.is_proof_grade() {
        return Err(ProofReplayError::new(
            "proof_replay.evidence",
            "evidence is missing proof-grade schema, checker, digest, or artifact identity",
        ));
    }

    let (_, proof) = checked_native_pure_proof(request, obligation)?;
    let expected = proof_evidence_for_obligation(request, obligation, &proof);

    if evidence.to_stable_wire() != expected.to_stable_wire() {
        return Err(ProofReplayError::new(
            "proof_replay.mismatch",
            format!(
                "canonical evidence does not match replayed native proof: {}",
                evidence_mismatch_detail(evidence, &expected)
            ),
        ));
    }

    Ok(())
}

fn checked_native_pure_proof(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> Result<(NativeBundlePredicate, NativePureProof), ProofReplayError> {
    if !request
        .obligations
        .iter()
        .any(|candidate| candidate == obligation)
    {
        return Err(ProofReplayError::new(
            "proof_replay.obligation",
            format!(
                "obligation `{}` is not present in bundle `{}`",
                obligation.id, request.bundle_id
            ),
        ));
    }

    if let Some(diagnostic) = request.validation_diagnostics().into_iter().next() {
        return Err(ProofReplayError::new(diagnostic.code, diagnostic.message));
    }

    if !is_trust_wp_owned_obligation_kind(&obligation.kind) {
        return Err(ProofReplayError::new(
            "proof_replay.kind",
            "trust-wp native replay does not own this obligation kind",
        ));
    }

    let native_predicate = native_predicate_for_obligation(obligation)
        .map_err(|diagnostic| ProofReplayError::new(diagnostic.code, diagnostic.message))?;

    match prove_native_pure_predicate(
        &native_predicate.predicate,
        native_predicate.claim_format,
        &obligation.summary_facts,
    ) {
        NativePureProofOutcome::Verified(proof) => Ok((native_predicate, proof)),
        NativePureProofOutcome::Failed(reason) | NativePureProofOutcome::Unsupported(reason) => {
            Err(ProofReplayError::new(
                "proof_replay.result",
                format!("obligation does not replay to verified: {reason}"),
            ))
        }
    }
}

/// Replay and validate aggregate verify-bundle evidence for a successful
/// result.
///
/// This checks the bundle-level aggregate manifest, then replays each native
/// trust-wp per-obligation proof artifact. Non-native proof formats must still be
/// proof-grade checked evidence, but are not interpreted by the native pure
/// replay checker.
pub fn replay_verify_bundle_result_evidence(
    request: &VerifyBundleRequest,
    result: &VerifyBundleResult,
) -> Result<(), ProofReplayError> {
    let aggregate = checked_aggregate_result_evidence(request, result)?;
    replay_result_obligation_evidence(request, result)?;

    let expected = aggregate_proof_evidence_for_result(request, &result.obligation_results)
        .ok_or_else(|| {
            ProofReplayError::new(
                "proof_replay.aggregate_evidence",
                "verified result cannot be reconstructed into aggregate proof evidence",
            )
        })?;
    if aggregate.to_stable_wire() != expected.to_stable_wire() {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_mismatch",
            format!(
                "aggregate evidence does not match replayed bundle proof: {}",
                evidence_mismatch_detail(aggregate, &expected)
            ),
        ));
    }

    Ok(())
}

fn checked_aggregate_result_evidence<'a>(
    request: &VerifyBundleRequest,
    result: &'a VerifyBundleResult,
) -> Result<&'a ProofEvidence, ProofReplayError> {
    if result.api_version != VERIFY_BUNDLE_API_VERSION {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_api_version",
            format!(
                "result API version `{}` does not match `{VERIFY_BUNDLE_API_VERSION}`",
                result.api_version
            ),
        ));
    }
    if result.bundle_id != request.bundle_id {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_bundle",
            format!(
                "result bundle `{}` does not match request bundle `{}`",
                result.bundle_id, request.bundle_id
            ),
        ));
    }
    if result.status != VerifyBundleStatus::Verified {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_status",
            format!(
                "aggregate replay requires verified result status, got `{}`",
                result.status.as_str()
            ),
        ));
    }
    if result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity != super::BundleDiagnosticSeverity::Warning)
    {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_diagnostics",
            "verified aggregate result contains fail-closed diagnostics",
        ));
    }

    let aggregate = result.aggregate_evidence.as_ref().ok_or_else(|| {
        ProofReplayError::new(
            "proof_replay.aggregate_evidence",
            "verified result is missing aggregate proof evidence",
        )
    })?;
    if aggregate.format != ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1 {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_format",
            format!(
                "aggregate replay requires `{}` evidence, got `{}`",
                TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
                aggregate.format.as_str()
            ),
        ));
    }
    if !aggregate.is_proof_grade() {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_evidence",
            "aggregate evidence is missing proof-grade schema, checker, digest, or artifact identity",
        ));
    }

    Ok(aggregate)
}

fn replay_result_obligation_evidence(
    request: &VerifyBundleRequest,
    result: &VerifyBundleResult,
) -> Result<(), ProofReplayError> {
    for obligation in &request.obligations {
        let obligation_result = result
            .obligation_results
            .iter()
            .find(|candidate| candidate.obligation_id == obligation.id)
            .ok_or_else(|| {
                ProofReplayError::new(
                    "proof_replay.aggregate_obligation",
                    format!(
                        "verified aggregate result is missing obligation `{}`",
                        obligation.id
                    ),
                )
            })?;
        let BundleObligationStatus::Verified { evidence } = &obligation_result.status else {
            return Err(ProofReplayError::new(
                "proof_replay.aggregate_obligation",
                format!(
                    "aggregate replay requires verified obligation `{}`",
                    obligation.id
                ),
            ));
        };
        if obligation_result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity != super::BundleDiagnosticSeverity::Warning)
        {
            return Err(ProofReplayError::new(
                "proof_replay.aggregate_obligation_diagnostics",
                format!(
                    "verified obligation `{}` contains fail-closed diagnostics",
                    obligation.id
                ),
            ));
        }
        if evidence.format == ProofEvidenceFormat::TrustWpNativePureReplayV1 {
            replay_native_pure_evidence(request, obligation, evidence)?;
        } else if !evidence.is_proof_grade() {
            return Err(ProofReplayError::new(
                "proof_replay.aggregate_obligation_evidence",
                format!("obligation `{}` evidence is not proof-grade", obligation.id),
            ));
        }
    }

    Ok(())
}

#[allow(clippy::too_many_lines)]
fn evidence_mismatch_detail(provided: &ProofEvidence, expected: &ProofEvidence) -> String {
    let mut details = Vec::new();

    push_field_diff(
        &mut details,
        "schema_version",
        provided.schema_version.as_str(),
        expected.schema_version.as_str(),
    );
    push_field_diff(
        &mut details,
        "producer",
        provided.producer.as_str(),
        expected.producer.as_str(),
    );
    push_field_diff(
        &mut details,
        "format",
        provided.format.as_str(),
        expected.format.as_str(),
    );
    push_field_diff(
        &mut details,
        "strength",
        provided.strength.as_str(),
        expected.strength.as_str(),
    );
    push_optional_field_diff(
        &mut details,
        "checked_by",
        provided.checked_by.as_deref(),
        expected.checked_by.as_deref(),
    );

    if provided.artifacts.len() != expected.artifacts.len() {
        details.push(format!(
            "artifact count differs: expected {}, got {}",
            expected.artifacts.len(),
            provided.artifacts.len()
        ));
    }

    for (index, (provided_artifact, expected_artifact)) in provided
        .artifacts
        .iter()
        .zip(expected.artifacts.iter())
        .enumerate()
    {
        let label = artifact_diagnostic_label(index, expected_artifact);
        push_digest_diff(
            &mut details,
            &format!("{label} digest"),
            &provided_artifact.digest,
            &expected_artifact.digest,
        );
        push_field_diff(
            &mut details,
            &format!("{label} schema_version"),
            provided_artifact.schema_version.as_str(),
            expected_artifact.schema_version.as_str(),
        );
        if provided_artifact.digest == expected_artifact.digest
            && provided_artifact.kind == expected_artifact.kind
        {
            push_field_diff(
                &mut details,
                &format!("{label} id"),
                provided_artifact.id.as_str(),
                expected_artifact.id.as_str(),
            );
        }
        push_field_diff(
            &mut details,
            &format!("{label} kind"),
            provided_artifact.kind.as_str(),
            expected_artifact.kind.as_str(),
        );
        push_field_diff(
            &mut details,
            &format!("{label} description"),
            provided_artifact.description.as_str(),
            expected_artifact.description.as_str(),
        );
        push_optional_field_diff(
            &mut details,
            &format!("{label} uri"),
            provided_artifact.uri.as_deref(),
            expected_artifact.uri.as_deref(),
        );
        push_optional_field_diff(
            &mut details,
            &format!("{label} inline bytes encoding"),
            provided_artifact
                .inline_bytes
                .as_ref()
                .map(|bytes| bytes.encoding.as_str()),
            expected_artifact
                .inline_bytes
                .as_ref()
                .map(|bytes| bytes.encoding.as_str()),
        );
        if provided_artifact.inline_bytes.is_some() != expected_artifact.inline_bytes.is_some() {
            details.push(format!(
                "{label} inline bytes presence differs: expected `{}`, got `{}`",
                expected_artifact.inline_bytes.is_some(),
                provided_artifact.inline_bytes.is_some(),
            ));
        }
    }
    push_optional_digest_diff(
        &mut details,
        "digest",
        provided.digest.as_ref(),
        expected.digest.as_ref(),
    );

    if details.is_empty() {
        "stable wire differs without a structured field mismatch".to_string()
    } else {
        details.truncate(4);
        details.join("; ")
    }
}

fn push_field_diff(details: &mut Vec<String>, field: &str, provided: &str, expected: &str) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{expected}`, got `{provided}`"
        ));
    }
}

fn push_optional_field_diff(
    details: &mut Vec<String>,
    field: &str,
    provided: Option<&str>,
    expected: Option<&str>,
) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{}`, got `{}`",
            expected.unwrap_or("none"),
            provided.unwrap_or("none"),
        ));
    }
}

fn push_optional_digest_diff(
    details: &mut Vec<String>,
    field: &str,
    provided: Option<&BundleDigest>,
    expected: Option<&BundleDigest>,
) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{}`, got `{}`",
            digest_material(expected),
            digest_material(provided),
        ));
    }
}

fn push_digest_diff(
    details: &mut Vec<String>,
    field: &str,
    provided: &BundleDigest,
    expected: &BundleDigest,
) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{}`, got `{}`",
            digest_material(Some(expected)),
            digest_material(Some(provided)),
        ));
    }
}

fn artifact_diagnostic_label(index: usize, expected_artifact: &EvidenceArtifact) -> String {
    format!(
        "artifact {index} (`{}`; binds {})",
        expected_artifact.kind.as_str(),
        artifact_diagnostic_scope(&expected_artifact.kind)
    )
}

fn artifact_diagnostic_scope(kind: &EvidenceArtifactKind) -> &'static str {
    match kind {
        EvidenceArtifactKind::RequestDigest => {
            "typed request envelope, verification options, and obligation inventory"
        }
        EvidenceArtifactKind::AggregateProofManifest => {
            "bundle-level proof result, per-obligation evidence identities, and request digest"
        }
        EvidenceArtifactKind::NormalizedObligation => {
            "typed claim, tMIR metadata, native replay/verifier/solver identities, proof context, and summary digest"
        }
        EvidenceArtifactKind::SummaryEvidence => {
            "cross-crate summary fact identities, producers, endpoints, and digests"
        }
        EvidenceArtifactKind::ReplayLog => {
            "normalized proof digest, summary digest, and native replay steps"
        }
        EvidenceArtifactKind::ProofCertificate => "external proof certificate identity",
        EvidenceArtifactKind::SolverTranscript => "external solver transcript identity",
        EvidenceArtifactKind::Counterexample => "counterexample artifact identity",
        EvidenceArtifactKind::Model => "solver model artifact identity",
        EvidenceArtifactKind::DiagnosticTrace => "diagnostic trace artifact identity",
    }
}

#[allow(clippy::too_many_lines)]
pub(super) fn proof_evidence_for_obligation(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    proof: &NativePureProof,
) -> ProofEvidence {
    let summary_artifact = summary_facts_artifact(&obligation.summary_facts);
    let summary_digest_line = summary_artifact.as_ref().map_or_else(
        || "none".to_string(),
        |artifact| {
            format!(
                "{}:{}",
                artifact.digest.algorithm.as_str(),
                artifact.digest.value.as_str()
            )
        },
    );
    let claim_digest_line = digest_material(obligation.claim.digest.as_ref());
    let source_location = source_location_material(obligation.location.as_ref());
    let native_origin = native_origin_material(obligation);
    let tmir_source_span = tmir_source_span_material(obligation);
    let native_verifier = native_verifier_material(obligation);
    let native_replay = native_replay_material(obligation);
    let native_solvers = native_solvers_material(obligation);
    let tmir_obligation_source = tmir_obligation_source_material(obligation);
    let proof_context_digest = proof_context_digest_line(&obligation.metadata.proof_context);
    let normalized_material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nbundle={bundle}\nproducer.name={producer_name}\nproducer.version={producer_version}\nproducer.revision={producer_revision}\ntarget.crate={target_crate}\ntarget.package={target_package}\ntarget.triple={target_triple}\nobligation={obligation_id}\nkind={kind}\nfunction={function}\nlocation.file={location_file}\nlocation.line={location_line}\nlocation.column={location_column}\nnative-origin={native_origin}\ntmir-source-span={tmir_source_span}\nnative-verifier={native_verifier}\nnative-replay={native_replay}\nnative-solvers={native_solvers}\ntmir-obligation-source={tmir_obligation_source}\nproof-context.assumptions={assumptions}\nproof-context.assertions={assertions}\nproof-context-digest={proof_context_digest}\nclaim-format={claim_format}\nclaim-digest={claim_digest}\npredicate={predicate}\nsummary-count={summary_count}\nsummary-digest={summary_digest}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        bundle = request.bundle_id.as_str(),
        producer_name = material_text(&request.producer.name),
        producer_version = optional_material_text(request.producer.version.as_deref()),
        producer_revision = optional_material_text(request.producer.revision.as_deref()),
        target_crate = material_text(&request.target.crate_name),
        target_package = optional_material_text(request.target.package_name.as_deref()),
        target_triple = optional_material_text(request.target.target_triple.as_deref()),
        obligation_id = obligation.id.as_str(),
        kind = obligation_kind_label(&obligation.kind),
        function = obligation.function.as_str(),
        location_file = source_location.file.as_str(),
        location_line = source_location.line.as_str(),
        location_column = source_location.column.as_str(),
        native_origin = native_origin.as_str(),
        tmir_source_span = tmir_source_span.as_str(),
        native_verifier = native_verifier.as_str(),
        native_replay = native_replay.as_str(),
        native_solvers = native_solvers.as_str(),
        tmir_obligation_source = tmir_obligation_source.as_str(),
        assumptions = obligation.metadata.proof_context.assumptions.len(),
        assertions = obligation.metadata.proof_context.assertions.len(),
        proof_context_digest = proof_context_digest.as_str(),
        claim_format = claim_format_label(&obligation.claim.format),
        claim_digest = claim_digest_line.as_str(),
        predicate = proof.normalized_predicate.as_str(),
        summary_count = obligation.summary_facts.len(),
        summary_digest = summary_digest_line.as_str(),
    );
    let normalized_digest = stable_digest(&normalized_material);

    let replay_material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nnormalized-digest={algorithm}:{value}\nsummary-digest={summary_digest}\nsteps=\n{steps}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        algorithm = normalized_digest.algorithm.as_str(),
        value = normalized_digest.value.as_str(),
        summary_digest = summary_digest_line.as_str(),
        steps = proof
            .steps
            .iter()
            .map(NativeReplayStep::as_wire_line)
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let replay_digest = stable_digest(&replay_material);

    let normalized_artifact = EvidenceArtifact::new(
        EvidenceArtifactKind::NormalizedObligation,
        normalized_digest,
        "normalized typed trust-wp PureExpr obligation",
    )
    .with_utf8_bytes(normalized_material);
    let replay_artifact = EvidenceArtifact::new(
        EvidenceArtifactKind::ReplayLog,
        replay_digest,
        "native pure predicate replay trace",
    )
    .with_utf8_bytes(replay_material);
    let mut artifacts = vec![request_digest_artifact(request), normalized_artifact];
    artifacts.extend(summary_artifact);
    artifacts.push(replay_artifact);
    artifacts.push(proof_check_transcript_artifact(
        request, obligation, proof, &artifacts,
    ));
    let evidence_digest = stable_digest(&evidence_manifest_material(
        &ProofEvidenceFormat::TrustWpNativePureReplayV1,
        TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        &artifacts,
    ));

    let mut evidence = ProofEvidence::checked(
        "trust-wp-core.verify_bundle",
        ProofEvidenceFormat::TrustWpNativePureReplayV1,
        TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
    )
    .with_strength(ProofStrength::Sound)
    .with_digest(evidence_digest);
    for artifact in artifacts {
        evidence = evidence.with_artifact(artifact);
    }
    evidence
}

pub(super) fn aggregate_proof_evidence_for_result(
    request: &VerifyBundleRequest,
    obligation_results: &[BundleObligationResult],
) -> Option<ProofEvidence> {
    if obligation_results.len() != request.obligations.len() {
        return None;
    }

    let mut seen = HashSet::new();
    for obligation in &request.obligations {
        let result = obligation_results
            .iter()
            .find(|candidate| candidate.obligation_id == obligation.id)?;
        if !seen.insert(result.obligation_id.as_str()) {
            return None;
        }
        let BundleObligationStatus::Verified { evidence } = &result.status else {
            return None;
        };
        if !evidence.is_proof_grade() {
            return None;
        }
    }

    let request_artifact = request_digest_artifact(request);
    let aggregate_material = aggregate_proof_manifest_material(request, obligation_results);
    let aggregate_artifact = EvidenceArtifact::new(
        EvidenceArtifactKind::AggregateProofManifest,
        stable_digest(&aggregate_material),
        "aggregate verify-bundle proof manifest",
    )
    .with_utf8_bytes(aggregate_material);
    let artifacts = vec![request_artifact, aggregate_artifact];
    let evidence_digest = stable_digest(&evidence_manifest_material(
        &ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1,
        TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
        &artifacts,
    ));

    let mut evidence = ProofEvidence::checked(
        "trust-wp-core.verify_bundle",
        ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1,
        TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
    )
    .with_strength(ProofStrength::Sound)
    .with_digest(evidence_digest);
    for artifact in artifacts {
        evidence = evidence.with_artifact(artifact);
    }
    Some(evidence)
}

pub(super) fn proof_result_metadata_for_obligation(
    obligation: &BundleObligation,
    native_predicate: &NativeBundlePredicate,
    proof: &NativePureProof,
    evidence: &ProofEvidence,
) -> BundleResultMetadata {
    let proof_context = &obligation.metadata.proof_context;
    BundleResultMetadata::new(
        Some(BundleSolverMetadata::new(
            "trust-wp-core.native-pure-replay",
            TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
            native_predicate.claim_format.as_str(),
            proof.replay_step_count(),
            proof_context.assumptions.len(),
            proof_context.assertions.len(),
        )),
        Some(BundleEvidenceMetadata::from_evidence(evidence)),
    )
}

pub(super) fn is_trust_wp_owned_obligation_kind(kind: &BundleObligationKind) -> bool {
    matches!(
        kind,
        BundleObligationKind::Precondition { .. }
            | BundleObligationKind::Postcondition
            | BundleObligationKind::LoopInvariant
    )
}

fn aggregate_proof_manifest_material(
    request: &VerifyBundleRequest,
    obligation_results: &[BundleObligationResult],
) -> String {
    let request_digest = stable_digest(&request_digest_material(request));
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\naggregate-schema={aggregate_schema}\nbundle={bundle}\nrequest-digest={request_algorithm}:{request_value}\nobligation-count={obligation_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        aggregate_schema = TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
        bundle = material_text(&request.bundle_id),
        request_algorithm = request_digest.algorithm.as_str(),
        request_value = request_digest.value.as_str(),
        obligation_count = request.obligations.len(),
    );

    for (index, obligation) in request.obligations.iter().enumerate() {
        let result = obligation_results
            .iter()
            .find(|candidate| candidate.obligation_id == obligation.id)
            .expect("aggregate caller checked that all obligation results are present");
        let BundleObligationStatus::Verified { evidence } = &result.status else {
            unreachable!("aggregate caller checked that all obligation results are verified");
        };
        let evidence_wire_digest = stable_digest(&evidence.to_stable_wire());
        let _ = writeln!(
            material,
            "obligation.{index}.id={id}\nobligation.{index}.status=verified\nobligation.{index}.evidence-format={format}\nobligation.{index}.evidence-strength={strength}\nobligation.{index}.evidence-digest={digest}\nobligation.{index}.evidence-wire-digest={wire_algorithm}:{wire_value}\nobligation.{index}.checked-by={checked_by}\nobligation.{index}.artifact-count={artifact_count}",
            id = material_text(&obligation.id),
            format = material_text(evidence.format.as_str()),
            strength = evidence.strength.as_str(),
            digest = digest_material(evidence.digest.as_ref()),
            wire_algorithm = evidence_wire_digest.algorithm.as_str(),
            wire_value = evidence_wire_digest.value.as_str(),
            checked_by = optional_material_text(evidence.checked_by.as_deref()),
            artifact_count = evidence.artifacts.len(),
        );
        for (artifact_index, artifact) in evidence.artifacts.iter().enumerate() {
            let _ = writeln!(
                material,
                "obligation.{index}.artifact.{artifact_index}.id={id}\nobligation.{index}.artifact.{artifact_index}.kind={kind}\nobligation.{index}.artifact.{artifact_index}.digest={algorithm}:{value}",
                id = material_text(&artifact.id),
                kind = artifact.kind.as_str(),
                algorithm = artifact.digest.algorithm.as_str(),
                value = artifact.digest.value.as_str(),
            );
        }
    }

    material
}

fn evidence_manifest_material(
    format: &ProofEvidenceFormat,
    checker: &str,
    artifacts: &[EvidenceArtifact],
) -> String {
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nformat={format}\nstrength={strength}\nchecker={checker}\nartifact-count={artifact_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        format = format.as_str(),
        strength = ProofStrength::Sound.as_str(),
        checker = checker,
        artifact_count = artifacts.len(),
    );
    for (index, artifact) in artifacts.iter().enumerate() {
        let _ = writeln!(
            material,
            "artifact.{index}.id={id}\nartifact.{index}.kind={kind}\nartifact.{index}.digest={algorithm}:{value}",
            id = artifact.id.as_str(),
            kind = artifact.kind.as_str(),
            algorithm = artifact.digest.algorithm.as_str(),
            value = artifact.digest.value.as_str(),
        );
    }
    material
}

fn summary_facts_artifact(summary_facts: &[BundleSummaryFact]) -> Option<EvidenceArtifact> {
    (!summary_facts.is_empty()).then(|| {
        let material = summary_facts_material(summary_facts);
        EvidenceArtifact::new(
            EvidenceArtifactKind::SummaryEvidence,
            stable_digest(&material),
            "cross-crate summary evidence inputs",
        )
        .with_utf8_bytes(material)
    })
}

fn request_digest_artifact(request: &VerifyBundleRequest) -> EvidenceArtifact {
    let material = request_digest_material(request);
    EvidenceArtifact::new(
        EvidenceArtifactKind::RequestDigest,
        stable_digest(&material),
        "canonical verify-bundle request digest",
    )
    .with_utf8_bytes(material)
}

fn proof_check_transcript_artifact(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    proof: &NativePureProof,
    checked_artifacts: &[EvidenceArtifact],
) -> EvidenceArtifact {
    let material = proof_check_transcript_material(request, obligation, proof, checked_artifacts);
    EvidenceArtifact::new(
        EvidenceArtifactKind::SolverTranscript,
        stable_digest(&material),
        "native pure replay proof-check transcript over evidence artifact bytes",
    )
    .with_utf8_bytes(material)
}

fn proof_check_transcript_material(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    proof: &NativePureProof,
    checked_artifacts: &[EvidenceArtifact],
) -> String {
    let mut material = format!(
        "schema=trust-wp.native-pure-proof-check-transcript.v1\napi={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nbundle={bundle}\nobligation={obligation}\nchecker={checker}\nresult=verified\nreplay-steps={replay_steps}\nchecked-artifacts={artifact_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        bundle = material_text(&request.bundle_id),
        obligation = material_text(&obligation.id),
        checker = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        replay_steps = proof.replay_step_count(),
        artifact_count = checked_artifacts.len(),
    );

    for (index, artifact) in checked_artifacts.iter().enumerate() {
        let transport = artifact_transport_material(artifact);
        let _ = writeln!(
            material,
            "artifact.{index}.id={id}\nartifact.{index}.kind={kind}\nartifact.{index}.declared-digest={declared_algorithm}:{declared_value}\nartifact.{index}.transport={transport}\nartifact.{index}.actual-digest={actual_digest}\nartifact.{index}.byte-len={byte_len}",
            id = artifact.id.as_str(),
            kind = artifact.kind.as_str(),
            declared_algorithm = artifact.digest.algorithm.as_str(),
            declared_value = artifact.digest.value.as_str(),
            transport = transport.kind.as_str(),
            actual_digest = transport.digest.as_str(),
            byte_len = transport.byte_len.as_str(),
        );
    }

    material
}

struct ArtifactTransportMaterial {
    kind: String,
    digest: String,
    byte_len: String,
}

fn artifact_transport_material(artifact: &EvidenceArtifact) -> ArtifactTransportMaterial {
    match artifact
        .inline_bytes
        .as_ref()
        .and_then(|bytes| bytes.decoded_bytes().ok())
    {
        Some(bytes) => ArtifactTransportMaterial {
            kind: artifact.inline_bytes.as_ref().map_or_else(
                || "inline:unknown".to_string(),
                |bytes| format!("inline:{}", bytes.encoding.as_str()),
            ),
            digest: digest_bytes_material(&bytes),
            byte_len: bytes.len().to_string(),
        },
        None => ArtifactTransportMaterial {
            kind: artifact.uri.as_ref().map_or_else(
                || "missing".to_string(),
                |uri| format!("uri:{}", material_text(uri)),
            ),
            digest: "none".to_string(),
            byte_len: "none".to_string(),
        },
    }
}

fn digest_material(digest: Option<&BundleDigest>) -> String {
    digest.map_or_else(
        || "none".to_string(),
        |digest| format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str()),
    )
}

fn digest_bytes_material(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("sha256:{}", hex_bytes(&hasher.finalize()))
}

fn material_text(value: &str) -> String {
    format!("hex:{}", hex_bytes(value.as_bytes()))
}

fn optional_material_text(value: Option<&str>) -> String {
    value.map_or_else(|| "none".to_string(), material_text)
}

struct SourceLocationMaterial {
    file: String,
    line: String,
    column: String,
}

fn source_location_material(location: Option<&super::BundleSourceSpan>) -> SourceLocationMaterial {
    location.map_or_else(
        || SourceLocationMaterial {
            file: "none".to_string(),
            line: "none".to_string(),
            column: "none".to_string(),
        },
        |location| SourceLocationMaterial {
            file: material_text(&location.file),
            line: location.line.to_string(),
            column: location.column.to_string(),
        },
    )
}

fn native_origin_material(obligation: &BundleObligation) -> String {
    obligation.metadata.native_origin.as_ref().map_or_else(
        || "none".to_string(),
        |origin| {
            let lineage_roots = if origin.lineage_roots.is_empty() {
                "none".to_string()
            } else {
                origin
                    .lineage_roots
                    .iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            };
            let module_digest = digest_material(origin.tmir_module_digest.as_ref());
            format!(
                "schema={};mode={};request={};function={};obligation={};lineage-roots={};tmir-digest={}",
                material_text(&origin.schema),
                origin.mode.as_str(),
                origin.request_id,
                origin.function_id,
                origin.obligation_id,
                lineage_roots,
                module_digest,
            )
        },
    )
}

fn tmir_source_span_material(obligation: &BundleObligation) -> String {
    obligation.metadata.tmir_source_span.map_or_else(
        || "none".to_string(),
        |span| {
            format!(
                "file-id={};line={};column={}",
                span.file_id, span.line, span.column
            )
        },
    )
}

fn native_verifier_material(obligation: &BundleObligation) -> String {
    obligation
        .metadata
        .native_verifier
        .as_ref()
        .map_or_else(|| "none".to_string(), native_tool_identity_material)
}

fn native_replay_material(obligation: &BundleObligation) -> String {
    obligation.metadata.native_replay.as_ref().map_or_else(
        || "none".to_string(),
        |replay| {
            format!(
                "engine={};invocation={};transcript={}",
                material_text(&replay.engine),
                material_text(&replay.invocation),
                digest_material(Some(&replay.transcript_digest)),
            )
        },
    )
}

fn native_solvers_material(obligation: &BundleObligation) -> String {
    if obligation.metadata.native_solvers.is_empty() {
        return "none".to_string();
    }

    obligation
        .metadata
        .native_solvers
        .iter()
        .enumerate()
        .map(|(index, solver)| format!("{index}:{}", native_tool_identity_material(solver)))
        .collect::<Vec<_>>()
        .join(",")
}

fn native_tool_identity_material(identity: &BundleNativeToolIdentity) -> String {
    format!(
        "name={};version={};revision={};digest={}",
        material_text(&identity.name),
        optional_material_text(identity.version.as_deref()),
        optional_material_text(identity.revision.as_deref()),
        digest_material(identity.digest.as_ref()),
    )
}

fn tmir_obligation_source_material(obligation: &BundleObligation) -> String {
    obligation
        .metadata
        .tmir_obligation_source
        .as_ref()
        .map_or_else(
            || "none".to_string(),
            |source| {
                let mut fact_refs = source.compiler_fact_refs.iter().collect::<Vec<_>>();
                fact_refs.sort_by(|left, right| {
                    left.kind
                        .as_str()
                        .cmp(right.kind.as_str())
                        .then(left.id.cmp(&right.id))
                });
                let facts = if fact_refs.is_empty() {
                    "none".to_string()
                } else {
                    fact_refs
                        .into_iter()
                        .map(|fact| {
                            format!(
                                "{}:{}:{}",
                                fact.kind.as_str(),
                                fact.id,
                                digest_material(fact.digest.as_ref())
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(",")
                };
                format!(
                    "cause={};function={};assertion={};monomorphization={};facts={}",
                    material_text(source.cause.as_str()),
                    source
                        .function_id
                        .map_or_else(|| "none".to_string(), |id| id.to_string()),
                    source
                        .assertion_id
                        .map_or_else(|| "none".to_string(), |id| id.to_string()),
                    source
                        .monomorphization_id
                        .map_or_else(|| "none".to_string(), |id| id.to_string()),
                    material_text(&facts),
                )
            },
        )
}

fn proof_context_digest_line(context: &super::BundleProofContext) -> String {
    context.canonical_digest().map_or_else(
        || "none".to_string(),
        |digest| format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str()),
    )
}

fn request_digest_material(request: &VerifyBundleRequest) -> String {
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nrequest.api={request_api}\nbundle={bundle}\nproducer.name={producer_name}\nproducer.version={producer_version}\nproducer.revision={producer_revision}\ntarget.crate={target_crate}\ntarget.package={target_package}\ntarget.triple={target_triple}\noptions.require-proof-evidence={require_proof_evidence}\noptions.timeout-ms={timeout_ms}\nobligation-count={obligation_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        request_api = material_text(&request.api_version),
        bundle = material_text(&request.bundle_id),
        producer_name = material_text(&request.producer.name),
        producer_version = optional_material_text(request.producer.version.as_deref()),
        producer_revision = optional_material_text(request.producer.revision.as_deref()),
        target_crate = material_text(&request.target.crate_name),
        target_package = optional_material_text(request.target.package_name.as_deref()),
        target_triple = optional_material_text(request.target.target_triple.as_deref()),
        require_proof_evidence = request.options.require_proof_evidence,
        timeout_ms = timeout_material(request.options.timeout_ms),
        obligation_count = request.obligations.len(),
    );

    for (index, obligation) in request.obligations.iter().enumerate() {
        let location = source_location_material(obligation.location.as_ref());
        let native_origin = native_origin_material(obligation);
        let tmir_source_span = tmir_source_span_material(obligation);
        let native_verifier = native_verifier_material(obligation);
        let native_replay = native_replay_material(obligation);
        let native_solvers = native_solvers_material(obligation);
        let tmir_obligation_source = tmir_obligation_source_material(obligation);
        let proof_context_digest = proof_context_digest_line(&obligation.metadata.proof_context);
        let payload_digest = stable_digest(&obligation.claim.payload);
        let summary_digest_line = if obligation.summary_facts.is_empty() {
            "none".to_string()
        } else {
            let digest = stable_digest(&summary_facts_material(&obligation.summary_facts));
            format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str())
        };
        let _ = writeln!(
            material,
            "obligation.{index}.id={id}\nobligation.{index}.kind={kind}\nobligation.{index}.function={function}\nobligation.{index}.location.file={location_file}\nobligation.{index}.location.line={location_line}\nobligation.{index}.location.column={location_column}\nobligation.{index}.native-origin={native_origin}\nobligation.{index}.tmir-source-span={tmir_source_span}\nobligation.{index}.native-verifier={native_verifier}\nobligation.{index}.native-replay={native_replay}\nobligation.{index}.native-solvers={native_solvers}\nobligation.{index}.tmir-obligation-source={tmir_obligation_source}\nobligation.{index}.proof-context.assumptions={assumptions}\nobligation.{index}.proof-context.assertions={assertions}\nobligation.{index}.proof-context-digest={proof_context_digest}\nobligation.{index}.claim-format={claim_format}\nobligation.{index}.claim-digest={claim_digest}\nobligation.{index}.claim-payload-digest={payload_algorithm}:{payload_value}\nobligation.{index}.summary-count={summary_count}\nobligation.{index}.summary-digest={summary_digest}",
            id = material_text(&obligation.id),
            kind = material_text(&obligation_kind_label(&obligation.kind)),
            function = material_text(&obligation.function),
            location_file = location.file.as_str(),
            location_line = location.line.as_str(),
            location_column = location.column.as_str(),
            native_origin = native_origin.as_str(),
            tmir_source_span = tmir_source_span.as_str(),
            native_verifier = native_verifier.as_str(),
            native_replay = native_replay.as_str(),
            native_solvers = native_solvers.as_str(),
            tmir_obligation_source = tmir_obligation_source.as_str(),
            assumptions = obligation.metadata.proof_context.assumptions.len(),
            assertions = obligation.metadata.proof_context.assertions.len(),
            proof_context_digest = proof_context_digest.as_str(),
            claim_format = material_text(claim_format_label(&obligation.claim.format)),
            claim_digest = digest_material(obligation.claim.digest.as_ref()),
            payload_algorithm = payload_digest.algorithm.as_str(),
            payload_value = payload_digest.value.as_str(),
            summary_count = obligation.summary_facts.len(),
            summary_digest = summary_digest_line.as_str(),
        );
    }

    material
}

fn timeout_material(timeout_ms: Option<u64>) -> String {
    timeout_ms.map_or_else(|| "none".to_string(), |timeout_ms| timeout_ms.to_string())
}

fn summary_facts_material(summary_facts: &[BundleSummaryFact]) -> String {
    let mut facts = summary_facts.iter().collect::<Vec<_>>();
    facts.sort_by(|left, right| left.id.cmp(&right.id));

    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nsummary-count={summary_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        summary_count = facts.len(),
    );
    for (index, fact) in facts.into_iter().enumerate() {
        let _ = writeln!(
            material,
            "summary.{index}.id={id}\nsummary.{index}.producer={producer}\nsummary.{index}.source-crate={source_crate}\nsummary.{index}.source-item={source_item}\nsummary.{index}.kind={kind}\nsummary.{index}.digest={algorithm}:{value}",
            id = fact.id.as_str(),
            producer = fact.producer.as_str(),
            source_crate = fact.source_crate.as_str(),
            source_item = fact.source_item.as_str(),
            kind = fact.kind.as_str(),
            algorithm = fact.digest.algorithm.as_str(),
            value = fact.digest.value.as_str(),
        );
        if let Some(endpoints) = summary_fact_endpoints(fact) {
            let (left, right) = match endpoints {
                SummaryFactEndpoints::Textual { left, right }
                | SummaryFactEndpoints::Binding { left, right } => (left, right),
            };
            let _ = writeln!(
                material,
                "summary.{index}.left={left}\nsummary.{index}.right={right}",
            );
        }
    }
    material
}

fn stable_digest(material: &str) -> BundleDigest {
    let mut hasher = Sha256::new();
    hasher.update(material.as_bytes());
    BundleDigest::new("sha256", hex_bytes(&hasher.finalize()))
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn obligation_kind_label(kind: &BundleObligationKind) -> String {
    match kind {
        BundleObligationKind::Precondition { callee } => format!("precondition:{callee}"),
        BundleObligationKind::Postcondition => "postcondition".to_string(),
        BundleObligationKind::Assertion { message } => format!("assertion:{message}"),
        BundleObligationKind::LoopInvariant => "loop-invariant".to_string(),
        BundleObligationKind::Termination => "termination".to_string(),
        BundleObligationKind::MemorySafety => "memory-safety".to_string(),
        BundleObligationKind::ArithmeticSafety => "arithmetic-safety".to_string(),
        BundleObligationKind::TranslationValidation { pass } => {
            format!("translation-validation:{pass}")
        }
        BundleObligationKind::Other(kind) => format!("other:{kind}"),
    }
}

fn claim_format_label(format: &BundleClaimFormat) -> &str {
    format.as_str()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TruthValue {
    True { rule: &'static str },
    False { rule: &'static str },
    Unknown { reason: String },
}

#[derive(Debug, Clone, Copy)]
struct NativeReplayContext<'a> {
    summary_facts: &'a [BundleSummaryFact],
}

impl TruthValue {
    fn from_bool(value: bool, rule: &'static str) -> Self {
        if value {
            Self::True { rule }
        } else {
            Self::False { rule }
        }
    }

    fn unknown(reason: impl Into<String>) -> Self {
        Self::Unknown {
            reason: reason.into(),
        }
    }
}

fn prove_bool(expr: &PureExpr, context: &NativeReplayContext<'_>) -> TruthValue {
    let mut env = HashMap::new();
    prove_bool_with_env(expr, &mut env, context)
}

fn prove_bool_with_env(
    expr: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match expr {
        PureExpr::Bool(value) => TruthValue::from_bool(*value, "bool-literal"),
        PureExpr::UnOp(UnOp::Not, inner) => match prove_bool_with_env(inner, env, context) {
            TruthValue::True { .. } => TruthValue::False { rule: "not-true" },
            TruthValue::False { .. } => TruthValue::True { rule: "not-false" },
            TruthValue::Unknown { reason } => TruthValue::Unknown { reason },
        },
        PureExpr::BinOp(left, op, right) => prove_binary_bool(left, *op, right, env, context),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            prove_ite(cond, then_expr, else_expr, env, context)
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } => match with_bound_sort(env, var, var_sort.as_ref(), |env| {
            prove_bool_with_env(body, env, context)
        }) {
            TruthValue::True { .. } => TruthValue::True {
                rule: "forall-true-body",
            },
            TruthValue::False { .. } => TruthValue::False {
                rule: "forall-false-body",
            },
            TruthValue::Unknown { reason } => TruthValue::Unknown { reason },
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            ..
        } => match with_bound_sort(env, var, var_sort.as_ref(), |env| {
            prove_bool_with_env(body, env, context)
        }) {
            TruthValue::True { .. } => TruthValue::True {
                rule: "exists-true-body",
            },
            TruthValue::False { .. } => TruthValue::False {
                rule: "exists-false-body",
            },
            TruthValue::Unknown { reason } => TruthValue::Unknown { reason },
        },
        PureExpr::LetAssume { assumption, body } => {
            prove_binary_bool(assumption, BinOp::Implies, body, env, context)
        }
        PureExpr::LetObligation { obligation, body } => {
            prove_binary_bool(obligation, BinOp::And, body, env, context)
        }
        PureExpr::Let { var, value, body } => {
            let Some(inlined) = inline_let_binding_for_native_replay(var, value, body) else {
                return TruthValue::unknown(
                    "let binding crosses an old-state boundary outside the native replay fragment",
                );
            };
            prove_bool_with_env(&inlined, env, context)
        }
        PureExpr::Closure { .. }
        | PureExpr::Int(_)
        | PureExpr::Float(_)
        | PureExpr::Var(_, _)
        | PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, _)
        | PureExpr::Old(_)
        | PureExpr::Deref(_)
        | PureExpr::Final(_)
        | PureExpr::View(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. } => {
            TruthValue::unknown("predicate is outside the native replay fragment")
        }
    }
}

fn inline_let_binding_for_native_replay(
    var: &str,
    value: &PureExpr,
    body: &PureExpr,
) -> Option<PureExpr> {
    // A formula-level let evaluates `value` in the surrounding state. Moving
    // that expression beneath `old(...)` would instead evaluate its free
    // program variables in the entry state. Until replay carries explicit
    // state-indexed let values, reject this beta reduction rather than silently
    // changing `let t = x in old(t)` into `old(x)`.
    if body.any_recursive(|candidate| {
        matches!(candidate, PureExpr::Old(inner) if inner.any_free_var(|name, _| name == var))
    }) {
        return None;
    }
    let mut substitutions = HashMap::new();
    substitutions.insert(var.to_string(), value.clone());
    Some(body.substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default()))
}

fn prove_binary_bool(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match op {
        BinOp::And => prove_and(left, right, env, context),
        BinOp::Or => prove_or(left, right, env, context),
        BinOp::Implies => prove_implies(left, right, env, context),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            // Preserve the guard of a conditional operand instead of asking
            // the comparison prover to reason about an opaque value.  This is
            // the exact semantics of a total `if`: both guarded comparisons
            // must discharge independently.
            if let Some(rewritten) = split_comparison_ite(left, op, right) {
                prove_bool_with_env(&rewritten, env, context)
            } else {
                prove_comparison(left, op, right, env, context)
            }
        }
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Mod
        | BinOp::DivTrunc
        | BinOp::RemTrunc
        | BinOp::Shl
        | BinOp::Shr
        | BinOp::BitAnd
        | BinOp::BitXor
        | BinOp::BitOr => TruthValue::unknown("arithmetic expression is not a predicate"),
    }
}

fn prove_and(
    left: &PureExpr,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match (
        prove_bool_with_env(left, env, context),
        prove_bool_with_env(right, env, context),
    ) {
        (TruthValue::True { .. }, TruthValue::True { .. }) => TruthValue::True { rule: "and-true" },
        (TruthValue::False { .. }, _) | (_, TruthValue::False { .. }) => {
            TruthValue::False { rule: "and-false" }
        }
        (TruthValue::Unknown { reason }, _) | (_, TruthValue::Unknown { reason }) => {
            TruthValue::Unknown { reason }
        }
    }
}

fn prove_or(
    left: &PureExpr,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match (
        prove_bool_with_env(left, env, context),
        prove_bool_with_env(right, env, context),
    ) {
        (TruthValue::True { .. }, _) | (_, TruthValue::True { .. }) => {
            TruthValue::True { rule: "or-true" }
        }
        (TruthValue::False { .. }, TruthValue::False { .. }) => {
            TruthValue::False { rule: "or-false" }
        }
        (TruthValue::Unknown { reason }, _) | (_, TruthValue::Unknown { reason }) => {
            TruthValue::Unknown { reason }
        }
    }
}

fn prove_implies(
    left: &PureExpr,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    if assumption_entails_predicate(left, right) {
        return TruthValue::True {
            rule: "assumption-projection",
        };
    }

    match (
        prove_bool_with_env(left, env, context),
        prove_bool_with_env(right, env, context),
    ) {
        (TruthValue::False { .. }, _) | (_, TruthValue::True { .. }) => TruthValue::True {
            rule: "implies-true",
        },
        (TruthValue::True { .. }, TruthValue::False { .. }) => TruthValue::False {
            rule: "implies-false",
        },
        (TruthValue::Unknown { reason }, _) | (_, TruthValue::Unknown { reason }) => {
            prove_int_arithmetic_implication(left, right)
                .or_else(|| prove_linear_implication(left, right))
                .unwrap_or(TruthValue::Unknown { reason })
        }
    }
}

fn assumption_entails_predicate(assumption: &PureExpr, predicate: &PureExpr) -> bool {
    if predicates_equivalent(assumption, predicate) {
        return true;
    }

    if let PureExpr::BinOp(left, BinOp::And, right) = predicate {
        return assumption_entails_predicate(assumption, left)
            && assumption_entails_predicate(assumption, right);
    }

    assumption_contains_predicate(assumption, predicate)
}

fn assumption_contains_predicate(assumption: &PureExpr, predicate: &PureExpr) -> bool {
    if predicates_equivalent(assumption, predicate) {
        return true;
    }

    if let Some(normalized) = denegate_ordered_integer_comparison(assumption) {
        if predicates_equivalent(&normalized, predicate) {
            return true;
        }
    }

    match assumption {
        PureExpr::BinOp(left, BinOp::And, right) => {
            assumption_contains_predicate(left, predicate)
                || assumption_contains_predicate(right, predicate)
        }
        _ => false,
    }
}

fn predicates_equivalent(left: &PureExpr, right: &PureExpr) -> bool {
    left == right || symmetric_comparison_equivalent(left, right)
}

fn symmetric_comparison_equivalent(left: &PureExpr, right: &PureExpr) -> bool {
    let PureExpr::BinOp(left_lhs, left_op, left_rhs) = left else {
        return false;
    };
    let PureExpr::BinOp(right_lhs, right_op, right_rhs) = right else {
        return false;
    };

    left_lhs == right_rhs
        && left_rhs == right_lhs
        && comparison_reverse(*left_op) == Some(*right_op)
}

fn comparison_reverse(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Eq => Some(BinOp::Eq),
        BinOp::Ne => Some(BinOp::Ne),
        BinOp::Lt => Some(BinOp::Gt),
        BinOp::Le => Some(BinOp::Ge),
        BinOp::Gt => Some(BinOp::Lt),
        BinOp::Ge => Some(BinOp::Le),
        _ => None,
    }
}

/// Negate an ordered comparison without swapping its operands.
///
/// This is deliberately separate from [`comparison_reverse`].  It is valid
/// only over a total order and therefore remains gated by
/// [`is_ordered_integer_operand`] at its call site.
fn negate_ordered_comparison(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Lt => Some(BinOp::Ge),
        BinOp::Gt => Some(BinOp::Le),
        BinOp::Le => Some(BinOp::Gt),
        BinOp::Ge => Some(BinOp::Lt),
        BinOp::Eq | BinOp::Ne => None,
        _ => None,
    }
}

/// Whether an expression is inside the native replay engine's integer-order
/// fragment.  An absent sort means `Int` by the formula AST's documented
/// backwards-compatible convention.  Every other sort fails closed.
fn is_ordered_integer_operand(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Float(_) => false,
        PureExpr::Var(_, sort) => sort.as_ref().is_none_or(|sort| *sort == ExprSort::Int),
        PureExpr::UnOp(UnOp::Neg, inner) => is_ordered_integer_operand(inner),
        PureExpr::BinOp(left, op, right) => {
            matches!(
                op,
                BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::DivTrunc
                    | BinOp::RemTrunc
            ) && is_ordered_integer_operand(left)
                && is_ordered_integer_operand(right)
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => is_ordered_integer_operand(inner),
        _ => false,
    }
}

/// Rewrite `!(a op b)` to the equivalent ordered integer comparison.
///
/// Equality and disequality are intentionally excluded: their negations do not
/// project to one ordered comparison. Float and other explicitly non-integer
/// sorts are also excluded, so this helper can only add a total-order integer
/// fact.
fn denegate_ordered_integer_comparison(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::UnOp(UnOp::Not, inner) = expr else {
        return None;
    };
    let PureExpr::BinOp(left, op, right) = &**inner else {
        return None;
    };
    let negated = negate_ordered_comparison(*op)?;
    if !is_ordered_integer_operand(left) || !is_ordered_integer_operand(right) {
        return None;
    }
    Some(PureExpr::BinOp(
        Arc::clone(left),
        negated,
        Arc::clone(right),
    ))
}

fn ite_comparison_cases(cond: &PureExpr, then_cmp: PureExpr, else_cmp: PureExpr) -> PureExpr {
    let then_case = PureExpr::BinOp(Arc::new(cond.clone()), BinOp::Implies, Arc::new(then_cmp));
    let negated_cond = PureExpr::UnOp(UnOp::Not, Arc::new(cond.clone()));
    let else_case = PureExpr::BinOp(Arc::new(negated_cond), BinOp::Implies, Arc::new(else_cmp));
    PureExpr::BinOp(Arc::new(then_case), BinOp::And, Arc::new(else_case))
}

/// Split one conditional comparison operand into two guarded comparisons.
///
/// `(if c { t } else { e }) op rhs` is definitionally equivalent to
/// `(c -> t op rhs) && (!c -> e op rhs)`.  Recursion through the ordinary
/// boolean prover handles nested conditionals one layer at a time.  Splitting
/// the left operand first makes the rewrite deterministic when both sides are
/// conditional.
fn split_comparison_ite(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<PureExpr> {
    if let PureExpr::Ite(cond, then_arm, else_arm) = left {
        return Some(ite_comparison_cases(
            cond,
            PureExpr::BinOp(Arc::clone(then_arm), op, Arc::new(right.clone())),
            PureExpr::BinOp(Arc::clone(else_arm), op, Arc::new(right.clone())),
        ));
    }
    if let PureExpr::Ite(cond, then_arm, else_arm) = right {
        return Some(ite_comparison_cases(
            cond,
            PureExpr::BinOp(Arc::new(left.clone()), op, Arc::clone(then_arm)),
            PureExpr::BinOp(Arc::new(left.clone()), op, Arc::clone(else_arm)),
        ));
    }
    None
}

fn prove_ite(
    cond: &PureExpr,
    then_expr: &PureExpr,
    else_expr: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match prove_bool_with_env(cond, env, context) {
        TruthValue::True { .. } => prove_bool_with_env(then_expr, env, context),
        TruthValue::False { .. } => prove_bool_with_env(else_expr, env, context),
        TruthValue::Unknown { reason } => {
            let then_truth = prove_bool_with_env(then_expr, env, context);
            let else_truth = prove_bool_with_env(else_expr, env, context);
            match (then_truth, else_truth) {
                (TruthValue::True { .. }, TruthValue::True { .. }) => TruthValue::True {
                    rule: "ite-branches-true",
                },
                (TruthValue::False { .. }, TruthValue::False { .. }) => TruthValue::False {
                    rule: "ite-branches-false",
                },
                _ => TruthValue::Unknown { reason },
            }
        }
    }
}

fn prove_comparison(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    if let Some(reason) =
        checked_bitwise_replay_diagnostic(left).or_else(|| checked_bitwise_replay_diagnostic(right))
    {
        return TruthValue::unknown(reason);
    }

    if left == right {
        return match op {
            BinOp::Eq | BinOp::Le | BinOp::Ge => TruthValue::True {
                rule: "reflexive-comparison",
            },
            BinOp::Ne | BinOp::Lt | BinOp::Gt => TruthValue::False {
                rule: "irreflexive-comparison",
            },
            _ => unreachable!("comparison operators handled by caller"),
        };
    }

    if let Some(result) = prove_pointer_summary_comparison(left, op, right, env, context) {
        return result;
    }

    if let Some(reason) = pointer_replay_diagnostic(left, right, env) {
        return TruthValue::unknown(reason);
    }

    if let Some(result) = prove_bitwise_comparison(left, op, right) {
        return result;
    }

    match (eval_value(left), eval_value(right)) {
        (Some(left), Some(right)) => compare_known_values(left, op, right),
        _ => prove_linear_comparison(left, op, right).unwrap_or_else(|| {
            TruthValue::unknown("comparison contains symbolic or unsupported operands")
        }),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PointerReplayKind {
    Thin,
    Fat,
}

fn prove_pointer_summary_comparison(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    env: &HashMap<String, ExprSort>,
    context: &NativeReplayContext<'_>,
) -> Option<TruthValue> {
    let pointer_kind = pointer_kind_for_expr(left, env).max(pointer_kind_for_expr(right, env))?;
    let relation = context.summary_facts.iter().find_map(|fact| {
        let relation = pointer_summary_relation(fact, pointer_kind)?;
        summary_fact_matches_terms(fact, left, right).then_some(relation)
    })?;

    match (relation, op) {
        (PointerSummaryRelation::Equal, BinOp::Eq)
        | (PointerSummaryRelation::Disjoint, BinOp::Ne) => Some(TruthValue::True {
            rule: relation.rule(pointer_kind),
        }),
        (PointerSummaryRelation::Equal, BinOp::Ne)
        | (PointerSummaryRelation::Disjoint, BinOp::Eq) => Some(TruthValue::False {
            rule: relation.rule(pointer_kind),
        }),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PointerSummaryRelation {
    Equal,
    Disjoint,
}

impl PointerSummaryRelation {
    const fn rule(self, pointer_kind: PointerReplayKind) -> &'static str {
        match (self, pointer_kind) {
            (Self::Equal, PointerReplayKind::Thin) => "pointer-provenance-summary-equality",
            (Self::Equal, PointerReplayKind::Fat) => "fat-pointer-metadata-summary-equality",
            (Self::Disjoint, PointerReplayKind::Thin) => "pointer-provenance-summary-disjointness",
            (Self::Disjoint, PointerReplayKind::Fat) => "fat-pointer-metadata-summary-disjointness",
        }
    }
}

fn pointer_summary_relation(
    fact: &BundleSummaryFact,
    pointer_kind: PointerReplayKind,
) -> Option<PointerSummaryRelation> {
    match (&fact.kind, pointer_kind) {
        (
            BundleSummaryFactKind::PointerProvenanceEq { .. }
            | BundleSummaryFactKind::PointerProvenanceEqBinding { .. },
            PointerReplayKind::Thin,
        )
        | (
            BundleSummaryFactKind::FatPointerMetadataEq { .. }
            | BundleSummaryFactKind::FatPointerMetadataEqBinding { .. },
            PointerReplayKind::Fat,
        ) => Some(PointerSummaryRelation::Equal),
        (
            BundleSummaryFactKind::PointerProvenanceDisjointBinding { .. },
            PointerReplayKind::Thin,
        )
        | (
            BundleSummaryFactKind::FatPointerMetadataDisjointBinding { .. },
            PointerReplayKind::Fat,
        ) => Some(PointerSummaryRelation::Disjoint),
        _ => None,
    }
}

fn summary_fact_matches_terms(fact: &BundleSummaryFact, left: &PureExpr, right: &PureExpr) -> bool {
    let Some(endpoints) = summary_fact_endpoints(fact) else {
        return false;
    };
    match endpoints {
        SummaryFactEndpoints::Textual {
            left: fact_left,
            right: fact_right,
        } => {
            let Ok(fact_left) = parse_contract(fact_left.trim()) else {
                return false;
            };
            let Ok(fact_right) = parse_contract(fact_right.trim()) else {
                return false;
            };
            (left == &fact_left && right == &fact_right)
                || (left == &fact_right && right == &fact_left)
        }
        SummaryFactEndpoints::Binding {
            left: fact_left,
            right: fact_right,
        } => {
            (expr_matches_summary_binding(left, fact_left)
                && expr_matches_summary_binding(right, fact_right))
                || (expr_matches_summary_binding(left, fact_right)
                    && expr_matches_summary_binding(right, fact_left))
        }
    }
}

fn expr_matches_summary_binding(expr: &PureExpr, binding: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == binding)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SummaryFactEndpoints<'a> {
    Textual { left: &'a str, right: &'a str },
    Binding { left: &'a str, right: &'a str },
}

fn summary_fact_endpoints(fact: &BundleSummaryFact) -> Option<SummaryFactEndpoints<'_>> {
    match &fact.kind {
        BundleSummaryFactKind::PointerProvenanceEq { left, right }
        | BundleSummaryFactKind::FatPointerMetadataEq { left, right } => {
            Some(SummaryFactEndpoints::Textual { left, right })
        }
        BundleSummaryFactKind::PointerProvenanceEqBinding { left, right }
        | BundleSummaryFactKind::PointerProvenanceDisjointBinding { left, right }
        | BundleSummaryFactKind::FatPointerMetadataEqBinding { left, right }
        | BundleSummaryFactKind::FatPointerMetadataDisjointBinding { left, right } => {
            Some(SummaryFactEndpoints::Binding { left, right })
        }
        BundleSummaryFactKind::Other { .. } => None,
    }
}

fn pointer_replay_diagnostic(
    left: &PureExpr,
    right: &PureExpr,
    env: &HashMap<String, ExprSort>,
) -> Option<String> {
    let kind = pointer_kind_for_expr(left, env).max(pointer_kind_for_expr(right, env))?;
    match kind {
        PointerReplayKind::Thin => Some(
            "pointer replay requires alias/provenance summary evidence before non-reflexive pointer comparison can be checked"
                .to_string(),
        ),
        PointerReplayKind::Fat => Some(
            "fat-pointer metadata replay requires data-address and metadata summary evidence before non-reflexive pointer comparison can be checked"
                .to_string(),
        ),
    }
}

fn pointer_kind_for_expr(
    expr: &PureExpr,
    env: &HashMap<String, ExprSort>,
) -> Option<PointerReplayKind> {
    match expr {
        PureExpr::Var(name, sort) => sort
            .as_ref()
            .or_else(|| env.get(name))
            .and_then(pointer_kind_from_sort),
        PureExpr::Old(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            pointer_kind_for_expr(inner, env)
        }
        PureExpr::Ite(_, then_expr, else_expr) => {
            pointer_kind_for_expr(then_expr, env).max(pointer_kind_for_expr(else_expr, env))
        }
        PureExpr::Let { var, value, body } => pointer_kind_for_expr(
            &inline_let_binding_for_native_replay(var, value, body)?,
            env,
        ),
        PureExpr::Bool(_)
        | PureExpr::Int(_)
        | PureExpr::Float(_)
        | PureExpr::BinOp(_, _, _)
        | PureExpr::UnOp(_, _)
        | PureExpr::Deref(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. } => None,
    }
}

fn pointer_kind_from_sort(sort: &ExprSort) -> Option<PointerReplayKind> {
    match sort {
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => {
            Some(pointer_kind_from_referent_sort(inner))
        }
        _ => None,
    }
}

fn pointer_kind_from_referent_sort(sort: &ExprSort) -> PointerReplayKind {
    match sort {
        ExprSort::Seq | ExprSort::FMap => PointerReplayKind::Fat,
        _ => PointerReplayKind::Thin,
    }
}

fn with_bound_sort<T>(
    env: &mut HashMap<String, ExprSort>,
    var: &str,
    var_sort: Option<&ExprSort>,
    f: impl FnOnce(&mut HashMap<String, ExprSort>) -> T,
) -> T {
    let previous = match var_sort {
        Some(sort) => env.insert(var.to_string(), sort.clone()),
        None => env.remove(var),
    };
    let result = f(env);
    match previous {
        Some(sort) => {
            env.insert(var.to_string(), sort);
        }
        None => {
            env.remove(var);
        }
    }
    result
}

fn prove_linear_implication(antecedent: &PureExpr, consequent: &PureExpr) -> Option<TruthValue> {
    let (goal, strict_goal) = linear_goal_from_comparison(consequent)?;
    if let Some(minimum) =
        goal.minimum_with_linear_constraints(&linear_constraints_from_assumption(antecedent))
    {
        let proved = if strict_goal {
            minimum > 0
        } else {
            minimum >= 0
        };
        if proved {
            return Some(TruthValue::True {
                rule: "linear-int-implication",
            });
        }
    }

    integer_bounds_from_assumption(antecedent)?
        .into_iter()
        .find_map(|bound| {
            let minimum = goal.minimum_with_bound(&bound)?;
            let proved = if strict_goal {
                minimum > 0
            } else {
                minimum >= 0
            };
            proved.then_some(TruthValue::True {
                rule: "linear-int-implication",
            })
        })
}

fn prove_linear_comparison(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<TruthValue> {
    let (difference, strict) = linear_goal(left, op, right)?;
    if !difference.terms.is_empty() {
        return None;
    }

    let proved = if strict {
        difference.constant > 0
    } else {
        difference.constant >= 0
    };
    Some(TruthValue::from_bool(proved, "linear-int-comparison"))
}

fn prove_int_arithmetic_implication(
    antecedent: &PureExpr,
    consequent: &PureExpr,
) -> Option<TruthValue> {
    let constraints = linear_constraints_from_assumption(antecedent);
    if constraints.is_empty() {
        return None;
    }

    let consequent = substitute_equalities_from_assumption(antecedent, consequent);
    prove_int_arithmetic_predicate_with_constraints(&consequent, &constraints)
}

fn prove_int_arithmetic_predicate_with_constraints(
    expr: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<TruthValue> {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            prove_int_arithmetic_predicate_with_constraints(left, constraints)?;
            prove_int_arithmetic_predicate_with_constraints(right, constraints)?;
            Some(TruthValue::True {
                rule: "int-arithmetic-implication",
            })
        }
        PureExpr::BinOp(guard, BinOp::Implies, conclusion) => {
            // The conclusion of an implication is checked under both the
            // enclosing constraints and its own guard.  This is what carries
            // branch facts produced by `split_comparison_ite` into each arm.
            let mut extended = constraints.to_vec();
            collect_linear_constraints(guard, &mut extended);
            prove_int_arithmetic_predicate_with_constraints(conclusion, &extended)
        }
        PureExpr::BinOp(left, op, right)
            if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) =>
        {
            if let Some(rewritten) = split_comparison_ite(left, *op, right) {
                prove_int_arithmetic_predicate_with_constraints(&rewritten, constraints)
            } else {
                prove_int_arithmetic_comparison_with_constraints(left, *op, right, constraints)
            }
        }
        _ => None,
    }
}

fn prove_int_arithmetic_comparison_with_constraints(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<TruthValue> {
    let (minimum, strict) = match op {
        BinOp::Gt => (lower_bound_int_difference(left, right, constraints)?, true),
        BinOp::Ge => (lower_bound_int_difference(left, right, constraints)?, false),
        BinOp::Lt => (lower_bound_int_difference(right, left, constraints)?, true),
        BinOp::Le => (lower_bound_int_difference(right, left, constraints)?, false),
        _ => return None,
    };
    let proved = if strict { minimum > 0 } else { minimum >= 0 };
    proved.then_some(TruthValue::True {
        rule: "int-arithmetic-implication",
    })
}

fn substitute_equalities_from_assumption(assumption: &PureExpr, expr: &PureExpr) -> PureExpr {
    // `old(x)` denotes the entry-state value of the program variable, not an
    // application of an ordinary congruent function to its current-state
    // value. Consequently an antecedent equality such as `x == 0` must not
    // rewrite `old(x)` to `old(0)`. Keep the whole consequent opaque to this
    // current-state substitution pass when it contains an entry-state term;
    // the linear prover can still reason about explicit `old(x)` constraints
    // because `LinearInt` gives those variables a distinct namespace.
    if expr.any_recursive(|candidate| matches!(candidate, PureExpr::Old(_))) {
        return expr.clone();
    }
    let mut substitutions = HashMap::new();
    collect_equality_substitutions(assumption, &mut substitutions);
    if substitutions.is_empty() {
        expr.clone()
    } else {
        expr.substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default())
    }
}

fn collect_equality_substitutions(expr: &PureExpr, substitutions: &mut HashMap<String, PureExpr>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_equality_substitutions(left, substitutions);
            collect_equality_substitutions(right, substitutions);
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            insert_equality_substitution(left, right, substitutions);
            insert_equality_substitution(right, left, substitutions);
        }
        _ => {}
    }
}

fn insert_equality_substitution(
    candidate_var: &PureExpr,
    replacement: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    let PureExpr::Var(name, sort) = candidate_var else {
        return;
    };
    if !matches!(sort.as_ref(), None | Some(ExprSort::Int | ExprSort::Bool)) {
        return;
    }
    if contains_var(replacement, name) {
        return;
    }
    match substitutions.get(name) {
        Some(existing) if existing == replacement => {}
        Some(_) => {
            substitutions.remove(name);
        }
        None => {
            substitutions.insert(name.clone(), replacement.clone());
        }
    }
}

fn contains_var(expr: &PureExpr, name: &str) -> bool {
    match expr {
        PureExpr::Var(candidate, _) => candidate == name,
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_var(inner, name),
        PureExpr::BinOp(left, _, right) => contains_var(left, name) || contains_var(right, name),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_var(cond, name)
                || contains_var(then_expr, name)
                || contains_var(else_expr, name)
        }
        PureExpr::Let { var, value, body } => {
            contains_var(value, name) || (var != name && contains_var(body, name))
        }
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            var != name && contains_var(body, name)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_var(receiver, name) || args.iter().any(|arg| contains_var(arg, name))
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(|arg| contains_var(arg, name)),
        PureExpr::Match { scrutinee, arms } => {
            contains_var(scrutinee, name) || arms.iter().any(|arm| contains_var(&arm.body, name))
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_var(assumption, name) || contains_var(body, name)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_var(obligation, name) || contains_var(body, name)
        }
        PureExpr::Closure { body, .. } => contains_var(body, name),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
    }
}

fn upper_bound_int_expr(expr: &PureExpr, constraints: &[LinearConstraint]) -> Option<i64> {
    if let Some(linear) = LinearInt::from_expr(expr) {
        return linear.maximum_with_linear_constraints(constraints);
    }

    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => Some(
            upper_bound_int_expr(left, constraints)?
                .checked_add(upper_bound_int_expr(right, constraints)?)?,
        ),
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            upper_bound_int_difference(left, right, constraints)
        }
        PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) => {
            // `dividend_max / divisor_min` (toward zero) bounds both Euclidean
            // `Div` and truncated `DivTrunc` above when divisor > 0 and the
            // dividend's max is non-negative (for a < 0, a/b <= 0 <= the bound).
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let dividend_max = upper_bound_int_expr(dividend, constraints)?;
            if divisor_min > 0 && dividend_max >= 0 {
                return Some(dividend_max / divisor_min);
            }
            None
        }
        PureExpr::BinOp(_dividend, BinOp::Mod | BinOp::RemTrunc, divisor) => {
            // `(a mod b) <= b - 1` whenever `b >= 1`, for *any* dividend. This
            // holds under both SMT-LIB Euclidean `(mod a b)` and truncated
            // remainder (`a % b` lies in `(-b, b)`), so it is sound on the
            // native evaluator and the SMT backend alike. With a known divisor
            // maximum this yields a concrete upper bound.
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let divisor_max = upper_bound_int_expr(divisor, constraints)?;
            if divisor_min >= 1 {
                return divisor_max.checked_sub(1);
            }
            None
        }
        _ => None,
    }
}

fn upper_bound_int_difference(
    left: &PureExpr,
    right: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<i64> {
    if left == right {
        return Some(0);
    }

    let difference = PureExpr::BinOp(Arc::new(left.clone()), BinOp::Sub, Arc::new(right.clone()));
    if let Some(linear) = LinearInt::from_expr(&difference) {
        return linear.maximum_with_linear_constraints(constraints);
    }

    let left_max = upper_bound_int_expr(left, constraints)?;
    let right_min = lower_bound_int_expr(right, constraints)?;
    left_max.checked_sub(right_min)
}

fn lower_bound_int_difference(
    left: &PureExpr,
    right: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<i64> {
    if left == right {
        return Some(0);
    }

    let difference = PureExpr::BinOp(Arc::new(left.clone()), BinOp::Sub, Arc::new(right.clone()));
    if let Some(linear) = LinearInt::from_expr(&difference) {
        return linear.minimum_with_linear_constraints(constraints);
    }

    // `left - (dividend % divisor)`. Under `BinOp::Mod`, `(a mod b) <= b - 1`
    // whenever `b >= 1`, so `left - (dividend % divisor) >= (left - divisor) + 1`
    // for a positive divisor. This holds under both Euclidean `(mod a b)` and
    // truncated remainder (`a % b` lies in `(-b, b)`), so it is sound on the
    // native evaluator and the SMT backend alike. Discharges the keystone
    // `(ring_head + base) % len < len` under `len >= 1`.
    if let PureExpr::BinOp(_dividend, BinOp::Mod | BinOp::RemTrunc, divisor) = right {
        let divisor_min = lower_bound_int_expr(divisor, constraints)?;
        if divisor_min >= 1 {
            let left_minus_divisor = lower_bound_int_difference(left, divisor, constraints)?;
            return left_minus_divisor.checked_add(1);
        }
    }

    if let Some(right_constant) = constant_int(right) {
        return lower_bound_int_expr(left, constraints)?.checked_sub(right_constant);
    }

    if let PureExpr::BinOp(add_left, BinOp::Add, add_right) = left {
        if add_left.as_ref() == right {
            return lower_bound_int_expr(add_right, constraints);
        }
        if add_right.as_ref() == right {
            return lower_bound_int_expr(add_left, constraints);
        }
    }

    if let PureExpr::BinOp(r_left, BinOp::Add, r_right) = right {
        if r_left.as_ref() == left {
            return upper_bound_int_expr(r_right, constraints).map(|v| -v);
        }
        if r_right.as_ref() == left {
            return upper_bound_int_expr(r_left, constraints).map(|v| -v);
        }
        // Handle hi - (lo + (hi - lo) / 2)
        if let Some(linear_diff) = LinearInt::from_expr(&PureExpr::BinOp(
            Arc::new(left.clone()),
            BinOp::Sub,
            r_left.clone(),
        )) {
            if let PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) =
                r_right.as_ref()
            {
                if let Some(linear_dividend) = LinearInt::from_expr(dividend) {
                    if linear_diff == linear_dividend {
                        let x_min = linear_diff.minimum_with_linear_constraints(constraints)?;
                        let k_min = lower_bound_int_expr(divisor, constraints)?;
                        if x_min >= 0 && k_min >= 1 {
                            return Some(0);
                        }
                    }
                }
            }
        }
    }

    None
}

fn lower_bound_int_expr(expr: &PureExpr, constraints: &[LinearConstraint]) -> Option<i64> {
    if let Some(linear) = LinearInt::from_expr(expr) {
        return linear.minimum_with_linear_constraints(constraints);
    }

    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => lower_bound_int_expr(left, constraints)?
            .checked_add(lower_bound_int_expr(right, constraints)?),
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            lower_bound_int_difference(left, right, constraints)
        }
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            if let Some(factor) = constant_int(left) {
                return lower_bound_scaled_expr(factor, right, constraints);
            }
            if let Some(factor) = constant_int(right) {
                return lower_bound_scaled_expr(factor, left, constraints);
            }
            None
        }
        PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) => {
            // `a / b >= 0` for a non-negative dividend and positive divisor —
            // true for both Euclidean and truncated (toward-zero) division.
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let dividend_min = lower_bound_int_expr(dividend, constraints)?;
            (divisor_min > 0 && dividend_min >= 0).then_some(0)
        }
        PureExpr::BinOp(dividend, BinOp::Mod | BinOp::RemTrunc, divisor) => {
            // `a % b >= 0` for a non-negative dividend and positive divisor —
            // true for both Euclidean and truncated (sign-of-dividend) remainder.
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let dividend_min = lower_bound_int_expr(dividend, constraints)?;
            (divisor_min > 0 && dividend_min >= 0).then_some(0)
        }
        PureExpr::Let { var, value, body } => lower_bound_int_expr(
            &inline_let_binding_for_native_replay(var, value, body)?,
            constraints,
        ),
        // A compound entry-state expression must not inherit bounds on its
        // current-state variables. `LinearInt::from_expr` above deliberately
        // supports the sound atomic `old(x)` case with a distinct symbol; all
        // other `old(...)` shapes remain outside this native bound fragment.
        PureExpr::Old(_) => None,
        _ => None,
    }
}

fn lower_bound_scaled_expr(
    factor: i64,
    expr: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<i64> {
    if factor < 0 {
        return None;
    }
    lower_bound_int_expr(expr, constraints)?.checked_mul(factor)
}

fn constant_int(expr: &PureExpr) -> Option<i64> {
    match eval_value(expr)? {
        KnownValue::Int(value) => Some(value),
        KnownValue::Bool(_) => None,
    }
}

fn linear_goal_from_comparison(expr: &PureExpr) -> Option<(LinearInt, bool)> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    linear_goal(left, *op, right)
}

fn linear_goal(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<(LinearInt, bool)> {
    match op {
        BinOp::Gt => Some((
            LinearInt::from_expr(left)?.sub(LinearInt::from_expr(right)?)?,
            true,
        )),
        BinOp::Ge => Some((
            LinearInt::from_expr(left)?.sub(LinearInt::from_expr(right)?)?,
            false,
        )),
        BinOp::Lt => Some((
            LinearInt::from_expr(right)?.sub(LinearInt::from_expr(left)?)?,
            true,
        )),
        BinOp::Le => Some((
            LinearInt::from_expr(right)?.sub(LinearInt::from_expr(left)?)?,
            false,
        )),
        _ => None,
    }
}

fn integer_bound_from_comparison(expr: &PureExpr) -> Option<IntegerBound> {
    let (goal, strict) = linear_goal_from_comparison(expr)?;
    let (var, coefficient) = single_linear_term(&goal.terms)?;
    match coefficient {
        1 => {
            let mut value = goal.constant.checked_neg()?;
            if strict {
                value = value.checked_add(1)?;
            }
            Some(IntegerBound {
                var: var.to_string(),
                kind: IntegerBoundKind::Lower,
                value,
            })
        }
        -1 => {
            let mut value = goal.constant;
            if strict {
                value = value.checked_sub(1)?;
            }
            Some(IntegerBound {
                var: var.to_string(),
                kind: IntegerBoundKind::Upper,
                value,
            })
        }
        _ => None,
    }
}

fn integer_bounds_from_assumption(expr: &PureExpr) -> Option<Vec<IntegerBound>> {
    if let PureExpr::BinOp(left, BinOp::And, right) = expr {
        let mut bounds = Vec::new();
        collect_integer_bounds(left, &mut bounds);
        collect_integer_bounds(right, &mut bounds);
        (!bounds.is_empty()).then_some(bounds)
    } else {
        let normalized = denegate_ordered_integer_comparison(expr);
        integer_bound_from_comparison(normalized.as_ref().unwrap_or(expr)).map(|bound| vec![bound])
    }
}

fn collect_integer_bounds(expr: &PureExpr, bounds: &mut Vec<IntegerBound>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_integer_bounds(left, bounds);
            collect_integer_bounds(right, bounds);
        }
        _ => {
            if let Some(normalized) = denegate_ordered_integer_comparison(expr) {
                collect_integer_bounds(&normalized, bounds);
            } else if let Some(bound) = integer_bound_from_comparison(expr) {
                bounds.push(bound);
            }
        }
    }
}

fn linear_constraints_from_assumption(expr: &PureExpr) -> Vec<LinearConstraint> {
    let mut constraints = Vec::new();
    collect_linear_constraints(expr, &mut constraints);
    constraints
}

fn collect_linear_constraints(expr: &PureExpr, constraints: &mut Vec<LinearConstraint>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_linear_constraints(left, constraints);
            collect_linear_constraints(right, constraints);
        }
        _ => {
            if let Some(normalized) = denegate_ordered_integer_comparison(expr) {
                collect_linear_constraints(&normalized, constraints);
            } else if let Some((linear, strict)) = linear_goal_from_comparison(expr) {
                constraints.push(LinearConstraint {
                    expr: linear,
                    strict,
                });
            }
        }
    }
}

fn single_linear_term(terms: &BTreeMap<String, i64>) -> Option<(&str, i64)> {
    let mut iter = terms.iter();
    let (var, coefficient) = iter.next()?;
    iter.next()
        .is_none()
        .then_some((var.as_str(), *coefficient))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LinearConstraint {
    expr: LinearInt,
    strict: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IntegerBound {
    var: String,
    kind: IntegerBoundKind,
    value: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IntegerBoundKind {
    Lower,
    Upper,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LinearInt {
    constant: i64,
    terms: BTreeMap<String, i64>,
}

impl LinearInt {
    fn constant(value: i64) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    fn var(name: String) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(name, 1);
        Self { constant: 0, terms }
    }

    fn from_expr(expr: &PureExpr) -> Option<Self> {
        match expr {
            PureExpr::Int(value) => Some(Self::constant(*value)),
            PureExpr::Var(name, sort)
                if sort
                    .as_ref()
                    .is_none_or(|sort| *sort == crate::formula::ExprSort::Int) =>
            {
                Some(Self::var(name.clone()))
            }
            PureExpr::UnOp(UnOp::Neg, inner) => Self::from_expr(inner)?.neg(),
            PureExpr::BinOp(left, BinOp::Add, right) => {
                Self::from_expr(left)?.add(Self::from_expr(right)?)
            }
            PureExpr::BinOp(left, BinOp::Sub, right) => {
                Self::from_expr(left)?.sub(Self::from_expr(right)?)
            }
            PureExpr::BinOp(left, BinOp::Mul, right) => {
                let left = Self::from_expr(left)?;
                let right = Self::from_expr(right)?;
                if let Some(factor) = left.constant_value() {
                    right.mul_constant(factor)
                } else if let Some(factor) = right.constant_value() {
                    left.mul_constant(factor)
                } else {
                    None
                }
            }
            PureExpr::Old(inner) => match inner.as_ref() {
                PureExpr::Var(name, sort)
                    if sort
                        .as_ref()
                        .is_none_or(|sort| *sort == crate::formula::ExprSort::Int) =>
                {
                    Some(Self::var(format!("old({name})")))
                }
                _ => None,
            },
            PureExpr::Let { var, value, body } => {
                Self::from_expr(&inline_let_binding_for_native_replay(var, value, body)?)
            }
            _ => None,
        }
    }

    fn constant_value(&self) -> Option<i64> {
        self.terms.is_empty().then_some(self.constant)
    }

    fn add(self, other: Self) -> Option<Self> {
        let mut result = Self {
            constant: self.constant.checked_add(other.constant)?,
            terms: self.terms,
        };
        for (var, coefficient) in other.terms {
            result.add_term(var, coefficient)?;
        }
        Some(result)
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.add(other.neg()?)
    }

    fn neg(mut self) -> Option<Self> {
        self.constant = self.constant.checked_neg()?;
        for coefficient in self.terms.values_mut() {
            *coefficient = coefficient.checked_neg()?;
        }
        Some(self)
    }

    fn add_term(&mut self, var: String, coefficient: i64) -> Option<()> {
        let updated = self
            .terms
            .get(&var)
            .copied()
            .unwrap_or(0)
            .checked_add(coefficient)?;
        if updated == 0 {
            self.terms.remove(&var);
        } else {
            self.terms.insert(var, updated);
        }
        Some(())
    }

    fn mul_constant(mut self, factor: i64) -> Option<Self> {
        self.constant = self.constant.checked_mul(factor)?;
        for coefficient in self.terms.values_mut() {
            *coefficient = coefficient.checked_mul(factor)?;
        }
        self.terms.retain(|_, coefficient| *coefficient != 0);
        Some(self)
    }

    fn minimum_with_bound(&self, bound: &IntegerBound) -> Option<i64> {
        let (var, coefficient) = single_linear_term(&self.terms)?;
        if var != bound.var {
            return None;
        }

        let uses_bound = match bound.kind {
            IntegerBoundKind::Lower => coefficient > 0,
            IntegerBoundKind::Upper => coefficient < 0,
        };
        if !uses_bound {
            return None;
        }

        coefficient
            .checked_mul(bound.value)?
            .checked_add(self.constant)
    }

    fn maximum_with_linear_constraints(&self, constraints: &[LinearConstraint]) -> Option<i64> {
        if self.terms.is_empty() {
            return Some(self.constant);
        }
        let mut neg = self.clone();
        neg.constant = neg.constant.checked_neg()?;
        for val in neg.terms.values_mut() {
            *val = (*val).checked_neg()?;
        }
        neg.minimum_with_linear_constraints(constraints).map(|v| -v)
    }

    fn minimum_with_linear_constraints(&self, constraints: &[LinearConstraint]) -> Option<i64> {
        if self.terms.is_empty() {
            return Some(self.constant);
        }
        constraints
            .iter()
            .find_map(|constraint| self.minimum_with_linear_constraint(constraint))
    }

    fn minimum_with_linear_constraint(&self, constraint: &LinearConstraint) -> Option<i64> {
        let factor = positive_term_scale(&self.terms, &constraint.expr.terms)?;
        let residual = self
            .constant
            .checked_sub(constraint.expr.constant.checked_mul(factor)?)?;
        let constraint_min = i64::from(constraint.strict);
        factor.checked_mul(constraint_min)?.checked_add(residual)
    }
}

fn positive_term_scale(
    goal_terms: &BTreeMap<String, i64>,
    constraint_terms: &BTreeMap<String, i64>,
) -> Option<i64> {
    if constraint_terms.is_empty() || goal_terms.len() != constraint_terms.len() {
        return None;
    }

    let mut scale = None;
    for (var, constraint_coefficient) in constraint_terms {
        if *constraint_coefficient == 0 {
            return None;
        }
        let goal_coefficient = *goal_terms.get(var)?;
        if goal_coefficient % constraint_coefficient != 0 {
            return None;
        }
        let candidate = goal_coefficient / constraint_coefficient;
        if candidate <= 0 {
            return None;
        }
        match scale {
            Some(scale) if scale != candidate => return None,
            Some(_) => {}
            None => scale = Some(candidate),
        }
    }
    scale
}

fn prove_bitwise_comparison(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<TruthValue> {
    if !matches!(op, BinOp::Eq | BinOp::Ne) {
        return None;
    }
    if !contains_bitwise_expr(left) && !contains_bitwise_expr(right) {
        return None;
    }

    let left = normalize_bitwise_identities(left);
    let right = normalize_bitwise_identities(right);
    if left == right {
        return Some(TruthValue::from_bool(
            op == BinOp::Eq,
            "checked-bitwise-identity",
        ));
    }

    match (eval_value(&left), eval_value(&right)) {
        (Some(left), Some(right)) => Some(compare_known_values_with_int_rule(
            left,
            op,
            right,
            "checked-bitwise-constant-comparison",
        )),
        _ => None,
    }
}

fn checked_bitwise_replay_diagnostic(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::BinOp(left, BinOp::Shl | BinOp::Shr, right) => {
            if checked_shift_amount_from_expr(right).is_none() {
                return Some(
                    "bitwise shift count is not a known checked i64 shift amount".to_string(),
                );
            }
            checked_bitwise_replay_diagnostic(left)
                .or_else(|| checked_bitwise_replay_diagnostic(right))
        }
        PureExpr::BinOp(left, _, right) => checked_bitwise_replay_diagnostic(left)
            .or_else(|| checked_bitwise_replay_diagnostic(right)),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => checked_bitwise_replay_diagnostic(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => checked_bitwise_replay_diagnostic(cond)
            .or_else(|| checked_bitwise_replay_diagnostic(then_expr))
            .or_else(|| checked_bitwise_replay_diagnostic(else_expr)),
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Closure { body, .. } => checked_bitwise_replay_diagnostic(body),
        PureExpr::Let { value, body, .. } => checked_bitwise_replay_diagnostic(value)
            .or_else(|| checked_bitwise_replay_diagnostic(body)),
        PureExpr::LetAssume { assumption, body } => checked_bitwise_replay_diagnostic(assumption)
            .or_else(|| checked_bitwise_replay_diagnostic(body)),
        PureExpr::LetObligation { obligation, body } => {
            checked_bitwise_replay_diagnostic(obligation)
                .or_else(|| checked_bitwise_replay_diagnostic(body))
        }
        PureExpr::Match { scrutinee, arms } => checked_bitwise_replay_diagnostic(scrutinee)
            .or_else(|| {
                arms.iter()
                    .find_map(|arm| checked_bitwise_replay_diagnostic(&arm.body))
            }),
        PureExpr::MethodCall { receiver, args, .. } => checked_bitwise_replay_diagnostic(receiver)
            .or_else(|| args.iter().find_map(checked_bitwise_replay_diagnostic)),
        PureExpr::LogicFnCall { args, .. } => {
            args.iter().find_map(checked_bitwise_replay_diagnostic)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => None,
    }
}

fn checked_shift_amount_from_expr(expr: &PureExpr) -> Option<u32> {
    match eval_value(expr)? {
        KnownValue::Int(amount) => checked_shift_amount(amount),
        KnownValue::Bool(_) => None,
    }
}

fn checked_shift_amount(amount: i64) -> Option<u32> {
    u32::try_from(amount)
        .ok()
        .filter(|amount| *amount < i64::BITS)
}

fn contains_bitwise_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(left, op, right) => {
            matches!(
                op,
                BinOp::Shl | BinOp::Shr | BinOp::BitAnd | BinOp::BitXor | BinOp::BitOr
            ) || contains_bitwise_expr(left)
                || contains_bitwise_expr(right)
        }
        PureExpr::UnOp(UnOp::BitNot, _) => true,
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_bitwise_expr(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_bitwise_expr(cond)
                || contains_bitwise_expr(then_expr)
                || contains_bitwise_expr(else_expr)
        }
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Closure { body, .. } => contains_bitwise_expr(body),
        PureExpr::Let { value, body, .. } => {
            contains_bitwise_expr(value) || contains_bitwise_expr(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_bitwise_expr(assumption) || contains_bitwise_expr(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_bitwise_expr(obligation) || contains_bitwise_expr(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_bitwise_expr(scrutinee)
                || arms.iter().any(|arm| contains_bitwise_expr(&arm.body))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_bitwise_expr(receiver) || args.iter().any(contains_bitwise_expr)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(contains_bitwise_expr),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
    }
}

fn normalize_bitwise_identities(expr: &PureExpr) -> PureExpr {
    if let Some(KnownValue::Int(value)) = eval_value(expr) {
        return PureExpr::Int(value);
    }

    match expr {
        PureExpr::BinOp(left, op, right) => {
            let left = normalize_bitwise_identities(left);
            let right = normalize_bitwise_identities(right);
            normalize_bitwise_binary(left, *op, right)
        }
        PureExpr::UnOp(UnOp::BitNot, inner) => {
            let inner = normalize_bitwise_identities(inner);
            if let PureExpr::UnOp(UnOp::BitNot, nested) = &inner {
                return nested.as_ref().clone();
            }
            PureExpr::UnOp(UnOp::BitNot, Arc::new(inner))
        }
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(normalize_bitwise_identities(inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_bitwise_identities(cond)),
            Arc::new(normalize_bitwise_identities(then_expr)),
            Arc::new(normalize_bitwise_identities(else_expr)),
        ),
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(normalize_bitwise_identities(value)),
            body: Arc::new(normalize_bitwise_identities(body)),
        },
        _ => expr.clone(),
    }
}

fn normalize_bitwise_binary(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    match op {
        BinOp::BitAnd => {
            if is_int_literal(&left, 0) || is_int_literal(&right, 0) {
                return PureExpr::Int(0);
            }
            if is_int_literal(&left, -1) {
                return right;
            }
            if is_int_literal(&right, -1) || left == right {
                return left;
            }
        }
        BinOp::BitOr => {
            if is_int_literal(&left, -1) || is_int_literal(&right, -1) {
                return PureExpr::Int(-1);
            }
            if is_int_literal(&left, 0) {
                return right;
            }
            if is_int_literal(&right, 0) || left == right {
                return left;
            }
        }
        BinOp::BitXor => {
            if left == right {
                return PureExpr::Int(0);
            }
            if is_int_literal(&left, 0) {
                return right;
            }
            if is_int_literal(&right, 0) {
                return left;
            }
        }
        BinOp::Shl | BinOp::Shr if is_int_literal(&right, 0) => {
            return left;
        }
        _ => {}
    }

    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

fn is_int_literal(expr: &PureExpr, value: i64) -> bool {
    matches!(expr, PureExpr::Int(candidate) if *candidate == value)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum KnownValue {
    Bool(bool),
    Int(i64),
}

fn eval_value(expr: &PureExpr) -> Option<KnownValue> {
    match expr {
        PureExpr::Bool(value) => Some(KnownValue::Bool(*value)),
        PureExpr::Int(value) => Some(KnownValue::Int(*value)),
        PureExpr::UnOp(UnOp::Not, inner) => match eval_value(inner)? {
            KnownValue::Bool(value) => Some(KnownValue::Bool(!value)),
            KnownValue::Int(_) => None,
        },
        PureExpr::UnOp(UnOp::Neg, inner) => match eval_value(inner)? {
            KnownValue::Int(value) => value.checked_neg().map(KnownValue::Int),
            KnownValue::Bool(_) => None,
        },
        PureExpr::UnOp(UnOp::BitNot, inner) => match eval_value(inner)? {
            KnownValue::Int(value) => Some(KnownValue::Int(!value)),
            KnownValue::Bool(_) => None,
        },
        PureExpr::BinOp(left, op, right) => eval_binary_value(left, *op, right),
        PureExpr::Ite(cond, then_expr, else_expr) => match eval_value(cond)? {
            KnownValue::Bool(true) => eval_value(then_expr),
            KnownValue::Bool(false) => eval_value(else_expr),
            KnownValue::Int(_) => None,
        },
        PureExpr::Let { var, value, body } => {
            eval_value(&inline_let_binding_for_native_replay(var, value, body)?)
        }
        PureExpr::Old(inner) => eval_value(inner),
        PureExpr::Float(_)
        | PureExpr::Var(_, _)
        | PureExpr::Deref(_)
        | PureExpr::Final(_)
        | PureExpr::View(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. } => None,
    }
}

fn eval_binary_value(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<KnownValue> {
    match op {
        BinOp::Add => eval_int_binop(left, right, i64::checked_add),
        BinOp::Sub => eval_int_binop(left, right, i64::checked_sub),
        BinOp::Mul => eval_int_binop(left, right, i64::checked_mul),
        BinOp::Div => eval_int_binop(left, right, i64::checked_div),
        BinOp::Mod => eval_int_binop(left, right, i64::checked_rem),
        // Truncated machine ops: Rust's `/`/`%` are exactly i64 checked_div/rem
        // (toward-zero, remainder takes the dividend's sign).
        BinOp::DivTrunc => eval_int_binop(left, right, i64::checked_div),
        BinOp::RemTrunc => eval_int_binop(left, right, i64::checked_rem),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let left = eval_value(left)?;
            let right = eval_value(right)?;
            match compare_known_values(left, op, right) {
                TruthValue::True { .. } => Some(KnownValue::Bool(true)),
                TruthValue::False { .. } => Some(KnownValue::Bool(false)),
                TruthValue::Unknown { .. } => None,
            }
        }
        BinOp::And | BinOp::Or | BinOp::Implies => {
            let left = eval_value(left)?;
            let right = eval_value(right)?;
            eval_bool_binop(left, op, right)
        }
        BinOp::Shl => eval_shift_binop(left, right, i64::checked_shl),
        BinOp::Shr => eval_shift_binop(left, right, i64::checked_shr),
        BinOp::BitAnd => eval_int_binop(left, right, |left, right| Some(left & right)),
        BinOp::BitXor => eval_int_binop(left, right, |left, right| Some(left ^ right)),
        BinOp::BitOr => eval_int_binop(left, right, |left, right| Some(left | right)),
    }
}

fn eval_int_binop(
    left: &PureExpr,
    right: &PureExpr,
    op: fn(i64, i64) -> Option<i64>,
) -> Option<KnownValue> {
    match (eval_value(left)?, eval_value(right)?) {
        (KnownValue::Int(left), KnownValue::Int(right)) => op(left, right).map(KnownValue::Int),
        _ => None,
    }
}

fn eval_shift_binop(
    left: &PureExpr,
    right: &PureExpr,
    op: fn(i64, u32) -> Option<i64>,
) -> Option<KnownValue> {
    match (eval_value(left)?, eval_value(right)?) {
        (KnownValue::Int(left), KnownValue::Int(right)) => {
            op(left, checked_shift_amount(right)?).map(KnownValue::Int)
        }
        _ => None,
    }
}

fn eval_bool_binop(left: KnownValue, op: BinOp, right: KnownValue) -> Option<KnownValue> {
    let (KnownValue::Bool(left), KnownValue::Bool(right)) = (left, right) else {
        return None;
    };
    let value = match op {
        BinOp::And => left && right,
        BinOp::Or => left || right,
        BinOp::Implies => !left || right,
        _ => return None,
    };
    Some(KnownValue::Bool(value))
}

fn compare_known_values(left: KnownValue, op: BinOp, right: KnownValue) -> TruthValue {
    compare_known_values_with_int_rule(left, op, right, "int-constant-comparison")
}

fn compare_known_values_with_int_rule(
    left: KnownValue,
    op: BinOp,
    right: KnownValue,
    int_rule: &'static str,
) -> TruthValue {
    match (left, right) {
        (KnownValue::Bool(left), KnownValue::Bool(right)) => match op {
            BinOp::Eq => TruthValue::from_bool(left == right, "bool-eq"),
            BinOp::Ne => TruthValue::from_bool(left != right, "bool-ne"),
            _ => TruthValue::unknown("non-equality comparison over boolean constants"),
        },
        (KnownValue::Int(left), KnownValue::Int(right)) => {
            let value = match op {
                BinOp::Eq => left == right,
                BinOp::Ne => left != right,
                BinOp::Lt => left < right,
                BinOp::Le => left <= right,
                BinOp::Gt => left > right,
                BinOp::Ge => left >= right,
                _ => unreachable!("comparison operators handled by caller"),
            };
            TruthValue::from_bool(value, int_rule)
        }
        _ => TruthValue::unknown("comparison mixes incompatible constant sorts"),
    }
}

#[cfg(test)]
mod guarded_ite_comparison_tests {
    use super::*;
    use crate::formula::FloatBits;

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Int))
    }

    fn bool_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Bool))
    }

    fn bin(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
    }

    fn not(expr: PureExpr) -> PureExpr {
        PureExpr::UnOp(UnOp::Not, Arc::new(expr))
    }

    fn ite(cond: PureExpr, then_expr: PureExpr, else_expr: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr))
    }

    fn verified(predicate: &PureExpr) -> bool {
        matches!(
            prove_native_pure_predicate(predicate, NativeClaimFormat::TrustWpPureExprV1, &[],),
            NativePureProofOutcome::Verified(_)
        )
    }

    fn clamp(candidate: PureExpr, lo: PureExpr, hi: PureExpr) -> PureExpr {
        ite(
            bin(candidate.clone(), BinOp::Lt, lo.clone()),
            lo,
            ite(bin(candidate.clone(), BinOp::Gt, hi.clone()), hi, candidate),
        )
    }

    #[test]
    fn proves_total_ite_comparison_only_when_both_arms_hold() {
        let condition = bool_var("condition");
        let true_predicate = bin(
            ite(condition.clone(), PureExpr::Int(1), PureExpr::Int(2)),
            BinOp::Ge,
            PureExpr::Int(1),
        );
        assert!(verified(&true_predicate));

        let false_predicate = bin(
            ite(condition, PureExpr::Int(1), PureExpr::Int(0)),
            BinOp::Ge,
            PureExpr::Int(1),
        );
        assert!(
            !verified(&false_predicate),
            "one false conditional arm must keep the result non-authoritative"
        );

        let right_operand_predicate = bin(
            PureExpr::Int(2),
            BinOp::Le,
            ite(
                bool_var("right_condition"),
                PureExpr::Int(2),
                PureExpr::Int(3),
            ),
        );
        assert!(
            verified(&right_operand_predicate),
            "the symmetric right-operand rewrite must retain both guards"
        );
    }

    #[test]
    fn proves_nested_clamp_bounds_under_the_enclosing_precondition() {
        let candidate = int_var("candidate");
        let lo = int_var("lo");
        let hi = int_var("hi");
        let result = clamp(candidate, lo.clone(), hi.clone());
        let postcondition = bin(
            bin(lo.clone(), BinOp::Le, result.clone()),
            BinOp::And,
            bin(result, BinOp::Le, hi.clone()),
        );
        let predicate = bin(bin(lo, BinOp::Le, hi), BinOp::Implies, postcondition);

        assert!(
            verified(&predicate),
            "the enclosing bound and each dominating branch guard prove the clamp range"
        );
    }

    #[test]
    fn rejects_a_false_strict_clamp_bound() {
        let candidate = int_var("candidate");
        let lo = int_var("lo");
        let hi = int_var("hi");
        let result = clamp(candidate, lo.clone(), hi.clone());
        let predicate = bin(
            bin(lo, BinOp::Le, hi.clone()),
            BinOp::Implies,
            bin(result, BinOp::Lt, hi),
        );

        assert!(
            !verified(&predicate),
            "the upper clamp arm equals `hi`, so a strict upper bound is false"
        );
    }

    #[test]
    fn projects_negated_order_only_for_the_integer_fragment() {
        let x = int_var("x");
        let lo = int_var("lo");
        let integer_predicate = bin(
            not(bin(x.clone(), BinOp::Lt, lo.clone())),
            BinOp::Implies,
            bin(lo, BinOp::Le, x),
        );
        assert!(verified(&integer_predicate));

        let float_x = PureExpr::Var("float_x".to_string(), Some(ExprSort::Float));
        let float_y = PureExpr::Var("float_y".to_string(), Some(ExprSort::Float));
        let float_predicate = bin(
            not(bin(float_x.clone(), BinOp::Lt, float_y.clone())),
            BinOp::Implies,
            bin(float_x, BinOp::Ge, float_y),
        );
        assert!(
            !verified(&float_predicate),
            "ordered-negation projection is intentionally integer-only"
        );
    }

    #[test]
    fn rejects_equality_negation_and_nan_order_projection() {
        let x = int_var("x");
        let y = int_var("y");
        let equality_predicate = bin(
            not(bin(x.clone(), BinOp::Eq, y.clone())),
            BinOp::Implies,
            bin(x, BinOp::Lt, y),
        );
        assert!(
            !verified(&equality_predicate),
            "disequality does not choose either direction of an integer order"
        );

        assert_eq!(negate_ordered_comparison(BinOp::Lt), Some(BinOp::Ge));
        assert_eq!(negate_ordered_comparison(BinOp::Gt), Some(BinOp::Le));
        assert_eq!(negate_ordered_comparison(BinOp::Le), Some(BinOp::Gt));
        assert_eq!(negate_ordered_comparison(BinOp::Ge), Some(BinOp::Lt));
        assert_eq!(negate_ordered_comparison(BinOp::Eq), None);
        assert_eq!(negate_ordered_comparison(BinOp::Ne), None);

        let nan = PureExpr::Float(FloatBits::from_f64(f64::NAN));
        let zero = PureExpr::Float(FloatBits::from_f64(0.0));
        let nan_predicate = bin(
            not(bin(nan.clone(), BinOp::Lt, zero.clone())),
            BinOp::Implies,
            bin(nan, BinOp::Ge, zero),
        );
        assert!(
            !verified(&nan_predicate),
            "the direct replay API must not turn a NaN negated order into its converse"
        );
    }
}

#[cfg(test)]
mod modulo_upper_bound_tests {
    use super::*;

    fn prove(text: &str) -> NativePureProofOutcome {
        let predicate = parse_contract(text).expect("parse contract predicate");
        prove_native_pure_predicate(&predicate, NativeClaimFormat::TrustWpPureExprV1, &[])
    }

    fn is_verified(outcome: &NativePureProofOutcome) -> bool {
        matches!(outcome, NativePureProofOutcome::Verified(_))
    }

    #[test]
    fn does_not_apply_current_bound_inside_compound_old_expression() {
        let outcome = prove("x >= 0 ==> old(x + 1) >= 1");
        assert!(
            !is_verified(&outcome),
            "a current-state bound must not constrain entry-state `old(x)`, got {outcome:?}"
        );
    }

    #[test]
    fn does_not_substitute_current_equality_inside_old_expression() {
        let outcome = prove("(x == 0 && x >= 0) ==> old(x) >= 0");
        assert!(
            !is_verified(&outcome),
            "a current-state equality must not rewrite entry-state `old(x)`, got {outcome:?}"
        );
    }

    #[test]
    fn does_not_beta_reduce_current_let_value_across_old_boundary() {
        let outcome = prove("{ let t = x; old(t) == old(x) }");
        assert!(
            !is_verified(&outcome),
            "a current-state let value must not be moved beneath `old`, got {outcome:?}"
        );
    }

    #[test]
    fn preserves_explicit_old_variable_linear_reasoning() {
        let outcome = prove("old(x) >= 0 ==> old(x) + 1 >= 1");
        assert!(
            is_verified(&outcome),
            "an explicit entry-state bound should still constrain the same `old(x)`, got {outcome:?}"
        );
    }

    // Keystone: `(ring_head + base) % len < len` under `len >= 1`.
    #[test]
    fn proves_row_index_modulo_upper_bound() {
        let outcome = prove("len >= 1 ==> (ring_head + base) % len < len");
        assert!(is_verified(&outcome), "expected Verified, got {outcome:?}");
    }

    // Simplest form: `n % m < m` under `m >= 1`.
    #[test]
    fn proves_simple_modulo_upper_bound() {
        let outcome = prove("m >= 1 ==> n % m < m");
        assert!(is_verified(&outcome), "expected Verified, got {outcome:?}");
    }

    // `<=` form: `n % m <= m - 1` under `m >= 1`.
    #[test]
    fn proves_modulo_upper_bound_le() {
        let outcome = prove("m >= 1 ==> n % m <= m - 1");
        assert!(is_verified(&outcome), "expected Verified, got {outcome:?}");
    }

    // Soundness guard: without a positive-divisor assumption the upper bound
    // must NOT be claimed, so this stays non-Verified.
    #[test]
    fn does_not_prove_modulo_upper_bound_without_positive_divisor() {
        let outcome = prove("n % m < m");
        assert!(
            !is_verified(&outcome),
            "must not prove a modulo bound without a positive divisor, got {outcome:?}"
        );
    }

    // Soundness guard: a genuinely false modulo bound must not be proved.
    // `n % m < m - 1` is false e.g. for n=1, m=2 (1 % 2 = 1, not < 1).
    #[test]
    fn does_not_prove_false_modulo_strict_upper_bound() {
        let outcome = prove("m >= 1 ==> n % m < m - 1");
        assert!(
            !is_verified(&outcome),
            "must not prove a false modulo bound, got {outcome:?}"
        );
    }

    // Soundness guard: equality against the divisor is false in general.
    #[test]
    fn does_not_prove_modulo_equals_divisor() {
        let outcome = prove("m >= 1 ==> n % m == m");
        assert!(
            !is_verified(&outcome),
            "must not prove `n % m == m`, got {outcome:?}"
        );
    }

    // Soundness guard: the native constant evaluator uses TRUNCATED remainder
    // (`-1 % 5 == -1`), so `n % m >= 0` must NOT be proved for a symbolic
    // dividend even under `m >= 1` — proving it would contradict the prover's
    // own ground evaluation. The non-negativity rule in `lower_bound_int_expr`
    // is therefore deliberately gated on a non-negative dividend.
    #[test]
    fn does_not_prove_modulo_nonneg_for_symbolic_dividend() {
        let outcome = prove("m >= 1 ==> n % m >= 0");
        assert!(
            !is_verified(&outcome),
            "must not prove n % m >= 0 for symbolic n (truncated rem can be negative), got {outcome:?}"
        );
    }
}

#[cfg(test)]
mod truncated_bound_tests {
    use super::*;

    fn v(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn bin(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
    }
    fn verified(pred: &PureExpr) -> bool {
        matches!(
            prove_native_pure_predicate(pred, NativeClaimFormat::TrustWpPureExprV1, &[]),
            NativePureProofOutcome::Verified(_)
        )
    }

    // Keystone for the truncated remainder: exercises the extended
    // lower_bound_int_difference / upper-bound rules for BinOp::RemTrunc.
    // `len >= 1 ==> (ring_head + base) %trunc len < len`.
    #[test]
    fn native_proves_remtrunc_keystone() {
        let pred = bin(
            bin(v("len"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(
                    bin(v("ring_head"), BinOp::Add, v("base")),
                    BinOp::RemTrunc,
                    v("len"),
                ),
                BinOp::Lt,
                v("len"),
            ),
        );
        assert!(
            verified(&pred),
            "len>=1 ==> (ring_head+base) %trunc len < len"
        );
    }

    // `m >= 1 ==> n %trunc m < m`.
    #[test]
    fn native_proves_remtrunc_simple_upper_bound() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(bin(v("n"), BinOp::RemTrunc, v("m")), BinOp::Lt, v("m")),
        );
        assert!(verified(&pred), "m>=1 ==> n %trunc m < m");
    }

    // SOUNDNESS: the truncated remainder takes the dividend's sign, so for a
    // possibly-negative symbolic dividend `n %trunc m >= 0` must NOT be proved.
    #[test]
    fn native_does_not_prove_remtrunc_nonneg_for_symbolic_dividend() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(v("n"), BinOp::RemTrunc, v("m")),
                BinOp::Ge,
                PureExpr::Int(0),
            ),
        );
        assert!(
            !verified(&pred),
            "must NOT prove n %trunc m >= 0 for possibly-negative symbolic n"
        );
    }

    // With a non-negative dividend (literal 7), `7 %trunc m >= 0` IS provable —
    // exercises the extended lower_bound_int_expr RemTrunc arm (>= 0 for a
    // non-negative dividend and positive divisor). A literal dividend keeps this
    // to a single antecedent the native prover gathers. (The nested-antecedent
    // `n>=0 ==> m>=1 ==> ...` form fails for both Mod and RemTrunc — a pre-
    // existing prover premise-gathering limitation, not a div/mod issue.)
    #[test]
    fn native_proves_remtrunc_nonneg_for_nonnegative_dividend() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(PureExpr::Int(7), BinOp::RemTrunc, v("m")),
                BinOp::Ge,
                PureExpr::Int(0),
            ),
        );
        assert!(verified(&pred), "m>=1 ==> 7 %trunc m >= 0");
    }

    // DivTrunc lower bound: `m >= 1 ==> 7 /trunc m >= 0`.
    #[test]
    fn native_proves_divtrunc_nonneg_for_nonnegative_dividend() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(PureExpr::Int(7), BinOp::DivTrunc, v("m")),
                BinOp::Ge,
                PureExpr::Int(0),
            ),
        );
        assert!(verified(&pred), "m>=1 ==> 7 /trunc m >= 0");
    }
}
