// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{self, Write},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    BundleDigest, BundleObligation, VerifyBundleRequest, PROOF_EVIDENCE_SCHEMA_VERSION,
    PROOF_EVIDENCE_WIRE_PREFIX, TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
    TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION, VERIFY_BUNDLE_API_VERSION,
};

/// Aggregate bundle verification result.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifyBundleResult {
    pub api_version: String,
    pub bundle_id: String,
    pub status: VerifyBundleStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub aggregate_evidence: Option<ProofEvidence>,
    #[serde(default)]
    pub obligation_results: Vec<BundleObligationResult>,
    #[serde(default)]
    pub diagnostics: Vec<BundleDiagnostic>,
}

impl VerifyBundleResult {
    /// Build an aggregate result from per-obligation results.
    #[must_use]
    pub fn from_obligation_results(
        request: VerifyBundleRequest,
        obligation_results: Vec<BundleObligationResult>,
        mut diagnostics: Vec<BundleDiagnostic>,
    ) -> Self {
        diagnostics.extend(request.validation_diagnostics());

        let obligations_by_id: BTreeMap<&str, &BundleObligation> = request
            .obligations
            .iter()
            .map(|obligation| (obligation.id.as_str(), obligation))
            .collect();
        let mut expected: BTreeMap<&str, bool> = request
            .obligations
            .iter()
            .map(|obligation| (obligation.id.as_str(), false))
            .collect();
        let mut seen_results = HashSet::new();

        for result in &obligation_results {
            if !expected.contains_key(result.obligation_id.as_str()) {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation_results",
                    format!(
                        "unexpected result for obligation `{}`",
                        result.obligation_id
                    ),
                ));
            } else if !seen_results.insert(result.obligation_id.as_str()) {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation_results",
                    format!("duplicate result for obligation `{}`", result.obligation_id),
                ));
            } else if let Some(seen) = expected.get_mut(result.obligation_id.as_str()) {
                *seen = true;
            }

            if let BundleObligationStatus::Verified { evidence } = &result.status {
                if !evidence.is_proof_grade() {
                    diagnostics.push(BundleDiagnostic::invalid(
                        "proof_evidence",
                        format!(
                            "verified obligation `{}` is missing proof-grade checked evidence",
                            result.obligation_id
                        ),
                    ));
                }
                if evidence.format == ProofEvidenceFormat::TrustWpNativePureReplayV1 {
                    if let Some(obligation) = obligations_by_id.get(result.obligation_id.as_str()) {
                        if let Err(err) = super::proof::replay_native_pure_evidence(
                            &request, obligation, evidence,
                        ) {
                            diagnostics.push(BundleDiagnostic::invalid(
                                "proof_evidence.replay",
                                format!(
                                    "verified obligation `{}` failed native proof replay: {err}",
                                    result.obligation_id
                                ),
                            ));
                        }
                    }
                }
            }
        }

        for (obligation_id, seen) in expected {
            if !seen {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation_results",
                    format!("missing result for obligation `{obligation_id}`"),
                ));
            }
        }

        let mut status = aggregate_status(&obligation_results, &diagnostics);
        let aggregate_evidence = if matches!(status, VerifyBundleStatus::Verified) {
            let evidence =
                super::proof::aggregate_proof_evidence_for_result(&request, &obligation_results);
            if evidence.as_ref().is_some_and(ProofEvidence::is_proof_grade) {
                evidence
            } else {
                diagnostics.push(BundleDiagnostic::invalid(
                    "aggregate_proof_evidence",
                    "verified bundle is missing proof-grade aggregate evidence",
                ));
                status = aggregate_status(&obligation_results, &diagnostics);
                None
            }
        } else {
            None
        };

        Self {
            api_version: VERIFY_BUNDLE_API_VERSION.to_string(),
            bundle_id: request.bundle_id,
            status,
            aggregate_evidence,
            obligation_results,
            diagnostics,
        }
    }

    pub(super) fn invalid(
        request: VerifyBundleRequest,
        diagnostics: Vec<BundleDiagnostic>,
    ) -> Self {
        Self {
            api_version: VERIFY_BUNDLE_API_VERSION.to_string(),
            bundle_id: request.bundle_id,
            status: VerifyBundleStatus::Invalid,
            aggregate_evidence: None,
            obligation_results: Vec::new(),
            diagnostics,
        }
    }

    /// Returns true only when every obligation and the aggregate bundle result
    /// have proof-grade checked evidence.
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self.status, VerifyBundleStatus::Verified)
            && !self.obligation_results.is_empty()
            && self
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.severity == BundleDiagnosticSeverity::Warning)
            && self
                .aggregate_evidence
                .as_ref()
                .is_some_and(ProofEvidence::is_proof_grade)
            && self.obligation_results.iter().all(|result| {
                result
                    .diagnostics
                    .iter()
                    .all(|diagnostic| diagnostic.severity == BundleDiagnosticSeverity::Warning)
                    && matches!(
                        &result.status,
                        BundleObligationStatus::Verified { evidence }
                            if evidence.is_proof_grade()
                    )
            })
    }

    /// trust-wp-style fail-closed process code.
    ///
    /// `0` means fully verified. Every other status is non-success.
    #[must_use]
    pub fn exit_code(&self) -> i32 {
        match self.status {
            VerifyBundleStatus::Verified => 0,
            VerifyBundleStatus::Failed => 1,
            VerifyBundleStatus::Unknown | VerifyBundleStatus::Unsupported => 2,
            VerifyBundleStatus::Invalid => 3,
        }
    }
}

fn aggregate_status(
    obligation_results: &[BundleObligationResult],
    diagnostics: &[BundleDiagnostic],
) -> VerifyBundleStatus {
    if obligation_results.is_empty()
        || diagnostics.iter().any(BundleDiagnostic::is_invalid)
        || obligation_results
            .iter()
            .flat_map(|result| result.diagnostics.iter())
            .any(BundleDiagnostic::is_invalid)
    {
        return VerifyBundleStatus::Invalid;
    }
    if obligation_results
        .iter()
        .any(|result| matches!(result.status, BundleObligationStatus::Failed { .. }))
    {
        return VerifyBundleStatus::Failed;
    }
    if diagnostics.iter().any(BundleDiagnostic::is_unsupported)
        || obligation_results
            .iter()
            .flat_map(|result| result.diagnostics.iter())
            .any(BundleDiagnostic::is_unsupported)
        || obligation_results
            .iter()
            .any(|result| matches!(result.status, BundleObligationStatus::Unsupported { .. }))
    {
        return VerifyBundleStatus::Unsupported;
    }
    if obligation_results
        .iter()
        .any(|result| matches!(result.status, BundleObligationStatus::Unknown { .. }))
    {
        return VerifyBundleStatus::Unknown;
    }
    if obligation_results
        .iter()
        .all(|result| matches!(result.status, BundleObligationStatus::Verified { .. }))
    {
        return VerifyBundleStatus::Verified;
    }

    VerifyBundleStatus::Invalid
}

/// High-level aggregate status.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerifyBundleStatus {
    Verified,
    Failed,
    Unknown,
    Unsupported,
    Invalid,
}

impl VerifyBundleStatus {
    /// Stable machine-readable status label.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Unknown => "unknown",
            Self::Unsupported => "unsupported",
            Self::Invalid => "invalid",
        }
    }
}

/// Per-obligation verification result.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleObligationResult {
    pub obligation_id: String,
    pub status: BundleObligationStatus,
    #[serde(default)]
    pub diagnostics: Vec<BundleDiagnostic>,
    #[serde(default)]
    pub metadata: BundleResultMetadata,
}

impl BundleObligationResult {
    /// Create a verified result with explicit proof evidence.
    #[must_use]
    pub fn verified(obligation_id: impl Into<String>, evidence: ProofEvidence) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: BundleObligationStatus::Verified { evidence },
            diagnostics: Vec::new(),
            metadata: BundleResultMetadata::default(),
        }
    }

    /// Create a failed result.
    #[must_use]
    pub fn failed(obligation_id: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: BundleObligationStatus::Failed {
                reason: reason.into(),
            },
            diagnostics: Vec::new(),
            metadata: BundleResultMetadata::default(),
        }
    }

    /// Create an inconclusive result.
    #[must_use]
    pub fn unknown(obligation_id: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: BundleObligationStatus::Unknown {
                reason: reason.into(),
            },
            diagnostics: Vec::new(),
            metadata: BundleResultMetadata::default(),
        }
    }

    /// Create an unsupported result.
    #[must_use]
    pub fn unsupported(obligation_id: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: BundleObligationStatus::Unsupported {
                reason: reason.into(),
            },
            diagnostics: Vec::new(),
            metadata: BundleResultMetadata::default(),
        }
    }

    /// Attach machine-readable result metadata.
    #[must_use]
    pub fn with_metadata(mut self, metadata: BundleResultMetadata) -> Self {
        self.metadata = metadata;
        self
    }
}

/// Per-obligation status. Only `Verified` is success.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleObligationStatus {
    Verified { evidence: ProofEvidence },
    Failed { reason: String },
    Unknown { reason: String },
    Unsupported { reason: String },
}

impl BundleObligationStatus {
    /// Stable machine-readable status label.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Verified { .. } => "verified",
            Self::Failed { .. } => "failed",
            Self::Unknown { .. } => "unknown",
            Self::Unsupported { .. } => "unsupported",
        }
    }
}

/// Machine-readable metadata about how one obligation result was produced.
#[non_exhaustive]
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleResultMetadata {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver: Option<BundleSolverMetadata>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub evidence: Option<BundleEvidenceMetadata>,
}

impl BundleResultMetadata {
    /// Create metadata with solver and evidence summaries.
    #[must_use]
    pub fn new(
        solver: Option<BundleSolverMetadata>,
        evidence: Option<BundleEvidenceMetadata>,
    ) -> Self {
        Self { solver, evidence }
    }
}

/// Deterministic native solver/replay metadata.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleSolverMetadata {
    pub engine: String,
    pub checker: String,
    pub claim_format: String,
    pub replay_steps: usize,
    pub assumptions: usize,
    pub assertions: usize,
}

impl BundleSolverMetadata {
    /// Create solver metadata for a replay-backed obligation.
    #[must_use]
    pub fn new(
        engine: impl Into<String>,
        checker: impl Into<String>,
        claim_format: impl Into<String>,
        replay_steps: usize,
        assumptions: usize,
        assertions: usize,
    ) -> Self {
        Self {
            engine: engine.into(),
            checker: checker.into(),
            claim_format: claim_format.into(),
            replay_steps,
            assumptions,
            assertions,
        }
    }
}

/// Stable summary of the attached proof evidence.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleEvidenceMetadata {
    pub format: ProofEvidenceFormat,
    pub strength: ProofStrength,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digest: Option<BundleDigest>,
    pub artifact_count: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub checked_by: Option<String>,
}

impl BundleEvidenceMetadata {
    /// Summarize a proof-evidence envelope without reparsing strings.
    #[must_use]
    pub fn from_evidence(evidence: &ProofEvidence) -> Self {
        Self {
            format: evidence.format.clone(),
            strength: evidence.strength,
            digest: evidence.digest.clone(),
            artifact_count: evidence.artifacts.len(),
            checked_by: evidence.checked_by.clone(),
        }
    }
}

/// Proof evidence required before an obligation can be marked verified.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofEvidence {
    pub schema_version: String,
    pub producer: String,
    pub format: ProofEvidenceFormat,
    pub strength: ProofStrength,
    #[serde(default)]
    pub digest: Option<BundleDigest>,
    #[serde(default)]
    pub artifacts: Vec<EvidenceArtifact>,
    #[serde(default)]
    pub checked_by: Option<String>,
}

/// Stable proof-evidence wire parsing failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofEvidenceWireError {
    pub code: String,
    pub message: String,
}

impl ProofEvidenceWireError {
    fn new(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ProofEvidenceWireError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code, self.message)
    }
}

impl std::error::Error for ProofEvidenceWireError {}

impl ProofEvidence {
    /// Construct checked proof evidence.
    #[must_use]
    pub fn checked(
        producer: impl Into<String>,
        format: ProofEvidenceFormat,
        checked_by: impl Into<String>,
    ) -> Self {
        Self {
            schema_version: PROOF_EVIDENCE_SCHEMA_VERSION.to_string(),
            producer: producer.into(),
            format,
            strength: ProofStrength::Sound,
            digest: None,
            artifacts: Vec::new(),
            checked_by: Some(checked_by.into()),
        }
    }

    /// Set the claimed proof strength.
    #[must_use]
    pub fn with_strength(mut self, strength: ProofStrength) -> Self {
        self.strength = strength;
        self
    }

    /// Attach a digest to the proof artifact.
    #[must_use]
    pub fn with_digest(mut self, digest: BundleDigest) -> Self {
        self.digest = Some(digest);
        self
    }

    /// Attach one hash-addressed evidence artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: EvidenceArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }

    /// Returns true when an external checker is recorded.
    #[must_use]
    pub fn is_checked(&self) -> bool {
        self.checked_by
            .as_ref()
            .is_some_and(|checker| !checker.trim().is_empty())
    }

    /// Returns true when the evidence is proof-grade and replay/check backed.
    #[must_use]
    pub fn is_proof_grade(&self) -> bool {
        self.schema_version == PROOF_EVIDENCE_SCHEMA_VERSION
            && self.is_checked()
            && self.strength.is_proof_grade()
            && self
                .digest
                .as_ref()
                .is_some_and(BundleDigest::is_hash_addressed)
            && self.has_release_grade_artifacts()
    }

    fn has_release_grade_artifacts(&self) -> bool {
        if self.artifacts.is_empty() {
            return false;
        }

        let mut seen = HashSet::new();
        self.artifacts
            .iter()
            .all(|artifact| artifact.has_stable_identity() && seen.insert(artifact.id.as_str()))
    }

    /// Serialize this evidence envelope in a deterministic single-record wire
    /// format suitable for golden tests, replay comparison, and release
    /// artifacts.
    #[must_use]
    pub fn to_stable_wire(&self) -> String {
        let mut wire = String::new();
        let _ = writeln!(wire, "{PROOF_EVIDENCE_WIRE_PREFIX}");
        write_hex_field(&mut wire, "schema_version", &self.schema_version);
        write_hex_field(&mut wire, "producer", &self.producer);
        let _ = writeln!(wire, "format={}", self.format.as_str());
        let _ = writeln!(wire, "strength={}", self.strength.as_str());
        write_optional_digest_field(&mut wire, "digest", self.digest.as_ref());
        write_optional_hex_field(&mut wire, "checked_by", self.checked_by.as_deref());
        let _ = writeln!(wire, "artifacts={}", self.artifacts.len());
        for (index, artifact) in self.artifacts.iter().enumerate() {
            artifact.write_stable_wire(&mut wire, index);
        }
        wire
    }

    /// Parse canonical stable proof evidence wire emitted by
    /// [`Self::to_stable_wire`].
    ///
    /// The parser is intentionally strict for admission use: missing fields,
    /// duplicate fields, malformed hex, unknown labels, unknown extra fields,
    /// and non-canonical reserialization all fail closed.
    pub fn from_stable_wire(wire: &str) -> Result<Self, ProofEvidenceWireError> {
        let mut fields = StableWireFields::parse(wire)?;

        let schema_version = fields.take_hex("schema_version")?;
        let producer = fields.take_hex("producer")?;
        let format = ProofEvidenceFormat::from_wire_label(&fields.take_raw("format")?);
        let strength = ProofStrength::from_wire_label(&fields.take_raw("strength")?)?;
        let digest = fields.take_optional_digest("digest")?;
        let checked_by = fields.take_optional_hex("checked_by")?;
        let artifact_count = fields.take_usize("artifacts")?;

        let mut artifacts = Vec::with_capacity(artifact_count);
        for index in 0..artifact_count {
            let prefix = format!("artifact.{index}");
            artifacts.push(EvidenceArtifact {
                schema_version: fields.take_hex(&format!("{prefix}.schema_version"))?,
                id: fields.take_hex(&format!("{prefix}.id"))?,
                kind: EvidenceArtifactKind::from_wire_label(
                    &fields.take_raw(&format!("{prefix}.kind"))?,
                )?,
                digest: fields.take_digest(&format!("{prefix}.digest"))?,
                description: fields.take_hex(&format!("{prefix}.description"))?,
                uri: None,
                inline_bytes: None,
            });
        }
        fields.finish()?;

        let evidence = Self {
            schema_version,
            producer,
            format,
            strength,
            digest,
            artifacts,
            checked_by,
        };
        if evidence.to_stable_wire() != wire {
            return Err(ProofEvidenceWireError::new(
                "proof_evidence_wire.noncanonical",
                "proof evidence wire is parseable but not canonical",
            ));
        }
        Ok(evidence)
    }
}

/// Proof artifact/checking format.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofEvidenceFormat {
    TrustWpNativePureReplayV1,
    TrustWpVerifyBundleAggregateV1,
    AYProofCertificate,
    Lean5Term,
    ExternalCertificate(String),
}

impl ProofEvidenceFormat {
    /// Stable machine-readable evidence format label.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::TrustWpNativePureReplayV1 => TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
            Self::TrustWpVerifyBundleAggregateV1 => TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
            Self::AYProofCertificate => "ay-proof-certificate",
            Self::Lean5Term => "lean5-term",
            Self::ExternalCertificate(format) => format.as_str(),
        }
    }

    fn from_wire_label(label: &str) -> Self {
        match label {
            label if label == TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION => {
                Self::TrustWpNativePureReplayV1
            }
            label if label == TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION => {
                Self::TrustWpVerifyBundleAggregateV1
            }
            "ay-proof-certificate" => Self::AYProofCertificate,
            "lean5-term" => Self::Lean5Term,
            other => Self::ExternalCertificate(other.to_string()),
        }
    }
}

/// Proof-strength taxonomy used by fail-closed full-verification policy.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofStrength {
    Certified,
    Sound,
    SmtBacked,
    Bounded,
    Heuristic,
    Unchecked,
}

impl ProofStrength {
    /// Stable machine-readable strength label.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Certified => "certified",
            Self::Sound => "sound",
            Self::SmtBacked => "smt-backed",
            Self::Bounded => "bounded",
            Self::Heuristic => "heuristic",
            Self::Unchecked => "unchecked",
        }
    }

    /// Returns true only for strengths acceptable as full proof evidence.
    #[must_use]
    pub fn is_proof_grade(self) -> bool {
        matches!(self, Self::Certified | Self::Sound | Self::SmtBacked)
    }

    fn from_wire_label(label: &str) -> Result<Self, ProofEvidenceWireError> {
        match label {
            "certified" => Ok(Self::Certified),
            "sound" => Ok(Self::Sound),
            "smt-backed" => Ok(Self::SmtBacked),
            "bounded" => Ok(Self::Bounded),
            "heuristic" => Ok(Self::Heuristic),
            "unchecked" => Ok(Self::Unchecked),
            _ => Err(ProofEvidenceWireError::new(
                "proof_evidence_wire.strength",
                format!("unknown proof strength `{label}`"),
            )),
        }
    }
}

/// One hash-addressed evidence artifact.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceArtifact {
    pub schema_version: String,
    pub id: String,
    pub kind: EvidenceArtifactKind,
    pub digest: BundleDigest,
    pub description: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub uri: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub inline_bytes: Option<EvidenceArtifactBytes>,
}

impl EvidenceArtifact {
    /// Create evidence artifact metadata.
    #[must_use]
    pub fn new(
        kind: EvidenceArtifactKind,
        digest: BundleDigest,
        description: impl Into<String>,
    ) -> Self {
        let id = Self::stable_id(&kind, &digest);
        Self {
            schema_version: PROOF_EVIDENCE_SCHEMA_VERSION.to_string(),
            id,
            kind,
            digest,
            description: description.into(),
            uri: None,
            inline_bytes: None,
        }
    }

    /// Attach a stable URI where the concrete artifact bytes can be fetched.
    #[must_use]
    pub fn with_uri(mut self, uri: impl Into<String>) -> Self {
        self.uri = Some(uri.into());
        self
    }

    /// Attach UTF-8 artifact bytes inline.
    ///
    /// The artifact digest is still authoritative; proof-grade evidence checks
    /// that these bytes hash to the artifact digest.
    #[must_use]
    pub fn with_utf8_bytes(mut self, bytes: impl Into<String>) -> Self {
        self.inline_bytes = Some(EvidenceArtifactBytes::utf8(bytes));
        self
    }

    /// Attach arbitrary artifact bytes as lowercase hex.
    ///
    /// The artifact digest is still authoritative; proof-grade evidence checks
    /// that these bytes hash to the artifact digest.
    #[must_use]
    pub fn with_hex_bytes(mut self, bytes_hex: impl Into<String>) -> Self {
        self.inline_bytes = Some(EvidenceArtifactBytes::hex(bytes_hex));
        self
    }

    /// Return the deterministic artifact identity for a kind/digest pair.
    #[must_use]
    pub fn stable_id(kind: &EvidenceArtifactKind, digest: &BundleDigest) -> String {
        format!(
            "{PROOF_EVIDENCE_SCHEMA_VERSION}/artifact/{}/{}/{}",
            kind.as_str(),
            digest.algorithm,
            digest.value
        )
    }

    /// Returns true when the artifact carries the stable v1 schema marker,
    /// deterministic id, and non-empty hash metadata.
    #[must_use]
    pub fn has_stable_identity(&self) -> bool {
        self.schema_version == PROOF_EVIDENCE_SCHEMA_VERSION
            && self.id == Self::stable_id(&self.kind, &self.digest)
            && self.digest.is_hash_addressed()
            && self.has_valid_transport()
    }

    /// Returns true when this artifact exposes concrete transport metadata.
    #[must_use]
    pub fn has_transport(&self) -> bool {
        self.uri.as_ref().is_some_and(|uri| !uri.trim().is_empty()) || self.inline_bytes.is_some()
    }

    /// Returns true when inline artifact bytes decode and match the digest.
    #[must_use]
    pub fn inline_bytes_digest_matches(&self) -> bool {
        self.inline_bytes
            .as_ref()
            .is_none_or(|bytes| bytes.digest_matches(&self.digest))
    }

    fn has_valid_transport(&self) -> bool {
        self.uri.as_ref().is_none_or(|uri| !uri.trim().is_empty())
            && self.inline_bytes_digest_matches()
    }

    fn write_stable_wire(&self, wire: &mut String, index: usize) {
        let prefix = format!("artifact.{index}");
        write_hex_field(
            wire,
            &format!("{prefix}.schema_version"),
            &self.schema_version,
        );
        write_hex_field(wire, &format!("{prefix}.id"), &self.id);
        let _ = writeln!(wire, "{prefix}.kind={}", self.kind.as_str());
        write_digest_field(wire, &format!("{prefix}.digest"), &self.digest);
        write_hex_field(wire, &format!("{prefix}.description"), &self.description);
    }
}

/// Inline bytes for a proof transport artifact.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceArtifactBytes {
    pub encoding: EvidenceArtifactBytesEncoding,
    pub data: String,
}

impl EvidenceArtifactBytes {
    /// Store UTF-8 bytes directly.
    #[must_use]
    pub fn utf8(bytes: impl Into<String>) -> Self {
        Self {
            encoding: EvidenceArtifactBytesEncoding::Utf8,
            data: bytes.into(),
        }
    }

    /// Store arbitrary bytes as hex.
    #[must_use]
    pub fn hex(bytes_hex: impl Into<String>) -> Self {
        Self {
            encoding: EvidenceArtifactBytesEncoding::Hex,
            data: bytes_hex.into(),
        }
    }

    /// Decode the inline bytes into their raw transport form.
    pub fn decoded_bytes(&self) -> Result<Vec<u8>, ProofEvidenceWireError> {
        match self.encoding {
            EvidenceArtifactBytesEncoding::Utf8 => Ok(self.data.as_bytes().to_vec()),
            EvidenceArtifactBytesEncoding::Hex => {
                decode_hex_bytes("artifact.inline_bytes.data", self.data.as_str())
            }
        }
    }

    fn digest_matches(&self, expected: &BundleDigest) -> bool {
        if expected.algorithm != "sha256" {
            return false;
        }
        let Ok(bytes) = self.decoded_bytes() else {
            return false;
        };
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        expected.value == hex_bytes(&hasher.finalize())
    }
}

/// Encoding used for inline proof artifact bytes.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvidenceArtifactBytesEncoding {
    Utf8,
    Hex,
}

impl EvidenceArtifactBytesEncoding {
    /// Stable machine-readable encoding label.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Utf8 => "utf8",
            Self::Hex => "hex",
        }
    }
}

/// Evidence artifact kinds aligned with the tRust full-verification manifest.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvidenceArtifactKind {
    RequestDigest,
    AggregateProofManifest,
    NormalizedObligation,
    SummaryEvidence,
    ProofCertificate,
    SolverTranscript,
    ReplayLog,
    Counterexample,
    Model,
    DiagnosticTrace,
}

impl EvidenceArtifactKind {
    /// Stable machine-readable artifact kind label.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::RequestDigest => "request-digest",
            Self::AggregateProofManifest => "aggregate-proof-manifest",
            Self::NormalizedObligation => "normalized-obligation",
            Self::SummaryEvidence => "summary-evidence",
            Self::ProofCertificate => "proof-certificate",
            Self::SolverTranscript => "solver-transcript",
            Self::ReplayLog => "replay-log",
            Self::Counterexample => "counterexample",
            Self::Model => "model",
            Self::DiagnosticTrace => "diagnostic-trace",
        }
    }

    fn from_wire_label(label: &str) -> Result<Self, ProofEvidenceWireError> {
        match label {
            "request-digest" => Ok(Self::RequestDigest),
            "aggregate-proof-manifest" => Ok(Self::AggregateProofManifest),
            "normalized-obligation" => Ok(Self::NormalizedObligation),
            "summary-evidence" => Ok(Self::SummaryEvidence),
            "proof-certificate" => Ok(Self::ProofCertificate),
            "solver-transcript" => Ok(Self::SolverTranscript),
            "replay-log" => Ok(Self::ReplayLog),
            "counterexample" => Ok(Self::Counterexample),
            "model" => Ok(Self::Model),
            "diagnostic-trace" => Ok(Self::DiagnosticTrace),
            _ => Err(ProofEvidenceWireError::new(
                "proof_evidence_wire.artifact_kind",
                format!("unknown evidence artifact kind `{label}`"),
            )),
        }
    }
}

/// Structured diagnostic emitted by bundle validation or engines.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleDiagnostic {
    pub severity: BundleDiagnosticSeverity,
    pub code: String,
    pub message: String,
}

impl BundleDiagnostic {
    /// Create an invalid-input diagnostic.
    #[must_use]
    pub fn invalid(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: BundleDiagnosticSeverity::Invalid,
            code: code.into(),
            message: message.into(),
        }
    }

    /// Create an unsupported-feature diagnostic.
    #[must_use]
    pub fn unsupported(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: BundleDiagnosticSeverity::Unsupported,
            code: code.into(),
            message: message.into(),
        }
    }

    fn is_invalid(&self) -> bool {
        self.severity == BundleDiagnosticSeverity::Invalid
    }

    fn is_unsupported(&self) -> bool {
        self.severity == BundleDiagnosticSeverity::Unsupported
    }
}

/// Diagnostic severity for fail-closed routing.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleDiagnosticSeverity {
    Invalid,
    Unsupported,
    Warning,
}

impl BundleDiagnosticSeverity {
    /// Stable machine-readable severity label.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Invalid => "invalid",
            Self::Unsupported => "unsupported",
            Self::Warning => "warning",
        }
    }
}

impl BundleDigest {
    /// Returns true when this digest can address a concrete artifact.
    #[must_use]
    pub fn is_hash_addressed(&self) -> bool {
        !self.algorithm.trim().is_empty() && !self.value.trim().is_empty()
    }
}

struct StableWireFields {
    fields: HashMap<String, String>,
}

impl StableWireFields {
    fn parse(wire: &str) -> Result<Self, ProofEvidenceWireError> {
        let mut lines = wire.lines();
        match lines.next() {
            Some(prefix) if prefix == PROOF_EVIDENCE_WIRE_PREFIX => {}
            Some(prefix) => {
                return Err(ProofEvidenceWireError::new(
                    "proof_evidence_wire.prefix",
                    format!(
                        "unexpected proof evidence wire prefix `{prefix}`; expected `{PROOF_EVIDENCE_WIRE_PREFIX}`"
                    ),
                ));
            }
            None => {
                return Err(ProofEvidenceWireError::new(
                    "proof_evidence_wire.empty",
                    "proof evidence wire is empty",
                ));
            }
        }

        let mut fields = HashMap::new();
        for (line_index, line) in lines.enumerate() {
            if line.is_empty() {
                return Err(ProofEvidenceWireError::new(
                    "proof_evidence_wire.line",
                    format!("empty proof evidence wire line at index {}", line_index + 2),
                ));
            }
            let Some((key, value)) = line.split_once('=') else {
                return Err(ProofEvidenceWireError::new(
                    "proof_evidence_wire.line",
                    format!(
                        "proof evidence wire line {} does not contain `=`",
                        line_index + 2
                    ),
                ));
            };
            if key.is_empty() {
                return Err(ProofEvidenceWireError::new(
                    "proof_evidence_wire.line",
                    format!(
                        "proof evidence wire line {} has an empty key",
                        line_index + 2
                    ),
                ));
            }
            if fields.insert(key.to_string(), value.to_string()).is_some() {
                return Err(ProofEvidenceWireError::new(
                    "proof_evidence_wire.duplicate",
                    format!("duplicate proof evidence wire field `{key}`"),
                ));
            }
        }

        Ok(Self { fields })
    }

    fn take_raw(&mut self, key: &str) -> Result<String, ProofEvidenceWireError> {
        self.fields.remove(key).ok_or_else(|| {
            ProofEvidenceWireError::new(
                "proof_evidence_wire.missing",
                format!("missing proof evidence wire field `{key}`"),
            )
        })
    }

    fn take_hex(&mut self, key: &str) -> Result<String, ProofEvidenceWireError> {
        let value = self.take_raw(key)?;
        decode_hex_field(key, &value)
    }

    fn take_optional_hex(&mut self, key: &str) -> Result<Option<String>, ProofEvidenceWireError> {
        let value = self.take_raw(key)?;
        if value.is_empty() {
            Ok(None)
        } else {
            decode_hex_field(key, &value).map(Some)
        }
    }

    fn take_usize(&mut self, key: &str) -> Result<usize, ProofEvidenceWireError> {
        let value = self.take_raw(key)?;
        value.parse::<usize>().map_err(|err| {
            ProofEvidenceWireError::new(
                "proof_evidence_wire.integer",
                format!("proof evidence wire field `{key}` is not a valid usize: {err}"),
            )
        })
    }

    fn take_digest(&mut self, prefix: &str) -> Result<BundleDigest, ProofEvidenceWireError> {
        let algorithm = self.take_hex(&format!("{prefix}.algorithm"))?;
        let value = self.take_hex(&format!("{prefix}.value"))?;
        Ok(BundleDigest::new(algorithm, value))
    }

    fn take_optional_digest(
        &mut self,
        prefix: &str,
    ) -> Result<Option<BundleDigest>, ProofEvidenceWireError> {
        let algorithm = self.take_optional_hex(&format!("{prefix}.algorithm"))?;
        let value = self.take_optional_hex(&format!("{prefix}.value"))?;
        match (algorithm, value) {
            (None, None) => Ok(None),
            (Some(algorithm), Some(value)) => Ok(Some(BundleDigest::new(algorithm, value))),
            _ => Err(ProofEvidenceWireError::new(
                "proof_evidence_wire.digest",
                format!("digest `{prefix}` must include both algorithm and value"),
            )),
        }
    }

    fn finish(self) -> Result<(), ProofEvidenceWireError> {
        if let Some(extra) = self.fields.keys().min() {
            return Err(ProofEvidenceWireError::new(
                "proof_evidence_wire.unknown_field",
                format!("unknown proof evidence wire field `{extra}`"),
            ));
        }
        Ok(())
    }
}

fn write_optional_digest_field(wire: &mut String, field: &str, digest: Option<&BundleDigest>) {
    if let Some(digest) = digest {
        write_digest_field(wire, field, digest);
    } else {
        let _ = writeln!(wire, "{field}.algorithm=");
        let _ = writeln!(wire, "{field}.value=");
    }
}

fn write_digest_field(wire: &mut String, field: &str, digest: &BundleDigest) {
    write_hex_field(wire, &format!("{field}.algorithm"), &digest.algorithm);
    write_hex_field(wire, &format!("{field}.value"), &digest.value);
}

fn write_optional_hex_field(wire: &mut String, field: &str, value: Option<&str>) {
    match value {
        Some(value) => write_hex_field(wire, field, value),
        None => {
            let _ = writeln!(wire, "{field}=");
        }
    }
}

fn write_hex_field(wire: &mut String, field: &str, value: &str) {
    let _ = writeln!(wire, "{field}={}", hex_bytes(value.as_bytes()));
}

fn decode_hex_field(field: &str, value: &str) -> Result<String, ProofEvidenceWireError> {
    let bytes = decode_hex_bytes(field, value)?;

    String::from_utf8(bytes).map_err(|err| {
        ProofEvidenceWireError::new(
            "proof_evidence_wire.utf8",
            format!("proof evidence wire field `{field}` is not UTF-8: {err}"),
        )
    })
}

fn decode_hex_bytes(field: &str, value: &str) -> Result<Vec<u8>, ProofEvidenceWireError> {
    if value.len() % 2 != 0 {
        return Err(ProofEvidenceWireError::new(
            "proof_evidence_wire.hex",
            format!("proof evidence wire field `{field}` has odd-length hex"),
        ));
    }

    let mut bytes = Vec::with_capacity(value.len() / 2);
    let raw = value.as_bytes();
    for index in (0..raw.len()).step_by(2) {
        let hi = hex_nibble(raw[index]).ok_or_else(|| {
            ProofEvidenceWireError::new(
                "proof_evidence_wire.hex",
                format!("proof evidence wire field `{field}` contains non-hex data"),
            )
        })?;
        let lo = hex_nibble(raw[index + 1]).ok_or_else(|| {
            ProofEvidenceWireError::new(
                "proof_evidence_wire.hex",
                format!("proof evidence wire field `{field}` contains non-hex data"),
            )
        })?;
        bytes.push((hi << 4) | lo);
    }

    Ok(bytes)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
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
