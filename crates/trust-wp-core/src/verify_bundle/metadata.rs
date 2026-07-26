// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable metadata keys and typed native replay metadata helpers.

use std::collections::HashMap;

use serde::{de::DeserializeOwned, Deserialize, Serialize};

use super::{
    BundleDigest, BundleNativeOrigin, BundleNativeReplayIdentity, BundleNativeToolIdentity,
    BundleObligation, BundleProducer, BundleProofContext, BundleSummaryFact, BundleTarget,
    BundleTmirObligationSource, BundleTmirSourceSpan, VerifyBundleRequest,
};

/// Optional JSON metadata key carrying typed native trust-wp origin information.
pub const TRUST_WP_NATIVE_ORIGIN_METADATA_KEY: &str = "trust.trust-wp.native-origin.v1";

/// Optional JSON metadata key carrying a trust-wp [`super::BundleClaim`] digest.
pub const TRUST_WP_CLAIM_DIGEST_METADATA_KEY: &str = "trust.trust-wp.claim-digest.v1";

/// JSON metadata key carrying a typed trust-wp tMIR source span.
pub const TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY: &str = "trust.trust-wp.tmir-source-span.v1";

/// JSON metadata key carrying a typed trust-wp native verifier identity.
pub const TRUST_WP_NATIVE_VERIFIER_METADATA_KEY: &str = "trust.trust-wp.native-verifier.v1";

/// JSON metadata key carrying a typed trust-wp native replay identity.
pub const TRUST_WP_NATIVE_REPLAY_METADATA_KEY: &str = "trust.trust-wp.native-replay.v1";

/// JSON metadata key carrying one typed native solver/prover identity.
pub const TRUST_WP_NATIVE_SOLVER_METADATA_KEY: &str = "trust.trust-wp.native-solver.v1";

/// JSON metadata key carrying a typed trust-wp tMIR obligation source.
pub const TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY: &str =
    "trust.trust-wp.tmir-obligation-source.v1";

/// JSON metadata key carrying typed assumption/assertion proof context.
pub const TRUST_WP_PROOF_CONTEXT_METADATA_KEY: &str = "trust.trust-wp.proof-context.v1";

/// JSON metadata key carrying one trust-wp-native abstract-interpretation summary fact.
pub const TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY: &str = "trust.trust-wp.summary-fact.v1";

/// One stable JSON metadata entry for compiler/router integration.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustWpMetadataEntry {
    pub key: String,
    pub value: String,
}

impl TrustWpMetadataEntry {
    /// Create a metadata entry from already serialized JSON.
    #[must_use]
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    fn typed<T: Serialize>(
        key: &'static str,
        value: &T,
    ) -> Result<Self, TrustWpNativeReplayMetadataError> {
        serde_json::to_string(value)
            .map(|json| Self::new(key, json))
            .map_err(|err| TrustWpNativeReplayMetadataError::Serialize {
                key,
                message: err.to_string(),
            })
    }
}

/// Complete typed metadata needed before trust-wp native replay evidence can be
/// created for a MIR/tMIR-originated obligation.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustWpNativeReplayEvidenceInput {
    pub native_origin: BundleNativeOrigin,
    pub tmir_source_span: BundleTmirSourceSpan,
    pub native_verifier: BundleNativeToolIdentity,
    pub native_replay: BundleNativeReplayIdentity,
    #[serde(default)]
    pub native_solvers: Vec<BundleNativeToolIdentity>,
    pub tmir_obligation_source: BundleTmirObligationSource,
    #[serde(default)]
    pub proof_context: BundleProofContext,
    #[serde(default)]
    pub summary_facts: Vec<BundleSummaryFact>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub claim_digest: Option<BundleDigest>,
}

impl TrustWpNativeReplayEvidenceInput {
    /// Create native replay metadata from the required typed identities.
    #[must_use]
    pub fn new(
        native_origin: BundleNativeOrigin,
        tmir_source_span: BundleTmirSourceSpan,
        native_verifier: BundleNativeToolIdentity,
        native_replay: BundleNativeReplayIdentity,
        native_solvers: Vec<BundleNativeToolIdentity>,
        tmir_obligation_source: BundleTmirObligationSource,
    ) -> Self {
        Self {
            native_origin,
            tmir_source_span,
            native_verifier,
            native_replay,
            native_solvers,
            tmir_obligation_source,
            proof_context: BundleProofContext::default(),
            summary_facts: Vec::new(),
            claim_digest: None,
        }
    }

    /// Attach a producer-supplied digest for the obligation claim payload.
    #[must_use]
    pub fn with_claim_digest(mut self, digest: BundleDigest) -> Self {
        self.claim_digest = Some(digest);
        self
    }

    /// Attach typed proof-context atoms.
    #[must_use]
    pub fn with_proof_context(mut self, context: BundleProofContext) -> Self {
        self.proof_context = context;
        self
    }

    /// Attach one producer-supplied summary fact.
    #[must_use]
    pub fn with_summary_fact(mut self, fact: BundleSummaryFact) -> Self {
        self.summary_facts.push(fact);
        self
    }

    /// Attach producer-supplied summary facts.
    #[must_use]
    pub fn with_summary_facts(
        mut self,
        facts: impl IntoIterator<Item = BundleSummaryFact>,
    ) -> Self {
        self.summary_facts.extend(facts);
        self
    }

    /// Apply this metadata to a trust-wp obligation before native replay.
    #[must_use]
    pub fn apply_to_obligation(&self, mut obligation: BundleObligation) -> BundleObligation {
        if let Some(digest) = &self.claim_digest {
            obligation.claim = obligation.claim.with_digest(digest.clone());
        }
        obligation = obligation
            .with_native_origin(self.native_origin.clone())
            .with_tmir_source_span(self.tmir_source_span)
            .with_native_verifier(self.native_verifier.clone())
            .with_native_replay(self.native_replay.clone())
            .with_native_solvers(self.native_solvers.iter().cloned())
            .with_tmir_obligation_source(self.tmir_obligation_source.clone());
        if !self.proof_context.is_empty() {
            obligation = obligation.with_proof_context(self.proof_context.clone());
        }
        for fact in &self.summary_facts {
            obligation = obligation.with_summary_fact(fact.clone());
        }
        obligation
    }

    /// Return fail-closed diagnostics for this metadata applied to an
    /// obligation shape.
    #[must_use]
    pub fn validation_diagnostics_for_obligation(
        &self,
        obligation: &BundleObligation,
    ) -> Vec<super::BundleDiagnostic> {
        VerifyBundleRequest::new(
            "trust-wp-native-replay-metadata-validation",
            BundleProducer::new("trust-wp-core"),
            BundleTarget::new("metadata-validation"),
        )
        .with_obligation(self.apply_to_obligation(obligation.clone()))
        .validation_diagnostics()
    }

    /// Serialize typed metadata into stable key/value entries for compiler
    /// metadata channels that cannot carry trust-wp structs directly.
    pub fn to_metadata_entries(
        &self,
    ) -> Result<Vec<TrustWpMetadataEntry>, TrustWpNativeReplayMetadataError> {
        let mut entries = Vec::new();
        if let Some(digest) = &self.claim_digest {
            entries.push(TrustWpMetadataEntry::typed(
                TRUST_WP_CLAIM_DIGEST_METADATA_KEY,
                digest,
            )?);
        }
        entries.push(TrustWpMetadataEntry::typed(
            TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
            &self.native_origin,
        )?);
        entries.push(TrustWpMetadataEntry::typed(
            TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
            &self.tmir_source_span,
        )?);
        entries.push(TrustWpMetadataEntry::typed(
            TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
            &self.native_verifier,
        )?);
        entries.push(TrustWpMetadataEntry::typed(
            TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
            &self.native_replay,
        )?);
        for solver in &self.native_solvers {
            entries.push(TrustWpMetadataEntry::typed(
                TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
                solver,
            )?);
        }
        entries.push(TrustWpMetadataEntry::typed(
            TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
            &self.tmir_obligation_source,
        )?);
        if !self.proof_context.is_empty() {
            entries.push(TrustWpMetadataEntry::typed(
                TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
                &self.proof_context,
            )?);
        }
        for fact in &self.summary_facts {
            entries.push(TrustWpMetadataEntry::typed(
                TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
                fact,
            )?);
        }
        Ok(entries)
    }

    /// Parse typed native replay metadata from stable key/value pairs.
    ///
    /// Unknown keys are ignored so callers may pass a whole compiler metadata
    /// stream. Required trust-wp keys and duplicate singleton keys fail closed.
    pub fn from_metadata_pairs<'a>(
        entries: impl IntoIterator<Item = (&'a str, &'a str)>,
    ) -> Result<Self, TrustWpNativeReplayMetadataError> {
        let mut singleton_entries: HashMap<&'static str, &str> = HashMap::new();
        let mut solver_values = Vec::new();
        let mut summary_fact_values = Vec::new();

        for (key, value) in entries {
            match key {
                TRUST_WP_NATIVE_SOLVER_METADATA_KEY => solver_values.push(value),
                TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY => summary_fact_values.push(value),
                key => insert_singleton_metadata(&mut singleton_entries, key, value)?,
            }
        }

        let native_solvers =
            parse_repeated_metadata(TRUST_WP_NATIVE_SOLVER_METADATA_KEY, solver_values, true)?;
        let summary_facts = parse_repeated_metadata(
            TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
            summary_fact_values,
            false,
        )?;

        Ok(Self {
            native_origin: required_metadata_json(
                &mut singleton_entries,
                TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
            )?,
            tmir_source_span: required_metadata_json(
                &mut singleton_entries,
                TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
            )?,
            native_verifier: required_metadata_json(
                &mut singleton_entries,
                TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
            )?,
            native_replay: required_metadata_json(
                &mut singleton_entries,
                TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
            )?,
            native_solvers,
            tmir_obligation_source: required_metadata_json(
                &mut singleton_entries,
                TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
            )?,
            proof_context: optional_metadata_json(
                &mut singleton_entries,
                TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
            )?
            .unwrap_or_default(),
            summary_facts,
            claim_digest: optional_metadata_json(
                &mut singleton_entries,
                TRUST_WP_CLAIM_DIGEST_METADATA_KEY,
            )?,
        })
    }

    /// Extract typed native replay metadata from an already built obligation.
    pub fn from_obligation(
        obligation: &BundleObligation,
    ) -> Result<Self, TrustWpNativeReplayMetadataError> {
        let metadata = &obligation.metadata;
        let native_solvers = metadata.native_solvers.clone();
        if native_solvers.is_empty() {
            return Err(TrustWpNativeReplayMetadataError::Missing {
                key: TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
            });
        }

        Ok(Self {
            native_origin: metadata.native_origin.clone().ok_or(
                TrustWpNativeReplayMetadataError::Missing {
                    key: TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
                },
            )?,
            tmir_source_span: metadata.tmir_source_span.ok_or(
                TrustWpNativeReplayMetadataError::Missing {
                    key: TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
                },
            )?,
            native_verifier: metadata.native_verifier.clone().ok_or(
                TrustWpNativeReplayMetadataError::Missing {
                    key: TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
                },
            )?,
            native_replay: metadata.native_replay.clone().ok_or(
                TrustWpNativeReplayMetadataError::Missing {
                    key: TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
                },
            )?,
            native_solvers,
            tmir_obligation_source: metadata.tmir_obligation_source.clone().ok_or(
                TrustWpNativeReplayMetadataError::Missing {
                    key: TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
                },
            )?,
            proof_context: metadata.proof_context.clone(),
            summary_facts: obligation.summary_facts.clone(),
            claim_digest: obligation.claim.digest.clone(),
        })
    }
}

fn insert_singleton_metadata<'a>(
    entries: &mut HashMap<&'static str, &'a str>,
    key: &str,
    value: &'a str,
) -> Result<(), TrustWpNativeReplayMetadataError> {
    let Some(key) = singleton_metadata_key(key) else {
        return Ok(());
    };

    // Tolerate an IDENTICAL duplicate singleton-metadata entry (a benign
    // double-attach — e.g. the `?` desugar surfaces the native-origin key on the
    // precondition obligation via two paths); reject only a CONFLICTING value,
    // where the origin is genuinely ambiguous. Sound either way: identical entries
    // carry one unambiguous fact; conflicting ones still fail closed.
    if let Some(previous) = entries.insert(key, value) {
        if previous != value {
            return Err(TrustWpNativeReplayMetadataError::Duplicate { key });
        }
    }
    Ok(())
}

fn singleton_metadata_key(key: &str) -> Option<&'static str> {
    match key {
        TRUST_WP_CLAIM_DIGEST_METADATA_KEY => Some(TRUST_WP_CLAIM_DIGEST_METADATA_KEY),
        TRUST_WP_NATIVE_ORIGIN_METADATA_KEY => Some(TRUST_WP_NATIVE_ORIGIN_METADATA_KEY),
        TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY => Some(TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY),
        TRUST_WP_NATIVE_VERIFIER_METADATA_KEY => Some(TRUST_WP_NATIVE_VERIFIER_METADATA_KEY),
        TRUST_WP_NATIVE_REPLAY_METADATA_KEY => Some(TRUST_WP_NATIVE_REPLAY_METADATA_KEY),
        TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY => {
            Some(TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY)
        }
        TRUST_WP_PROOF_CONTEXT_METADATA_KEY => Some(TRUST_WP_PROOF_CONTEXT_METADATA_KEY),
        _ => None,
    }
}

fn parse_repeated_metadata<T: DeserializeOwned>(
    key: &'static str,
    values: Vec<&str>,
    required: bool,
) -> Result<Vec<T>, TrustWpNativeReplayMetadataError> {
    if required && values.is_empty() {
        return Err(TrustWpNativeReplayMetadataError::Missing { key });
    }

    values
        .into_iter()
        .map(|value| parse_metadata_json(key, value))
        .collect()
}

fn required_metadata_json<T: DeserializeOwned>(
    entries: &mut HashMap<&'static str, &str>,
    key: &'static str,
) -> Result<T, TrustWpNativeReplayMetadataError> {
    let value = entries
        .remove(key)
        .ok_or(TrustWpNativeReplayMetadataError::Missing { key })?;
    parse_metadata_json(key, value)
}

fn optional_metadata_json<T: DeserializeOwned>(
    entries: &mut HashMap<&'static str, &str>,
    key: &'static str,
) -> Result<Option<T>, TrustWpNativeReplayMetadataError> {
    entries
        .remove(key)
        .map(|value| parse_metadata_json(key, value))
        .transpose()
}

fn parse_metadata_json<T: DeserializeOwned>(
    key: &'static str,
    value: &str,
) -> Result<T, TrustWpNativeReplayMetadataError> {
    serde_json::from_str(value).map_err(|err| TrustWpNativeReplayMetadataError::Deserialize {
        key,
        message: err.to_string(),
    })
}

/// Error returned while converting stable metadata entries to typed trust-wp
/// native replay metadata.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TrustWpNativeReplayMetadataError {
    #[error("failed to serialize trust-wp metadata key `{key}`: {message}")]
    Serialize { key: &'static str, message: String },
    #[error("missing required trust-wp metadata key `{key}`")]
    Missing { key: &'static str },
    #[error("trust-wp singleton metadata key `{key}` appeared more than once")]
    Duplicate { key: &'static str },
    #[error("invalid trust-wp typed metadata `{key}`: {message}")]
    Deserialize { key: &'static str, message: String },
}
