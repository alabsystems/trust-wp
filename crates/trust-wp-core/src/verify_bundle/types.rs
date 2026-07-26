// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::HashSet,
    fmt::{self, Write},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    native_predicate_for_obligation, BundleDiagnostic, PROOF_EVIDENCE_SCHEMA_VERSION,
    TMIR_NATIVE_ORIGIN_SCHEMA_PREFIX, VERIFY_BUNDLE_API_VERSION,
};
use crate::contract_parser::parse_contract;

const TRUST_WP_NATIVE_VERIFIER_NAME: &str = "trust-wp";
const EMPTY_NATIVE_TOOL_PLACEHOLDER_NAME: &str = "unknown";

/// Complete request for verifying a tRust-style bundle.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifyBundleRequest {
    /// API/schema version expected by this module.
    pub api_version: String,
    /// Stable bundle identity supplied by the producer.
    pub bundle_id: String,
    /// Producer metadata.
    pub producer: BundleProducer,
    /// Compilation target metadata.
    pub target: BundleTarget,
    /// Proof obligations to verify.
    #[serde(default)]
    pub obligations: Vec<BundleObligation>,
    /// tMIR Function bodies for inlining.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub functions: Option<Vec<serde_json::Value>>,
    /// Engine options.
    #[serde(default)]
    pub options: VerifyBundleOptions,
}

impl VerifyBundleRequest {
    /// Create a request for the current API version.
    #[must_use]
    pub fn new(
        bundle_id: impl Into<String>,
        producer: BundleProducer,
        target: BundleTarget,
    ) -> Self {
        Self {
            api_version: VERIFY_BUNDLE_API_VERSION.to_string(),
            bundle_id: bundle_id.into(),
            producer,
            target,
            obligations: Vec::new(),
            functions: None,
            options: VerifyBundleOptions::default(),
        }
    }

    /// Add one proof obligation.
    #[must_use]
    pub fn with_obligation(mut self, obligation: BundleObligation) -> Self {
        self.obligations.push(obligation);
        self
    }

    /// Replace verification options.
    #[must_use]
    pub fn with_options(mut self, options: VerifyBundleOptions) -> Self {
        self.options = options;
        self
    }

    /// Return structured request validation diagnostics.
    #[must_use]
    pub fn validation_diagnostics(&self) -> Vec<BundleDiagnostic> {
        let mut diagnostics = Vec::new();

        if self.api_version != VERIFY_BUNDLE_API_VERSION {
            diagnostics.push(BundleDiagnostic::invalid(
                "api_version",
                format!(
                    "unsupported verify-bundle API version `{}`; expected `{VERIFY_BUNDLE_API_VERSION}`",
                    self.api_version
                ),
            ));
        }
        if self.bundle_id.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid("bundle_id", "bundle id is empty"));
        }
        if self.producer.name.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "producer.name",
                "producer name is empty",
            ));
        }
        if self.target.crate_name.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "target.crate_name",
                "crate name is empty",
            ));
        }
        if self.obligations.is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligations",
                "bundle contains no proof obligations",
            ));
        }

        let mut seen = HashSet::new();
        for obligation in &self.obligations {
            if obligation.id.trim().is_empty() {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.id",
                    "obligation id is empty",
                ));
            } else if !seen.insert(obligation.id.as_str()) {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.id",
                    format!("duplicate obligation id `{}`", obligation.id),
                ));
            }
            if obligation.function.trim().is_empty() {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.function",
                    format!("obligation `{}` has an empty function name", obligation.id),
                ));
            }
            if obligation.claim.payload.trim().is_empty() {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.claim.payload",
                    format!("obligation `{}` has an empty claim payload", obligation.id),
                ));
            } else if let Err(diagnostic) = native_predicate_for_obligation(obligation) {
                diagnostics.push(diagnostic);
            }
            if obligation
                .claim
                .digest
                .as_ref()
                .is_some_and(|digest| !digest.is_hash_addressed())
            {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.claim.digest",
                    format!(
                        "obligation `{}` claim digest is not hash addressed",
                        obligation.id
                    ),
                ));
            }
            diagnostics.extend(obligation_metadata_diagnostics(obligation));

            let mut seen_summary_facts = HashSet::new();
            for fact in &obligation.summary_facts {
                if fact.id.trim().is_empty() {
                    diagnostics.push(BundleDiagnostic::invalid(
                        "obligation.summary_facts.id",
                        format!(
                            "obligation `{}` has an empty summary fact id",
                            obligation.id
                        ),
                    ));
                } else if !seen_summary_facts.insert(fact.id.as_str()) {
                    diagnostics.push(BundleDiagnostic::invalid(
                        "obligation.summary_facts.id",
                        format!(
                            "obligation `{}` has duplicate summary fact id `{}`",
                            obligation.id, fact.id
                        ),
                    ));
                }
                diagnostics.extend(fact.validation_diagnostics(&obligation.id));
            }
        }

        diagnostics
    }
}

fn obligation_metadata_diagnostics(obligation: &BundleObligation) -> Vec<BundleDiagnostic> {
    let mut diagnostics = Vec::new();
    if let Some(origin) = &obligation.metadata.native_origin {
        if origin.schema.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.native_origin.schema",
                format!(
                    "obligation `{}` native-origin schema is empty",
                    obligation.id
                ),
            ));
        }
        if let Some(digest) = &origin.tmir_module_digest {
            if !digest.is_hash_addressed() {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.native_origin.tmir_module_digest",
                    format!(
                        "obligation `{}` native-origin tMIR digest is not hash addressed",
                        obligation.id
                    ),
                ));
            }
        }
        validate_tmir_native_origin_metadata(obligation, origin, &mut diagnostics);
    }
    if let Some(verifier) = &obligation.metadata.native_verifier {
        validate_native_tool_identity(
            obligation,
            verifier,
            "obligation.metadata.native_verifier",
            "native verifier",
            &mut diagnostics,
        );
    }
    if let Some(replay) = &obligation.metadata.native_replay {
        validate_native_replay_identity(obligation, replay, &mut diagnostics);
    }
    for solver in &obligation.metadata.native_solvers {
        validate_native_tool_identity(
            obligation,
            solver,
            "obligation.metadata.native_solvers",
            "native solver",
            &mut diagnostics,
        );
    }
    if let Some(source) = &obligation.metadata.tmir_obligation_source {
        validate_tmir_obligation_source(obligation, source, &mut diagnostics);
    }

    let context = &obligation.metadata.proof_context;
    validate_proof_context_indexes(obligation, context, &mut diagnostics);
    for atom in &context.assumptions {
        validate_proof_atom(
            obligation,
            atom,
            BundleProofAtomRole::Assumption,
            &mut diagnostics,
        );
    }
    for atom in &context.assertions {
        validate_proof_atom(
            obligation,
            atom,
            BundleProofAtomRole::Assertion,
            &mut diagnostics,
        );
    }
    diagnostics
}

fn validate_tmir_native_origin_metadata(
    obligation: &BundleObligation,
    origin: &BundleNativeOrigin,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if !origin.schema.starts_with(TMIR_NATIVE_ORIGIN_SCHEMA_PREFIX) {
        return;
    }

    if origin.lineage_roots.is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_origin.lineage_roots",
            format!(
                "obligation `{}` native tMIR origin has no lineage root",
                obligation.id
            ),
        ));
    }
    if origin.tmir_module_digest.is_none() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_origin.tmir_module_digest",
            format!(
                "obligation `{}` native tMIR origin has no tMIR module digest",
                obligation.id
            ),
        ));
    }
    validate_required_native_tmir_metadata(obligation, diagnostics);

    let Some(source) = &obligation.metadata.tmir_obligation_source else {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.tmir_obligation_source",
            format!(
                "obligation `{}` has native tMIR origin metadata but no tMIR obligation source",
                obligation.id
            ),
        ));
        return;
    };

    let Some(source_function) = source.function_id else {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.tmir_obligation_source.function_id",
            format!(
                "obligation `{}` tMIR source has no function binding for native origin function {}",
                obligation.id, origin.function_id
            ),
        ));
        return;
    };
    if source_function != origin.function_id {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.tmir_obligation_source.function_id",
            format!(
                "obligation `{}` tMIR source function {} does not match native origin function {}",
                obligation.id, source_function, origin.function_id
            ),
        ));
    }
    validate_native_tmir_source_cause_matches_obligation_kind(obligation, source, diagnostics);
    validate_native_tmir_proof_atom_bindings(obligation, origin, source, diagnostics);

    if let Some(monomorphization_id) = source.monomorphization_id {
        let has_digest_bound_monomorphization = source.compiler_fact_refs.iter().any(|fact_ref| {
            fact_ref.kind == BundleTmirCompilerFactKind::Monomorphization
                && fact_ref.id == monomorphization_id
                && fact_ref
                    .digest
                    .as_ref()
                    .is_some_and(BundleDigest::is_hash_addressed)
        });
        if !has_digest_bound_monomorphization {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.tmir_obligation_source.compiler_fact_refs",
                format!(
                    "obligation `{}` tMIR source monomorphization {} is not bound by a matching hash-addressed compiler fact ref",
                    obligation.id, monomorphization_id
                ),
            ));
        }
    }

    for fact_ref in &source.compiler_fact_refs {
        if !fact_ref
            .digest
            .as_ref()
            .is_some_and(BundleDigest::is_hash_addressed)
        {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.tmir_obligation_source.compiler_fact_refs",
                format!(
                    "obligation `{}` native tMIR compiler fact ref `{}`/{} is not bound by a hash-addressed compiler fact digest",
                    obligation.id,
                    fact_ref.kind.as_str(),
                    fact_ref.id,
                ),
            ));
        }
    }
}

fn validate_required_native_tmir_metadata(
    obligation: &BundleObligation,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if obligation.metadata.tmir_source_span.is_none() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.tmir_source_span",
            format!(
                "obligation `{}` native tMIR origin has no typed tMIR source span",
                obligation.id
            ),
        ));
    }
    match &obligation.metadata.native_verifier {
        None => diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_verifier",
            format!(
                "obligation `{}` native tMIR origin has no native verifier identity",
                obligation.id
            ),
        )),
        // Accept the hyphen/underscore spellings interchangeably. The trust-ir
        // bridge stamps the provenance identity `trust_wp` (its `NativeToolIdentity`
        // convention, shared with trust-mc/trust-vc), while this crate's canonical
        // name is `trust-wp`. Normalizing `_`↔`-` lets a correctly-routed trust-wp
        // obligation (notably a `Precondition`, which is the only kind routed here)
        // pass the identity gate instead of failing closed on a pure spelling
        // mismatch. A genuinely FOREIGN identity (`trust-mc` / `trust-vc`) still
        // differs after normalization and is rejected — the gate stays fail-closed.
        Some(verifier)
            if verifier.name.replace('_', "-")
                != TRUST_WP_NATIVE_VERIFIER_NAME.replace('_', "-") =>
        {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.native_verifier.name",
                format!(
                    "obligation `{}` native tMIR origin expected verifier identity `{}`, expected `{TRUST_WP_NATIVE_VERIFIER_NAME}`",
                    obligation.id, verifier.name
                ),
            ));
        }
        Some(_) => {}
    }
    if obligation.metadata.native_solvers.is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_solvers",
            format!(
                "obligation `{}` native tMIR origin has no native solver identities",
                obligation.id
            ),
        ));
    } else {
        for (solver_index, solver) in obligation.metadata.native_solvers.iter().enumerate() {
            if is_empty_native_tool_identity(solver) {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.native_solvers",
                    format!(
                        "obligation `{}` native tMIR origin solver identity {solver_index} is an empty placeholder",
                        obligation.id
                    ),
                ));
            }
        }
    }
    if obligation.metadata.native_replay.is_none() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_replay",
            format!(
                "obligation `{}` native tMIR origin has no native replay identity with transcript digest",
                obligation.id
            ),
        ));
    }
}

fn validate_native_tmir_source_cause_matches_obligation_kind(
    obligation: &BundleObligation,
    source: &BundleTmirObligationSource,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if native_tmir_source_cause_matches_obligation_kind(&obligation.kind, &source.cause) {
        return;
    }

    diagnostics.push(BundleDiagnostic::invalid(
        "obligation.metadata.tmir_obligation_source.cause",
        format!(
            "obligation `{}` native tMIR source cause `{}` does not match obligation kind `{}`",
            obligation.id,
            source.cause.as_str(),
            obligation_kind_metadata_label(&obligation.kind),
        ),
    ));
}

fn native_tmir_source_cause_matches_obligation_kind(
    kind: &BundleObligationKind,
    cause: &BundleTmirObligationCause,
) -> bool {
    match kind {
        BundleObligationKind::Precondition { .. } => {
            matches!(cause, BundleTmirObligationCause::Precondition)
        }
        BundleObligationKind::Postcondition => {
            matches!(cause, BundleTmirObligationCause::Postcondition)
        }
        BundleObligationKind::Assertion { .. } => {
            matches!(cause, BundleTmirObligationCause::Assert)
        }
        BundleObligationKind::MemorySafety => matches!(
            cause,
            BundleTmirObligationCause::BoundsCheck
                | BundleTmirObligationCause::LayoutCheck
                | BundleTmirObligationCause::CastCheck
                | BundleTmirObligationCause::BorrowCheck
        ),
        BundleObligationKind::ArithmeticSafety => {
            matches!(cause, BundleTmirObligationCause::OverflowCheck)
        }
        BundleObligationKind::TranslationValidation { .. } => {
            matches!(cause, BundleTmirObligationCause::Translation)
        }
        BundleObligationKind::Other(kind) if kind == "panic_freedom" => {
            matches!(cause, BundleTmirObligationCause::Panic)
        }
        BundleObligationKind::LoopInvariant
        | BundleObligationKind::Termination
        | BundleObligationKind::Other(_) => true,
    }
}

fn obligation_kind_metadata_label(kind: &BundleObligationKind) -> String {
    match kind {
        BundleObligationKind::Precondition { callee } => format!("precondition:{callee}"),
        BundleObligationKind::Postcondition => "postcondition".to_string(),
        BundleObligationKind::Assertion { message } => format!("assertion:{message}"),
        BundleObligationKind::LoopInvariant => "loop_invariant".to_string(),
        BundleObligationKind::Termination => "termination".to_string(),
        BundleObligationKind::MemorySafety => "memory_safety".to_string(),
        BundleObligationKind::ArithmeticSafety => "arithmetic_safety".to_string(),
        BundleObligationKind::TranslationValidation { pass } => {
            format!("translation_validation:{pass}")
        }
        BundleObligationKind::Other(kind) => format!("other:{kind}"),
    }
}

fn validate_native_tool_identity(
    obligation: &BundleObligation,
    identity: &BundleNativeToolIdentity,
    field_prefix: &str,
    label: &str,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if identity.name.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            format!("{field_prefix}.name"),
            format!("obligation `{}` {label} name is empty", obligation.id),
        ));
    }
    if identity
        .digest
        .as_ref()
        .is_some_and(|digest| !digest.is_hash_addressed())
    {
        diagnostics.push(BundleDiagnostic::invalid(
            format!("{field_prefix}.digest"),
            format!(
                "obligation `{}` {label} digest is not hash addressed",
                obligation.id
            ),
        ));
    }
}

fn validate_native_replay_identity(
    obligation: &BundleObligation,
    replay: &BundleNativeReplayIdentity,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if replay.engine.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_replay.engine",
            format!(
                "obligation `{}` native replay engine is empty",
                obligation.id
            ),
        ));
    }
    if replay.invocation.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_replay.invocation",
            format!(
                "obligation `{}` native replay invocation is empty",
                obligation.id
            ),
        ));
    }
    if !replay.transcript_digest.is_hash_addressed() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.native_replay.transcript_digest",
            format!(
                "obligation `{}` native replay transcript digest is not hash addressed",
                obligation.id
            ),
        ));
    }
}

fn is_empty_native_tool_identity(identity: &BundleNativeToolIdentity) -> bool {
    identity.name == EMPTY_NATIVE_TOOL_PLACEHOLDER_NAME
        && identity.version.is_none()
        && identity.revision.is_none()
        && identity.digest.is_none()
}

fn validate_native_tmir_proof_atom_bindings(
    obligation: &BundleObligation,
    origin: &BundleNativeOrigin,
    source: &BundleTmirObligationSource,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    let context = &obligation.metadata.proof_context;
    let atoms = context
        .assumptions
        .iter()
        .chain(context.assertions.iter())
        .collect::<Vec<_>>();
    if atoms.is_empty() {
        return;
    }

    let mut seen_native_atom_ids = HashSet::new();
    for atom in atoms {
        match atom.native_replay_atom_id {
            Some(atom_id) if !seen_native_atom_ids.insert(atom_id) => {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.proof_context.native_replay_atom_id",
                    format!(
                        "obligation `{}` repeats native replay atom id {}",
                        obligation.id, atom_id
                    ),
                ));
            }
            Some(_) => {}
            None => diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.proof_context.native_replay_atom_id",
                format!(
                    "obligation `{}` native tMIR proof-context atom {} has no native replay atom id",
                    obligation.id, atom.index
                ),
            )),
        }

        if let Some(native_obligation_id) = atom.native_obligation_id {
            if native_obligation_id != origin.obligation_id {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.proof_context.native_obligation_id",
                    format!(
                        "obligation `{}` proof-context atom {} is bound to tMIR obligation {}, expected {}",
                        obligation.id, atom.index, native_obligation_id, origin.obligation_id
                    ),
                ));
            }
        }

        if let Some(native_assertion_id) = atom.native_assertion_id {
            if source.assertion_id != Some(native_assertion_id) {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.proof_context.native_assertion_id",
                    format!(
                        "obligation `{}` proof-context atom {} assertion id {} does not match tMIR source assertion {:?}",
                        obligation.id, atom.index, native_assertion_id, source.assertion_id
                    ),
                ));
            }
        }

        if let (Some(expected), Some(actual)) =
            (obligation.metadata.tmir_source_span, atom.native_span)
        {
            if expected != actual {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.proof_context.native_span",
                    format!(
                        "obligation `{}` proof-context atom {} span {:?} does not match tMIR source span {:?}",
                        obligation.id, atom.index, actual, expected
                    ),
                ));
            }
        }

        if atom.role == BundleProofAtomRole::Assertion
            && atom.native_obligation_id.is_none()
            && atom.native_assertion_id.is_none()
        {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.proof_context.assertion_binding",
                format!(
                    "obligation `{}` native tMIR assertion atom {} has no obligation or assertion binding",
                    obligation.id, atom.index
                ),
            ));
        }
    }
}

fn validate_tmir_obligation_source(
    obligation: &BundleObligation,
    source: &BundleTmirObligationSource,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if let BundleTmirObligationCause::Other(cause) = &source.cause {
        if cause.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.tmir_obligation_source.cause",
                format!(
                    "obligation `{}` tMIR obligation source has an empty cause",
                    obligation.id
                ),
            ));
        }
    }

    let mut seen = HashSet::new();
    for fact_ref in &source.compiler_fact_refs {
        if let BundleTmirCompilerFactKind::Other(kind) = &fact_ref.kind {
            if kind.trim().is_empty() {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.tmir_obligation_source.compiler_fact_refs.kind",
                    format!(
                        "obligation `{}` tMIR compiler fact ref {} has an empty kind",
                        obligation.id, fact_ref.id
                    ),
                ));
            }
        }
        if fact_ref
            .digest
            .as_ref()
            .is_some_and(|digest| !digest.is_hash_addressed())
        {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.tmir_obligation_source.compiler_fact_refs.digest",
                format!(
                    "obligation `{}` tMIR compiler fact ref `{}`/{} digest is not hash addressed",
                    obligation.id,
                    fact_ref.kind.as_str(),
                    fact_ref.id
                ),
            ));
        }
        if !seen.insert((&fact_ref.kind, fact_ref.id)) {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.tmir_obligation_source.compiler_fact_refs",
                format!(
                    "obligation `{}` repeats tMIR compiler fact ref `{}`/{}",
                    obligation.id,
                    fact_ref.kind.as_str(),
                    fact_ref.id
                ),
            ));
        }
    }
}

fn validate_proof_context_indexes(
    obligation: &BundleObligation,
    context: &BundleProofContext,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    let mut seen = HashSet::new();
    let mut expected_index = 0;
    for (label, atoms) in [
        ("assumption", context.assumptions.as_slice()),
        ("assertion", context.assertions.as_slice()),
    ] {
        for atom in atoms {
            if !seen.insert(atom.index) {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.proof_context.index",
                    format!(
                        "obligation `{}` repeats proof-context atom index {} in {label} context; indexes must be unique across assumptions and assertions",
                        obligation.id, atom.index
                    ),
                ));
            }
            if atom.index != expected_index {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.metadata.proof_context.index",
                    format!(
                        "obligation `{}` proof-context {label} atom index {} is not canonical; expected contiguous index {expected_index}",
                        obligation.id, atom.index
                    ),
                ));
            }
            expected_index += 1;
        }
    }
}

fn validate_proof_atom(
    obligation: &BundleObligation,
    atom: &BundleProofAtom,
    expected_role: BundleProofAtomRole,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if atom.role != expected_role {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.proof_context.role",
            format!(
                "obligation `{}` proof-context atom {} has role `{}` in the wrong list",
                obligation.id,
                atom.index,
                proof_atom_role_label(atom.role),
            ),
        ));
    }
    if atom.claim.payload.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.proof_context.claim.payload",
            format!(
                "obligation `{}` proof-context atom {} has an empty payload",
                obligation.id, atom.index
            ),
        ));
    } else {
        let probe_obligation = BundleObligation::new(
            format!(
                "{}::proof_context::{}::{}",
                obligation.id,
                proof_atom_role_label(expected_role),
                atom.index
            ),
            BundleObligationKind::Postcondition,
            obligation.function.clone(),
            atom.claim.clone(),
        );
        if let Err(diagnostic) = native_predicate_for_obligation(&probe_obligation) {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.metadata.proof_context.claim.payload",
                format!(
                    "obligation `{}` proof-context {} atom {} is not a typed boolean native proof claim: {}",
                    obligation.id,
                    proof_atom_role_label(expected_role),
                    atom.index,
                    diagnostic.message
                ),
            ));
        }
    }
    if atom
        .claim
        .digest
        .as_ref()
        .is_some_and(|digest| !digest.is_hash_addressed())
    {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.metadata.proof_context.claim.digest",
            format!(
                "obligation `{}` proof-context atom {} digest is not hash addressed",
                obligation.id, atom.index
            ),
        ));
    }
}

const fn proof_atom_role_label(role: BundleProofAtomRole) -> &'static str {
    match role {
        BundleProofAtomRole::Assumption => "assumption",
        BundleProofAtomRole::Assertion => "assertion",
    }
}

/// Metadata about the producer of a verification bundle.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleProducer {
    pub name: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub revision: Option<String>,
}

impl BundleProducer {
    /// Create producer metadata.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: None,
            revision: None,
        }
    }

    /// Attach a producer version.
    #[must_use]
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }

    /// Attach a source revision.
    #[must_use]
    pub fn with_revision(mut self, revision: impl Into<String>) -> Self {
        self.revision = Some(revision.into());
        self
    }
}

/// Target crate metadata for result correlation.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleTarget {
    pub crate_name: String,
    #[serde(default)]
    pub package_name: Option<String>,
    #[serde(default)]
    pub target_triple: Option<String>,
}

impl BundleTarget {
    /// Create target metadata from a crate name.
    #[must_use]
    pub fn new(crate_name: impl Into<String>) -> Self {
        Self {
            crate_name: crate_name.into(),
            package_name: None,
            target_triple: None,
        }
    }

    /// Attach a package name.
    #[must_use]
    pub fn with_package_name(mut self, package_name: impl Into<String>) -> Self {
        self.package_name = Some(package_name.into());
        self
    }

    /// Attach a target triple.
    #[must_use]
    pub fn with_target_triple(mut self, target_triple: impl Into<String>) -> Self {
        self.target_triple = Some(target_triple.into());
        self
    }
}

/// Verification options that affect proof acceptability.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifyBundleOptions {
    /// Require proof evidence before an obligation can count as verified.
    pub require_proof_evidence: bool,
    /// Optional per-obligation timeout in milliseconds.
    #[serde(default)]
    pub timeout_ms: Option<u64>,
}

impl Default for VerifyBundleOptions {
    fn default() -> Self {
        Self {
            require_proof_evidence: true,
            timeout_ms: None,
        }
    }
}

/// One proof obligation in a bundle.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleObligation {
    pub id: String,
    pub kind: BundleObligationKind,
    pub function: String,
    #[serde(default)]
    pub location: Option<BundleSourceSpan>,
    #[serde(default)]
    pub metadata: BundleObligationMetadata,
    pub claim: BundleClaim,
    /// Producer-supplied cross-crate facts available to native replay.
    ///
    /// These are not inferred by trust-wp. They must be hash-addressed facts
    /// emitted by tRust/tMIR or another trusted producer, and verified trust-wp
    /// evidence commits to them in its stable artifact manifest.
    #[serde(default)]
    pub summary_facts: Vec<BundleSummaryFact>,
}

impl BundleObligation {
    /// Create one proof obligation.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        kind: BundleObligationKind,
        function: impl Into<String>,
        claim: BundleClaim,
    ) -> Self {
        Self {
            id: id.into(),
            kind,
            function: function.into(),
            location: None,
            metadata: BundleObligationMetadata::default(),
            claim,
            summary_facts: Vec::new(),
        }
    }

    /// Attach a source location.
    #[must_use]
    pub fn with_location(mut self, location: BundleSourceSpan) -> Self {
        self.location = Some(location);
        self
    }

    /// Attach typed native-origin metadata.
    #[must_use]
    pub fn with_native_origin(mut self, origin: BundleNativeOrigin) -> Self {
        self.metadata.native_origin = Some(origin);
        self
    }

    /// Attach a typed tMIR source span.
    #[must_use]
    pub fn with_tmir_source_span(mut self, span: BundleTmirSourceSpan) -> Self {
        self.metadata.tmir_source_span = Some(span);
        self
    }

    /// Attach typed native verifier provenance.
    #[must_use]
    pub fn with_native_verifier(mut self, verifier: BundleNativeToolIdentity) -> Self {
        self.metadata.native_verifier = Some(verifier);
        self
    }

    /// Attach typed native replay identity and transcript provenance.
    #[must_use]
    pub fn with_native_replay(mut self, replay: BundleNativeReplayIdentity) -> Self {
        self.metadata.native_replay = Some(replay);
        self
    }

    /// Attach typed native solver/prover provenance.
    #[must_use]
    pub fn with_native_solver(mut self, solver: BundleNativeToolIdentity) -> Self {
        self.metadata.native_solvers.push(solver);
        self
    }

    /// Attach typed native solver/prover provenance.
    #[must_use]
    pub fn with_native_solvers(
        mut self,
        solvers: impl IntoIterator<Item = BundleNativeToolIdentity>,
    ) -> Self {
        self.metadata.native_solvers.extend(solvers);
        self
    }

    /// Attach typed tMIR obligation source/fact-reference metadata.
    #[must_use]
    pub fn with_tmir_obligation_source(mut self, source: BundleTmirObligationSource) -> Self {
        self.metadata.tmir_obligation_source = Some(source);
        self
    }

    /// Attach producer-supplied assumption/assertion context.
    #[must_use]
    pub fn with_proof_context(mut self, context: BundleProofContext) -> Self {
        self.metadata.proof_context = context;
        self
    }

    /// Attach one cross-crate summary fact available to replay.
    #[must_use]
    pub fn with_summary_fact(mut self, fact: BundleSummaryFact) -> Self {
        self.summary_facts.push(fact);
        self
    }
}

/// Machine-readable obligation metadata preserved from native producers.
#[non_exhaustive]
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleObligationMetadata {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_origin: Option<BundleNativeOrigin>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tmir_source_span: Option<BundleTmirSourceSpan>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_verifier: Option<BundleNativeToolIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_replay: Option<BundleNativeReplayIdentity>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub native_solvers: Vec<BundleNativeToolIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tmir_obligation_source: Option<BundleTmirObligationSource>,
    #[serde(default)]
    pub proof_context: BundleProofContext,
}

/// Native tMIR request/obligation identity for direct consumers.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleNativeOrigin {
    pub schema: String,
    pub mode: BundleNativeVerificationMode,
    pub request_id: u32,
    pub function_id: u32,
    pub obligation_id: u32,
    #[serde(default)]
    pub lineage_roots: Vec<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tmir_module_digest: Option<BundleDigest>,
}

impl BundleNativeOrigin {
    /// Create native request identity metadata.
    #[must_use]
    pub fn new(
        schema: impl Into<String>,
        mode: BundleNativeVerificationMode,
        request_id: u32,
        function_id: u32,
        obligation_id: u32,
    ) -> Self {
        Self {
            schema: schema.into(),
            mode,
            request_id,
            function_id,
            obligation_id,
            lineage_roots: Vec::new(),
            tmir_module_digest: None,
        }
    }

    /// Attach lineage-root ids from the native request.
    #[must_use]
    pub fn with_lineage_roots(mut self, roots: impl IntoIterator<Item = u32>) -> Self {
        self.lineage_roots.extend(roots);
        self
    }

    /// Attach the tMIR module digest that the native bundle validated.
    #[must_use]
    pub fn with_tmir_module_digest(mut self, digest: BundleDigest) -> Self {
        self.tmir_module_digest = Some(digest);
        self
    }
}

/// Native verifier mode preserved without string parsing.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleNativeVerificationMode {
    WeakestPrecondition,
    StrongestPostcondition,
    Abduction,
    Other(String),
}

impl BundleNativeVerificationMode {
    /// Stable mode label.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::WeakestPrecondition => "weakest_precondition",
            Self::StrongestPostcondition => "strongest_postcondition",
            Self::Abduction => "abduction",
            Self::Other(mode) => mode.as_str(),
        }
    }
}

/// Numeric tMIR source span preserved from in-process metadata.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleTmirSourceSpan {
    pub file_id: u32,
    pub line: u32,
    pub column: u32,
}

impl BundleTmirSourceSpan {
    /// Create a tMIR source span from typed file/line/column ids.
    #[must_use]
    pub const fn new(file_id: u32, line: u32, column: u32) -> Self {
        Self {
            file_id,
            line,
            column,
        }
    }
}

/// Stable identity of a native verifier/prover expected by the producer.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleNativeToolIdentity {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub revision: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digest: Option<BundleDigest>,
}

impl BundleNativeToolIdentity {
    /// Create typed native tool metadata.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: None,
            revision: None,
            digest: None,
        }
    }

    /// Attach a tool version.
    #[must_use]
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }

    /// Attach a tool source revision.
    #[must_use]
    pub fn with_revision(mut self, revision: impl Into<String>) -> Self {
        self.revision = Some(revision.into());
        self
    }

    /// Attach a hash-addressed tool digest.
    #[must_use]
    pub fn with_digest(mut self, digest: BundleDigest) -> Self {
        self.digest = Some(digest);
        self
    }
}

/// Replay identity for a native verifier request and its transcript.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleNativeReplayIdentity {
    pub engine: String,
    pub invocation: String,
    pub transcript_digest: BundleDigest,
}

impl BundleNativeReplayIdentity {
    /// Create native replay identity metadata.
    #[must_use]
    pub fn new(
        engine: impl Into<String>,
        invocation: impl Into<String>,
        transcript_digest: BundleDigest,
    ) -> Self {
        Self {
            engine: engine.into(),
            invocation: invocation.into(),
            transcript_digest,
        }
    }
}

/// tMIR source-map entry associated with a native obligation.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleTmirObligationSource {
    pub cause: BundleTmirObligationCause,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub assertion_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub monomorphization_id: Option<u32>,
    #[serde(default)]
    pub compiler_fact_refs: Vec<BundleTmirCompilerFactRef>,
}

impl BundleTmirObligationSource {
    /// Create tMIR source metadata for an obligation.
    #[must_use]
    pub fn new(cause: BundleTmirObligationCause) -> Self {
        Self {
            cause,
            function_id: None,
            assertion_id: None,
            monomorphization_id: None,
            compiler_fact_refs: Vec::new(),
        }
    }

    /// Attach the tMIR function id from the source map.
    #[must_use]
    pub fn with_function_id(mut self, function_id: u32) -> Self {
        self.function_id = Some(function_id);
        self
    }

    /// Attach the frontend assertion id from the tMIR source map.
    #[must_use]
    pub fn with_assertion_id(mut self, assertion_id: u32) -> Self {
        self.assertion_id = Some(assertion_id);
        self
    }

    /// Attach the frontend monomorphization id from the source map.
    #[must_use]
    pub fn with_monomorphization_id(mut self, monomorphization_id: u32) -> Self {
        self.monomorphization_id = Some(monomorphization_id);
        self
    }

    /// Attach typed compiler fact refs that justify this obligation source.
    #[must_use]
    pub fn with_compiler_fact_refs(
        mut self,
        refs: impl IntoIterator<Item = BundleTmirCompilerFactRef>,
    ) -> Self {
        self.compiler_fact_refs.extend(refs);
        self
    }
}

/// Typed tMIR reason an obligation was emitted.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleTmirObligationCause {
    Precondition,
    Postcondition,
    Assert,
    BoundsCheck,
    OverflowCheck,
    LayoutCheck,
    CastCheck,
    BorrowCheck,
    Translation,
    Panic,
    Temporal,
    Other(String),
}

impl BundleTmirObligationCause {
    /// Stable machine-readable cause label.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Precondition => "precondition",
            Self::Postcondition => "postcondition",
            Self::Assert => "assert",
            Self::BoundsCheck => "bounds_check",
            Self::OverflowCheck => "overflow_check",
            Self::LayoutCheck => "layout_check",
            Self::CastCheck => "cast_check",
            Self::BorrowCheck => "borrow_check",
            Self::Translation => "translation",
            Self::Panic => "panic",
            Self::Temporal => "temporal",
            Self::Other(cause) => cause.as_str(),
        }
    }
}

/// Typed tMIR compiler fact reference.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BundleTmirCompilerFactRef {
    pub kind: BundleTmirCompilerFactKind,
    pub id: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digest: Option<BundleDigest>,
}

impl BundleTmirCompilerFactRef {
    /// Reference an ADT-layout fact.
    #[must_use]
    pub const fn adt_layout(id: u32) -> Self {
        Self {
            kind: BundleTmirCompilerFactKind::AdtLayout,
            id,
            digest: None,
        }
    }

    /// Reference a fat-pointer fact.
    #[must_use]
    pub const fn fat_pointer(id: u32) -> Self {
        Self {
            kind: BundleTmirCompilerFactKind::FatPointer,
            id,
            digest: None,
        }
    }

    /// Reference a cast/transmute fact.
    #[must_use]
    pub const fn cast(id: u32) -> Self {
        Self {
            kind: BundleTmirCompilerFactKind::Cast,
            id,
            digest: None,
        }
    }

    /// Reference a monomorphization fact.
    #[must_use]
    pub const fn monomorphization(id: u32) -> Self {
        Self {
            kind: BundleTmirCompilerFactKind::Monomorphization,
            id,
            digest: None,
        }
    }

    /// Reference a producer-specific compiler fact kind.
    #[must_use]
    pub fn other(kind: impl Into<String>, id: u32) -> Self {
        Self {
            kind: BundleTmirCompilerFactKind::Other(kind.into()),
            id,
            digest: None,
        }
    }

    /// Attach the producer's stable digest for this compiler fact.
    #[must_use]
    pub fn with_digest(mut self, digest: BundleDigest) -> Self {
        self.digest = Some(digest);
        self
    }
}

/// Typed tMIR compiler fact table.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleTmirCompilerFactKind {
    AdtLayout,
    FatPointer,
    Cast,
    Monomorphization,
    Other(String),
}

impl BundleTmirCompilerFactKind {
    /// Stable machine-readable kind label.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::AdtLayout => "adt_layout",
            Self::FatPointer => "fat_pointer",
            Self::Cast => "cast",
            Self::Monomorphization => "monomorphization",
            Self::Other(kind) => kind.as_str(),
        }
    }
}

/// Producer-supplied proof context split into assumptions and assertions.
#[non_exhaustive]
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleProofContext {
    #[serde(default)]
    pub assumptions: Vec<BundleProofAtom>,
    #[serde(default)]
    pub assertions: Vec<BundleProofAtom>,
}

impl BundleProofContext {
    /// Create a proof context from typed assumption and assertion atoms.
    #[must_use]
    pub fn new(assumptions: Vec<BundleProofAtom>, assertions: Vec<BundleProofAtom>) -> Self {
        Self {
            assumptions,
            assertions,
        }
    }

    /// Returns true when no contextual atoms were supplied.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.assumptions.is_empty() && self.assertions.is_empty()
    }

    /// Return the canonical hash identity for this proof context.
    ///
    /// The digest is absent for an empty context. Non-empty contexts are hashed
    /// over ordered, role-separated atom identities, claim formats, optional
    /// claim digests, and claim payload digests. This is the same identity that
    /// native replay evidence commits to.
    #[must_use]
    pub fn canonical_digest(&self) -> Option<BundleDigest> {
        (!self.is_empty()).then(|| stable_digest(&proof_context_material(self)))
    }

    /// Return the canonical artifact-style identity for this proof context.
    #[must_use]
    pub fn canonical_identity(&self) -> Option<String> {
        self.canonical_digest().map(|digest| {
            format!(
                "{PROOF_EVIDENCE_SCHEMA_VERSION}/proof-context/{}/{}",
                digest.algorithm, digest.value
            )
        })
    }
}

fn proof_context_material(context: &BundleProofContext) -> String {
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nassumption-count={assumptions}\nassertion-count={assertions}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        assumptions = context.assumptions.len(),
        assertions = context.assertions.len(),
    );
    for atom in &context.assumptions {
        write_proof_atom_material(&mut material, "assumption", atom);
    }
    for atom in &context.assertions {
        write_proof_atom_material(&mut material, "assertion", atom);
    }
    material
}

fn write_proof_atom_material(material: &mut String, prefix: &str, atom: &BundleProofAtom) {
    let payload_digest = stable_digest(&atom.claim.payload);
    let _ = writeln!(
        material,
        "{prefix}.{index}.role={role}\n{prefix}.{index}.native-replay-atom={native_replay_atom}\n{prefix}.{index}.native-obligation={native_obligation}\n{prefix}.{index}.native-assertion={native_assertion}\n{prefix}.{index}.native-span={native_span}\n{prefix}.{index}.claim-format={claim_format}\n{prefix}.{index}.claim-digest={claim_digest}\n{prefix}.{index}.claim-payload-digest={payload_algorithm}:{payload_value}",
        index = atom.index,
        role = atom.role.as_str(),
        native_replay_atom = optional_u32_material(atom.native_replay_atom_id),
        native_obligation = optional_u32_material(atom.native_obligation_id),
        native_assertion = optional_u32_material(atom.native_assertion_id),
        native_span = optional_tmir_source_span_material(atom.native_span),
        claim_format = atom.claim.format.as_str(),
        claim_digest = digest_material(atom.claim.digest.as_ref()),
        payload_algorithm = payload_digest.algorithm.as_str(),
        payload_value = payload_digest.value.as_str(),
    );
}

fn optional_u32_material(value: Option<u32>) -> String {
    value.map_or_else(|| "none".to_string(), |value| value.to_string())
}

fn optional_tmir_source_span_material(value: Option<BundleTmirSourceSpan>) -> String {
    value.map_or_else(
        || "none".to_string(),
        |span| {
            format!(
                "file-id={};line={};column={}",
                span.file_id, span.line, span.column
            )
        },
    )
}

fn digest_material(digest: Option<&BundleDigest>) -> String {
    digest.map_or_else(
        || "none".to_string(),
        |digest| format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str()),
    )
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

/// One typed assumption or assertion carried with an obligation.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleProofAtom {
    pub index: u32,
    pub role: BundleProofAtomRole,
    pub claim: BundleClaim,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_replay_atom_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_obligation_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_assertion_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_span: Option<BundleTmirSourceSpan>,
}

impl BundleProofAtom {
    /// Create one proof-context atom.
    #[must_use]
    pub fn new(index: u32, role: BundleProofAtomRole, claim: BundleClaim) -> Self {
        Self {
            index,
            role,
            claim,
            native_replay_atom_id: None,
            native_obligation_id: None,
            native_assertion_id: None,
            native_span: None,
        }
    }

    /// Attach the tMIR native replay atom id this proof atom came from.
    #[must_use]
    pub fn with_native_replay_atom_id(mut self, atom_id: u32) -> Self {
        self.native_replay_atom_id = Some(atom_id);
        self
    }

    /// Attach the tMIR obligation id bound to this replay atom.
    #[must_use]
    pub fn with_native_obligation_id(mut self, obligation_id: u32) -> Self {
        self.native_obligation_id = Some(obligation_id);
        self
    }

    /// Attach the frontend assertion id bound to this replay atom.
    #[must_use]
    pub fn with_native_assertion_id(mut self, assertion_id: u32) -> Self {
        self.native_assertion_id = Some(assertion_id);
        self
    }

    /// Attach the tMIR source span bound to this replay atom.
    #[must_use]
    pub fn with_native_span(mut self, span: BundleTmirSourceSpan) -> Self {
        self.native_span = Some(span);
        self
    }
}

/// Role of a proof-context atom.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleProofAtomRole {
    Assumption,
    Assertion,
}

impl BundleProofAtomRole {
    /// Stable machine-readable role label.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Assumption => "assumption",
            Self::Assertion => "assertion",
        }
    }
}

/// Open-ended obligation kind aligned with tRust VC categories.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleObligationKind {
    Precondition { callee: String },
    Postcondition,
    Assertion { message: String },
    LoopInvariant,
    Termination,
    MemorySafety,
    ArithmeticSafety,
    TranslationValidation { pass: String },
    Other(String),
}

/// Hash-addressed cross-crate fact supplied by a bundle producer.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleSummaryFact {
    pub id: String,
    pub producer: String,
    pub source_crate: String,
    pub source_item: String,
    pub kind: BundleSummaryFactKind,
    pub digest: BundleDigest,
}

impl BundleSummaryFact {
    /// Create a summary fact with explicit source provenance.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        producer: impl Into<String>,
        source_crate: impl Into<String>,
        source_item: impl Into<String>,
        kind: BundleSummaryFactKind,
        digest: BundleDigest,
    ) -> Self {
        Self {
            id: id.into(),
            producer: producer.into(),
            source_crate: source_crate.into(),
            source_item: source_item.into(),
            kind,
            digest,
        }
    }

    fn validation_diagnostics(&self, obligation_id: &str) -> Vec<BundleDiagnostic> {
        let mut diagnostics = Vec::new();
        if self.producer.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.summary_facts.producer",
                format!(
                    "obligation `{obligation_id}` summary fact `{}` has an empty producer",
                    self.id
                ),
            ));
        }
        if self.source_crate.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.summary_facts.source_crate",
                format!(
                    "obligation `{obligation_id}` summary fact `{}` has an empty source crate",
                    self.id
                ),
            ));
        }
        if self.source_item.trim().is_empty() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.summary_facts.source_item",
                format!(
                    "obligation `{obligation_id}` summary fact `{}` has an empty source item",
                    self.id
                ),
            ));
        }
        if !self.digest.is_hash_addressed() {
            diagnostics.push(BundleDiagnostic::invalid(
                "obligation.summary_facts.digest",
                format!(
                    "obligation `{obligation_id}` summary fact `{}` is not hash addressed",
                    self.id
                ),
            ));
        }

        if let BundleSummaryFactKind::Other { schema } = &self.kind {
            if schema.trim().is_empty() {
                diagnostics.push(BundleDiagnostic::invalid(
                    "obligation.summary_facts.kind",
                    format!(
                        "obligation `{obligation_id}` summary fact `{}` has an empty kind schema",
                        self.id
                    ),
                ));
            }
        }

        match self.kind.endpoints() {
            Some(SummaryFactEndpoints::Textual { left, right }) => {
                validate_summary_endpoint(obligation_id, &self.id, "left", left, &mut diagnostics);
                validate_summary_endpoint(
                    obligation_id,
                    &self.id,
                    "right",
                    right,
                    &mut diagnostics,
                );
            }
            Some(SummaryFactEndpoints::Binding { left, right }) => {
                validate_summary_binding(obligation_id, &self.id, "left", left, &mut diagnostics);
                validate_summary_binding(obligation_id, &self.id, "right", right, &mut diagnostics);
            }
            None => {}
        }

        diagnostics
    }
}

/// Native summary fact kinds admitted by trust-wp replay.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleSummaryFactKind {
    /// Thin pointer equality backed by alias/provenance analysis.
    PointerProvenanceEq { left: String, right: String },
    /// Thin pointer equality over typed tMIR/trust-wp bindings.
    PointerProvenanceEqBinding { left: String, right: String },
    /// Thin pointer non-aliasing backed by alias/provenance analysis.
    PointerProvenanceDisjointBinding { left: String, right: String },
    /// Fat pointer equality backed by data-address and metadata equality.
    FatPointerMetadataEq { left: String, right: String },
    /// Fat pointer equality over typed tMIR/trust-wp bindings.
    FatPointerMetadataEqBinding { left: String, right: String },
    /// Fat pointer non-aliasing backed by data-address and metadata evidence.
    FatPointerMetadataDisjointBinding { left: String, right: String },
    /// Future fact kind carried for correlation but ignored by v1 replay.
    Other { schema: String },
}

impl BundleSummaryFactKind {
    /// Stable machine-readable kind label.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::PointerProvenanceEq { .. } => "pointer-provenance-eq",
            Self::PointerProvenanceEqBinding { .. } => "pointer-provenance-eq-binding",
            Self::PointerProvenanceDisjointBinding { .. } => "pointer-provenance-disjoint-binding",
            Self::FatPointerMetadataEq { .. } => "fat-pointer-metadata-eq",
            Self::FatPointerMetadataEqBinding { .. } => "fat-pointer-metadata-eq-binding",
            Self::FatPointerMetadataDisjointBinding { .. } => {
                "fat-pointer-metadata-disjoint-binding"
            }
            Self::Other { schema } => schema.as_str(),
        }
    }

    fn endpoints(&self) -> Option<SummaryFactEndpoints<'_>> {
        match self {
            Self::PointerProvenanceEq { left, right }
            | Self::FatPointerMetadataEq { left, right } => {
                Some(SummaryFactEndpoints::Textual { left, right })
            }
            Self::PointerProvenanceEqBinding { left, right }
            | Self::PointerProvenanceDisjointBinding { left, right }
            | Self::FatPointerMetadataEqBinding { left, right }
            | Self::FatPointerMetadataDisjointBinding { left, right } => {
                Some(SummaryFactEndpoints::Binding { left, right })
            }
            Self::Other { .. } => None,
        }
    }
}

enum SummaryFactEndpoints<'a> {
    Textual { left: &'a str, right: &'a str },
    Binding { left: &'a str, right: &'a str },
}

fn validate_summary_endpoint(
    obligation_id: &str,
    fact_id: &str,
    side: &str,
    endpoint: &str,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if endpoint.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.summary_facts.endpoint",
            format!(
                "obligation `{obligation_id}` summary fact `{fact_id}` has an empty {side} endpoint"
            ),
        ));
        return;
    }

    if let Err(err) = parse_contract(endpoint.trim()) {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.summary_facts.endpoint",
            format!(
                "obligation `{obligation_id}` summary fact `{fact_id}` has invalid {side} endpoint `{endpoint}`: {err}"
            ),
        ));
    }
}

fn validate_summary_binding(
    obligation_id: &str,
    fact_id: &str,
    side: &str,
    binding: &str,
    diagnostics: &mut Vec<BundleDiagnostic>,
) {
    if binding.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.summary_facts.binding",
            format!(
                "obligation `{obligation_id}` summary fact `{fact_id}` has an empty {side} binding"
            ),
        ));
        return;
    }

    if !is_summary_binding_name(binding) {
        diagnostics.push(BundleDiagnostic::invalid(
            "obligation.summary_facts.binding",
            format!(
                "obligation `{obligation_id}` summary fact `{fact_id}` has invalid {side} binding `{binding}`"
            ),
        ));
    }
}

fn is_summary_binding_name(binding: &str) -> bool {
    let mut chars = binding.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

/// Source span encoded without depending on rustc internals.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleSourceSpan {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl BundleSourceSpan {
    /// Create a source span.
    #[must_use]
    pub fn new(file: impl Into<String>, line: u32, column: u32) -> Self {
        Self {
            file: file.into(),
            line,
            column,
        }
    }
}

/// A machine-readable claim payload plus optional digest.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BundleClaim {
    pub format: BundleClaimFormat,
    pub payload: String,
    #[serde(default)]
    pub digest: Option<BundleDigest>,
}

impl BundleClaim {
    /// Create a claim from a known format and payload.
    #[must_use]
    pub fn new(format: BundleClaimFormat, payload: impl Into<String>) -> Self {
        Self {
            format,
            payload: payload.into(),
            digest: None,
        }
    }

    /// Attach a producer-supplied digest.
    #[must_use]
    pub fn with_digest(mut self, digest: BundleDigest) -> Self {
        self.digest = Some(digest);
        self
    }
}

/// Wire format of an obligation claim.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BundleClaimFormat {
    /// trust-wp pure-expression text parsed into native [`crate::formula::PureExpr`] proof input.
    TrustWpPureExprV1,
    /// SMT-LIB2 query text.
    SmtLib2,
    /// tRust `trust-types` formula JSON or another tRust-owned payload.
    TrustFormulaV1,
    /// Any future payload identified by a stable media type/schema string.
    Other(String),
}

impl BundleClaimFormat {
    /// Stable label used in proof and replay identity material.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::TrustWpPureExprV1 => "TrustWpPureExprV1",
            Self::SmtLib2 => "SMT-LIB2",
            Self::TrustFormulaV1 => "TrustFormulaV1",
            Self::Other(format) => format.as_str(),
        }
    }
}

/// Digest metadata for correlation across tools.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BundleDigest {
    pub algorithm: String,
    pub value: String,
}

impl BundleDigest {
    /// Create digest metadata.
    #[must_use]
    pub fn new(algorithm: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            algorithm: algorithm.into(),
            value: value.into(),
        }
    }
}

impl fmt::Display for BundleDigest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}:{}", self.algorithm, self.value)
    }
}
