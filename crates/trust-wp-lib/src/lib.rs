// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]

//! trust-wp Library API — stable, `rustc_private`-free verification interface.
//!
//! This crate provides a clean library API for external consumers (e.g., tRust)
//! to invoke trust-wp's verification engine without depending on `rustc_private`
//! or the trust-wp-driver compiler integration.
//!
//! # Architecture
//!
//! `trust-wp-lib` is a thin facade over `trust-wp-ay` and `trust-wp-core`. It:
//!
//! 1. Re-exports the stable subset of types that external consumers need
//! 2. Provides owned [`VerificationBundle`] / [`MutBorrowBundle`] types that
//!    can be constructed, serialized, and passed to verification
//! 3. Exposes top-level [`verify`] and [`verify_mut_borrow`] entry points
//!
//! # Usage
//!
//! ```rust,no_run
//! use trust_wp_lib::{VerificationBundle, verify};
//! use trust_wp_lib::PureExpr;
//!
//! let bundle = VerificationBundle::new(
//!     vec![/* preconditions */],
//!     vec![/* postconditions */],
//! );
//! let result = verify(&bundle).expect("verification should succeed");
//! ```
//!
//! # Serialization
//!
//! The tRust verify-bundle request/result boundary is serde-serializable
//! through the re-exported `VerifyBundle*` and `Bundle*` types. Use
//! [`verify_bundle`] for native requests or [`verify_trust_tmir_bundle`] for the
//! direct Trust/tMIR adapter path. The older [`VerificationBundle`] facade still
//! depends on `PureExpr` internals whose serde support is tracked separately.

pub mod bundle;
pub mod error;
pub mod result;
pub mod serial;
#[cfg(feature = "trust-ir-native")]
pub mod trust_ir_body;
#[cfg(feature = "trust-ir-native")]
pub mod trust_ir_native;

// --- Re-exports: trust-wp-core types ---

// --- Re-exports: bundle and error types ---
pub use bundle::{MutBorrowBundle, VerificationBundle};
pub use error::TrustWpLibError;
pub use serial::{
    deserialize_bundle, deserialize_verify_bundle_request, deserialize_verify_bundle_result,
    serialize_bundle, serialize_verify_bundle_request, serialize_verify_bundle_result,
};
#[cfg(feature = "trust-ir-native")]
pub use trust_ir_native::{
    trust_ir_native_bundle_to_verify_requests, verify_trust_ir_native_bundle,
    verify_trust_ir_native_bundle_and_record_evidence, verify_trust_ir_native_bundle_with_evidence,
    TrustIrClauseCarrier, TrustIrNativeBundleError, TrustIrNativeVerificationEvidenceOutput,
    TrustIrTrustWpMode, TrustIrUnsupportedClauseBindingReason, TrustIrUnsupportedModeReason,
    TrustIrUnsupportedObligationKindReason, TRUST_WP_PURE_EXPR_FORMULA_SCHEMA_VERSION,
};
// --- Re-exports: trust-wp-ay types ---
pub use trust_wp_ay::{
    BodyEffects, ClosureCaptureInfo, Counterexample, CounterexampleType, CounterexampleValue,
    EncodingError, LoopEncoderConfig, LoopVerificationContext, LoopVerificationResult,
    MutBorrowRequest, PostconditionInfo, ProofCertificateSummary, SolveStatisticsSnapshot,
    UnknownReason, VarOrigin, VerificationRequest, VerificationResult,
};
pub use trust_wp_core::{
    formula::{BinOp, BorrowFinality, BorrowIdOrigin, ExprSort, MatchArm, Pattern, PureExpr, UnOp},
    logic::{AdtDecl, AdtDecls, AdtFieldRanges, AdtKind, LogicFnDef, LogicMode, TypeInvariantDef},
    verify_bundle::{
        compile_trust_tmir_proof_call_vcs, create_native_pure_replay_evidence,
        create_native_pure_replay_result, replay_native_pure_evidence,
        replay_verify_bundle_result_evidence, trust_tmir_to_verify_bundle,
        trust_tmir_to_verify_bundle_with_budget, BundleClaim, BundleClaimFormat, BundleDiagnostic,
        BundleDiagnosticSeverity, BundleDigest, BundleEvidenceMetadata, BundleNativeOrigin,
        BundleNativeReplayIdentity, BundleNativeToolIdentity, BundleNativeVerificationMode,
        BundleObligation, BundleObligationKind, BundleObligationMetadata, BundleObligationResult,
        BundleObligationStatus, BundleProducer, BundleProofAtom, BundleProofAtomRole,
        BundleProofContext, BundleResultMetadata, BundleSolverMetadata, BundleSourceSpan,
        BundleSummaryFact, BundleSummaryFactKind, BundleTarget, BundleTmirCompilerFactKind,
        BundleTmirCompilerFactRef, BundleTmirObligationCause, BundleTmirObligationSource,
        BundleTmirSourceSpan, EvidenceArtifact, EvidenceArtifactBytes,
        EvidenceArtifactBytesEncoding, EvidenceArtifactKind, FailClosedBundleVerifier,
        NativeTrustWpBundleVerifier, ProofEvidence, ProofEvidenceFormat, ProofEvidenceWireError,
        ProofReplayError, ProofStrength, TrustFormulaDecodeError, TrustTmirAdapterBudget,
        TrustTmirAdapterError, TrustTmirAdapterMetrics, TrustTmirBinOp, TrustTmirBinding,
        TrustTmirBundle, TrustTmirExpr, TrustTmirFormula, TrustTmirObligation, TrustTmirProofCall,
        TrustTmirSort, TrustTmirUnaryOp, TrustWpMetadataEntry, TrustWpNativeReplayEvidenceInput,
        TrustWpNativeReplayMetadataError, VerifyBundleEngine, VerifyBundleOptions,
        VerifyBundleRequest, VerifyBundleResult, VerifyBundleStatus, PROOF_EVIDENCE_SCHEMA_VERSION,
        PROOF_EVIDENCE_WIRE_PREFIX, TMIR_NATIVE_ORIGIN_SCHEMA_PREFIX,
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION, TRUST_TMIR_ADAPTER_SCHEMA_VERSION,
        TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
        TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION, TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
        TRUST_WP_NATIVE_SOLVER_METADATA_KEY, TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
        TRUST_WP_NATIVE_VERIFIER_METADATA_KEY, TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
        TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY, TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
        TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION, VERIFY_BUNDLE_API_VERSION,
    },
    TrackLevel,
};

/// Verify a pure function's postconditions.
///
/// This is the primary entry point for external consumers.
/// Constructs a [`VerificationRequest`] from the bundle's owned fields
/// and delegates to [`trust_wp_ay::verify_function_with_modes`].
///
/// # Errors
///
/// Returns [`TrustWpLibError::Encoding`] if the verification encoder fails.
pub fn verify(bundle: &VerificationBundle) -> Result<VerificationResult, TrustWpLibError> {
    if is_structurally_empty_legacy_bundle(bundle) {
        return Ok(VerificationResult::Unknown(UnknownReason::SolverMessage(
            "verified function result lacks accepted solver evidence: structural provenance does not include verified solver evidence"
                .to_string(),
        )));
    }

    let mut request = VerificationRequest::new(&bundle.requires, &bundle.ensures)
        .return_expr(bundle.return_expr.as_ref())
        .total_int_arithmetic(bundle.total_int_arithmetic)
        .bitwise_proof(bundle.bitwise_proof)
        .track(bundle.track);

    if let Some(ref timeout) = bundle.timeout {
        request = request.timeout(Some(*timeout));
    }

    if !bundle.logic_fns.is_empty() {
        request = request.logic_fns(Some(&bundle.logic_fns));
    }
    if !bundle.mode_overrides.is_empty() {
        request = request.mode_overrides(Some(&bundle.mode_overrides));
    }
    if !bundle.type_invariants.is_empty() {
        request = request.type_invariants(Some(&bundle.type_invariants));
    }
    if !bundle.ghost_context.is_empty() {
        request = request.ghost_context(Some(&bundle.ghost_context));
    }
    if !bundle.type_constants.is_empty() {
        request = request.type_constants(Some(&bundle.type_constants));
    }
    if let Some(ref decls) = bundle.adt_decls {
        request = request.adt_decls(Some(decls.clone()));
    }
    if let Some(ref ranges) = bundle.adt_field_ranges {
        request = request.adt_field_ranges(Some(ranges.clone()));
    }

    trust_wp_ay::verify_function_with_modes(request).map_err(TrustWpLibError::from)
}

fn is_structurally_empty_legacy_bundle(bundle: &VerificationBundle) -> bool {
    bundle.requires.is_empty()
        && bundle.ensures.is_empty()
        && bundle.return_expr.is_none()
        && bundle.ghost_context.is_empty()
        && bundle.logic_fns.is_empty()
        && bundle.mode_overrides.is_empty()
        && bundle.type_invariants.is_empty()
        && bundle.adt_decls.is_none()
        && bundle.adt_field_ranges.is_none()
        && bundle.type_constants.is_empty()
}

/// Verify a function with mutable borrow patterns.
///
/// Constructs a [`MutBorrowRequest`] from the bundle's owned fields
/// and delegates to [`trust_wp_ay::verify_mut_borrow_function_with_modes`].
///
/// # Errors
///
/// Returns [`TrustWpLibError::Encoding`] if the verification encoder fails.
pub fn verify_mut_borrow(bundle: &MutBorrowBundle) -> Result<VerificationResult, TrustWpLibError> {
    let base = &bundle.base;

    let mut request = MutBorrowRequest::new(&base.requires, &base.ensures, &bundle.final_values)
        .return_expr(base.return_expr.as_ref())
        .total_int_arithmetic(base.total_int_arithmetic)
        .bitwise_proof(base.bitwise_proof)
        .track(base.track);

    if let Some(ref timeout) = base.timeout {
        request = request.timeout(Some(*timeout));
    }

    if !base.logic_fns.is_empty() {
        request = request.logic_fns(Some(&base.logic_fns));
    }
    if !base.mode_overrides.is_empty() {
        request = request.mode_overrides(Some(&base.mode_overrides));
    }
    if !base.type_invariants.is_empty() {
        request = request.type_invariants(Some(&base.type_invariants));
    }
    if !base.ghost_context.is_empty() {
        request = request.ghost_context(Some(&base.ghost_context));
    }
    if !base.type_constants.is_empty() {
        request = request.type_constants(Some(&base.type_constants));
    }
    if let Some(ref decls) = base.adt_decls {
        request = request.adt_decls(Some(decls.clone()));
    }
    if let Some(ref ranges) = base.adt_field_ranges {
        request = request.adt_field_ranges(Some(ranges.clone()));
    }

    // Mutable-borrow-specific fields
    if let Some(ref assumptions) = bundle.resolve_assumptions {
        request = request.resolve_assumptions(Some(assumptions.clone()));
    }
    if let Some(ref writebacks) = bundle.prophecy_writebacks {
        request = request.prophecy_writebacks(Some(writebacks.clone()));
    }
    if let Some(ref finality) = bundle.borrow_finality {
        request = request.borrow_finality(Some(finality.clone()));
    }
    if let Some(ref origins) = bundle.borrow_id_origins {
        request = request.borrow_id_origins(Some(origins.clone()));
    }
    if let Some(ref params) = bundle.mutation_continued_params {
        request = request.mutation_continued_params(Some(params.clone()));
    }

    trust_wp_ay::verify_mut_borrow_function_with_modes(request).map_err(TrustWpLibError::from)
}

/// Verify a tRust-style native bundle request through trust-wp's direct engine.
///
/// The result is fail-closed: malformed requests return `Invalid`, unsupported
/// obligations return `Unsupported`, and only proof-grade native obligations
/// return `Verified`.
#[must_use]
pub fn verify_bundle(request: VerifyBundleRequest) -> VerifyBundleResult {
    NativeTrustWpBundleVerifier.verify_bundle(request)
}

/// Convert and verify a direct Trust/tMIR bundle.
///
/// # Errors
///
/// Returns [`TrustWpLibError::TrustTmirAdapter`] when the adapter cannot produce
/// a supported native verify-bundle request.
pub fn verify_trust_tmir_bundle(
    bundle: TrustTmirBundle,
) -> Result<VerifyBundleResult, TrustWpLibError> {
    let request = trust_tmir_to_verify_bundle(bundle)?;
    Ok(verify_bundle(request))
}

/// Convert and verify a direct Trust/tMIR bundle after enforcing adapter budgets.
///
/// # Errors
///
/// Returns [`TrustWpLibError::TrustTmirAdapter`] when the bundle is unsupported
/// or exceeds the supplied deterministic work budget.
pub fn verify_trust_tmir_bundle_with_budget(
    bundle: TrustTmirBundle,
    budget: &TrustTmirAdapterBudget,
) -> Result<VerifyBundleResult, TrustWpLibError> {
    let request = trust_tmir_to_verify_bundle_with_budget(bundle, budget)?;
    Ok(verify_bundle(request))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_bundle_default_construction() {
        let bundle = VerificationBundle::new(vec![], vec![]);
        assert_eq!(bundle.requires, []);
        assert_eq!(bundle.ensures, []);
        assert!(bundle.return_expr.is_none());
        assert_eq!(bundle.ghost_context, []);
        assert!(bundle.logic_fns.is_empty());
        assert_eq!(bundle.mode_overrides, []);
        assert!(bundle.type_invariants.is_empty());
        assert!(bundle.adt_decls.is_none());
        assert!(bundle.adt_field_ranges.is_none());
        assert!(bundle.type_constants.is_empty());
        assert!(bundle.track.is_none());
        assert!(bundle.timeout.is_none());
        assert!(!bundle.total_int_arithmetic);
        assert!(bundle.bitwise_proof);
    }

    #[test]
    fn test_mut_borrow_bundle_default_construction() {
        let base = VerificationBundle::new(vec![], vec![]);
        let bundle = MutBorrowBundle::new(base, std::collections::HashMap::new());
        assert!(bundle.final_values.is_empty());
        assert!(bundle.resolve_assumptions.is_none());
        assert!(bundle.prophecy_writebacks.is_none());
        assert!(bundle.borrow_finality.is_none());
        assert!(bundle.borrow_id_origins.is_none());
        assert!(bundle.mutation_continued_params.is_none());
    }

    #[test]
    fn test_serialize_bundle_returns_pending_error() {
        let bundle = VerificationBundle::new(vec![], vec![]);
        let result = serialize_bundle(&bundle);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("serde support pending"),
            "expected serde pending message, got: {err}"
        );
    }

    #[test]
    fn test_deserialize_bundle_returns_pending_error() {
        let result = deserialize_bundle("{}");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("serde support pending"),
            "expected serde pending message, got: {err}"
        );
    }

    fn sample_verify_bundle_request() -> VerifyBundleRequest {
        let mut options = VerifyBundleOptions::default();
        options.require_proof_evidence = false;
        options.timeout_ms = Some(250);

        VerifyBundleRequest::new(
            "bundle-1",
            BundleProducer::new("tRust").with_version("0.1.0"),
            BundleTarget::new("demo_crate")
                .with_package_name("demo")
                .with_target_triple("x86_64-unknown-linux-gnu"),
        )
        .with_obligation(
            BundleObligation::new(
                "post-1",
                BundleObligationKind::Postcondition,
                "demo::f",
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true")
                    .with_digest(BundleDigest::new("sha256", "claim-digest")),
            )
            .with_location(BundleSourceSpan::new("src/lib.rs", 10, 5))
            .with_summary_fact(BundleSummaryFact::new(
                "summary-1",
                "tRust",
                "dep_crate",
                "dep_crate::g",
                BundleSummaryFactKind::Other {
                    schema: "trust.summary.v1".to_string(),
                },
                BundleDigest::new("sha256", "summary-digest"),
            )),
        )
        .with_options(options)
    }

    fn sample_trust_tmir_bundle() -> TrustTmirBundle {
        let x_nonnegative = TrustTmirExpr::binary(
            TrustTmirBinOp::Ge,
            TrustTmirExpr::var("x"),
            TrustTmirExpr::int(0),
        );
        let x_plus_one_positive = TrustTmirExpr::binary(
            TrustTmirBinOp::Gt,
            TrustTmirExpr::binary(
                TrustTmirBinOp::Add,
                TrustTmirExpr::var("x"),
                TrustTmirExpr::int(1),
            ),
            TrustTmirExpr::int(0),
        );
        let formula = TrustTmirFormula::new(TrustTmirExpr::binary(
            TrustTmirBinOp::Implies,
            x_nonnegative,
            x_plus_one_positive,
        ))
        .with_variable("x", TrustTmirSort::Int)
        .with_result(TrustTmirSort::Int);

        TrustTmirBundle::new("trust-tmir-lib-1", "demo", "demo::verified_from_tmir")
            .with_obligation(TrustTmirObligation::new(
                "post-1",
                BundleObligationKind::Postcondition,
                formula,
            ))
    }

    #[test]
    fn test_verify_bundle_request_json_round_trips() {
        let request = sample_verify_bundle_request();

        let json = serialize_verify_bundle_request(&request).expect("request serializes");
        let decoded =
            deserialize_verify_bundle_request(&json).expect("request deserializes from JSON");

        assert_eq!(decoded, request);
    }

    #[test]
    fn test_verify_bundle_result_json_round_trips() {
        let result = verify_bundle(sample_verify_bundle_request());
        assert_eq!(result.status, VerifyBundleStatus::Verified);

        let json = serialize_verify_bundle_result(&result).expect("result serializes");
        let decoded = deserialize_verify_bundle_result(&json).expect("result deserializes");

        assert_eq!(decoded, result);
    }

    #[test]
    fn test_verify_bundle_direct_entrypoint_verifies_native_request() {
        let result = verify_bundle(sample_verify_bundle_request());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        assert_eq!(result.exit_code(), 0);
        assert_eq!(result.obligation_results.len(), 1);
    }

    #[test]
    fn test_verify_trust_tmir_bundle_direct_entrypoint_verifies() {
        let result = verify_trust_tmir_bundle(sample_trust_tmir_bundle())
            .expect("Trust/tMIR bundle converts and verifies");

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        assert_eq!(result.exit_code(), 0);
        assert_eq!(result.obligation_results.len(), 1);
    }

    #[test]
    fn test_verify_trust_tmir_bundle_budget_fails_closed() {
        let mut budget = TrustTmirAdapterBudget::default();
        budget.max_expr_nodes = 1;

        let err = verify_trust_tmir_bundle_with_budget(sample_trust_tmir_bundle(), &budget)
            .expect_err("budget should reject bundle before verification");

        let TrustWpLibError::TrustTmirAdapter(err) = err else {
            panic!("expected Trust/tMIR adapter error");
        };
        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.severity == BundleDiagnosticSeverity::Unsupported
                && diagnostic.code == "trust_tmir.performance_budget"
                && diagnostic.message.contains("expr_nodes")
        }));
    }

    #[test]
    fn test_verify_empty_bundle_requires_accepted_solver_evidence() {
        // Empty legacy AY bundles carry only structural provenance. The
        // hardened facade keeps that fail-closed until accepted solver evidence
        // is available for downstream consumers.
        let bundle = VerificationBundle::new(vec![], vec![]);
        let result = verify(&bundle);
        assert!(
            result.is_ok(),
            "empty bundle verification failed: {result:?}"
        );
        match result.unwrap() {
            VerificationResult::Unknown(UnknownReason::SolverMessage(message)) => {
                assert!(message.contains("lacks accepted solver evidence"));
                assert!(message.contains("structural provenance"));
            }
            other => panic!("expected fail-closed Unknown for empty bundle, got: {other:?}"),
        }
    }

    #[test]
    fn test_verify_simple_postcondition() {
        // Verify that `true` as a postcondition with `true` body succeeds.
        let true_expr = PureExpr::Bool(true);
        let bundle = VerificationBundle {
            requires: vec![],
            ensures: vec![true_expr.clone()],
            return_expr: Some(true_expr),
            ..VerificationBundle::new(vec![], vec![])
        };
        let result = verify(&bundle);
        assert!(
            result.is_ok(),
            "trivial postcondition verification failed: {result:?}"
        );
    }
}
