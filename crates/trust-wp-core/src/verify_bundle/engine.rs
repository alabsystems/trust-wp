// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    native_predicate_for_obligation,
    proof::{
        is_trust_wp_owned_obligation_kind, proof_evidence_for_obligation,
        proof_result_metadata_for_obligation, prove_native_pure_predicate, NativePureProofOutcome,
    },
    BundleDiagnostic, BundleObligation, BundleObligationResult, VerifyBundleRequest,
    VerifyBundleResult,
};

/// Engine trait for native bundle verification.
pub trait VerifyBundleEngine {
    /// Verify a complete bundle and return a fail-closed aggregate result.
    fn verify_bundle(&self, request: VerifyBundleRequest) -> VerifyBundleResult;
}

/// A verifier implementation that never proves obligations.
///
/// Use this as the default integration placeholder. Valid bundles return
/// `Unsupported`; malformed bundles return `Invalid`. Both states are
/// fail-closed and map to non-success exit codes.
#[derive(Debug, Clone, Copy, Default)]
pub struct FailClosedBundleVerifier;

impl VerifyBundleEngine for FailClosedBundleVerifier {
    fn verify_bundle(&self, request: VerifyBundleRequest) -> VerifyBundleResult {
        let diagnostics = request.validation_diagnostics();
        if !diagnostics.is_empty() {
            return VerifyBundleResult::invalid(request, diagnostics);
        }

        let results = request
            .obligations
            .iter()
            .map(|obligation| {
                BundleObligationResult::unsupported(
                    obligation.id.clone(),
                    "native verify-bundle engine is not implemented",
                )
            })
            .collect();

        VerifyBundleResult::from_obligation_results(
            request,
            results,
            vec![BundleDiagnostic::unsupported(
                "engine",
                "native verify-bundle engine is not implemented",
            )],
        )
    }
}

/// Native trust-wp verifier for the typed functional/deductive bundle fragment.
///
/// This verifier only accepts trust-wp-owned obligation kinds and
/// typed claim payloads decoded into [`crate::formula::PureExpr`]. The
/// first replay fragment proves tautological/refutable boolean predicates from
/// the typed tree and returns proof-grade replay evidence for every verified
/// obligation. Anything outside that fragment fails closed as `Unsupported`.
#[derive(Debug, Clone, Copy, Default)]
pub struct NativeTrustWpBundleVerifier;

impl VerifyBundleEngine for NativeTrustWpBundleVerifier {
    fn verify_bundle(&self, request: VerifyBundleRequest) -> VerifyBundleResult {
        let diagnostics = request.validation_diagnostics();
        if !diagnostics.is_empty() {
            return VerifyBundleResult::invalid(request, diagnostics);
        }

        let results = request
            .obligations
            .iter()
            .map(|obligation| verify_obligation(&request, obligation))
            .collect();

        VerifyBundleResult::from_obligation_results(request, results, Vec::new())
    }
}

fn verify_obligation(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> BundleObligationResult {
    if !is_trust_wp_owned_obligation_kind(&obligation.kind) {
        return BundleObligationResult::unsupported(
            obligation.id.clone(),
            "trust-wp does not own this obligation kind",
        );
    }

    let native_predicate = match native_predicate_for_obligation(obligation) {
        Ok(native_predicate) => native_predicate,
        Err(diagnostic) => {
            let mut result = BundleObligationResult::unsupported(
                obligation.id.clone(),
                "obligation claim is not native trust-wp proof input",
            );
            result.diagnostics.push(diagnostic);
            return result;
        }
    };

    match prove_native_pure_predicate(
        &native_predicate.predicate,
        native_predicate.claim_format,
        &obligation.summary_facts,
    ) {
        NativePureProofOutcome::Verified(proof) => {
            let evidence = proof_evidence_for_obligation(request, obligation, &proof);
            let metadata = proof_result_metadata_for_obligation(
                obligation,
                &native_predicate,
                &proof,
                &evidence,
            );
            BundleObligationResult::verified(obligation.id.clone(), evidence)
                .with_metadata(metadata)
        }
        NativePureProofOutcome::Failed(reason) => {
            BundleObligationResult::failed(obligation.id.clone(), reason)
        }
        NativePureProofOutcome::Unsupported(reason) => {
            BundleObligationResult::unsupported(obligation.id.clone(), reason)
        }
    }
}
