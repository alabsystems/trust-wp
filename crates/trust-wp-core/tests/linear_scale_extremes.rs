// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use trust_wp_core::verify_bundle::{
    replay_verify_bundle_result_evidence, BundleClaim, BundleClaimFormat, BundleObligation,
    BundleObligationKind, BundleProducer, BundleTarget, NativeTrustWpBundleVerifier,
    VerifyBundleEngine, VerifyBundleRequest, VerifyBundleStatus,
};

fn request(predicate: &str) -> VerifyBundleRequest {
    VerifyBundleRequest::new(
        "extreme-linear-scale",
        BundleProducer::new("core-test"),
        BundleTarget::new("integer-predicate"),
    )
    .with_obligation(BundleObligation::new(
        "bound",
        BundleObligationKind::Postcondition,
        "integer-predicate",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, predicate),
    ))
}

#[test]
fn later_unrepresentable_scale_keeps_an_independent_checked_bound() {
    let request = request("(-2 * x >= 0 && -x >= 0) ==> (((-4611686018427387904 * 2) * x) >= 0)");
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
    replay_verify_bundle_result_evidence(&request, &result).unwrap();
}

#[test]
fn extreme_scale_cannot_make_a_false_bound_true() {
    let request = request("(-2 * x >= 0 && -x >= 0) ==> (((-4611686018427387904 * 2) * x) >= 1)");
    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_ne!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
}

#[test]
fn signed_64_minimum_scale_is_exact_in_wider_replay() {
    let request = request(
        "(-x - y >= 0) ==> (((-4611686018427387904 * 2) * x + (-4611686018427387904 * 2) * y) >= 0)",
    );
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
    replay_verify_bundle_result_evidence(&request, &result).unwrap();
}

#[test]
fn unrepresentable_upper_bound_is_not_a_proof() {
    let request = request("(-y >= (-4611686018427387904 * 2) && z >= 1) ==> x >= x + (y / z)");
    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_ne!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
}
