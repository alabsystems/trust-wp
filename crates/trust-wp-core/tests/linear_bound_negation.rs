// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use trust_wp_core::verify_bundle::{
    replay_verify_bundle_result_evidence, BundleClaim, BundleClaimFormat, BundleObligation,
    BundleObligationKind, BundleProducer, BundleTarget, NativeTrustWpBundleVerifier,
    VerifyBundleEngine, VerifyBundleRequest, VerifyBundleStatus,
};

fn request(predicate: &str) -> VerifyBundleRequest {
    VerifyBundleRequest::new(
        "linear-bound-negation",
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

fn assert_unsupported(predicate: &str) {
    let request = request(predicate);
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(
        result.status,
        VerifyBundleStatus::Unsupported,
        "{result:#?}"
    );
    assert!(replay_verify_bundle_result_evidence(&request, &result).is_err());
}

fn assert_proved(predicate: &str) {
    let request = request(predicate);
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
    replay_verify_bundle_result_evidence(&request, &result).unwrap();
}

#[test]
fn signed_64_minimum_cancellation_on_the_right_is_exact() {
    assert_proved("(x >= 0) ==> x >= x + (-4611686018427387904 * 2)");
}

#[test]
fn signed_64_minimum_cancellation_on_the_left_is_exact() {
    assert_proved("(x >= 0) ==> x >= (-4611686018427387904 * 2) + x");
}

#[test]
fn unrepresentable_maximum_is_unsupported() {
    assert_unsupported("(-y + 9223372036854775807 >= 0) ==> x >= x + ((y + 1) / 2)");
}

#[test]
fn stronger_independent_maximum_is_kept_in_either_order() {
    for assumptions in [
        "-y + 9223372036854775807 >= 0 && -y - 1 >= 0",
        "-y - 1 >= 0 && -y + 9223372036854775807 >= 0",
    ] {
        assert_proved(&format!("({assumptions}) ==> x >= x + ((y + 1) / 2)"));
    }
}

#[test]
fn ordinary_bounds_still_prove_and_replay() {
    for predicate in [
        "(x >= 0) ==> x >= x + -2",
        "(x >= 0) ==> x >= -2 + x",
        "(-y - 1 >= 0) ==> x >= x + ((y + 1) / 2)",
    ] {
        assert_proved(predicate);
    }
}

#[test]
fn negation_boundaries_cannot_prove_false_claims() {
    for predicate in [
        "(x >= 0) ==> x < x + (-4611686018427387904 * 2)",
        "(x >= 0) ==> x + (-4611686018427387904 * 2) >= x",
        "(-y + 9223372036854775807 >= 0 && -y - 1 >= 0) ==> x > x + ((y + 1) / 2)",
    ] {
        assert_unsupported(predicate);
    }
}
