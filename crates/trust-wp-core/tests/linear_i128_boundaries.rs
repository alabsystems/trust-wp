// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use trust_wp_core::verify_bundle::{
    replay_verify_bundle_result_evidence, BundleClaim, BundleClaimFormat, BundleObligation,
    BundleObligationKind, BundleProducer, BundleTarget, NativeTrustWpBundleVerifier,
    VerifyBundleEngine, VerifyBundleRequest, VerifyBundleStatus,
};

const MIN: &str = "((-4611686018427387904 * 2) * (4294967296 * 4294967296))";
const MAX: &str =
    "((9223372036854775807 * (4294967296 * 4294967296)) + ((4294967296 * 4294967296) - 1))";

fn question(predicate: &str) -> VerifyBundleRequest {
    VerifyBundleRequest::new(
        "checked-wide-linear",
        BundleProducer::new("core-test"),
        BundleTarget::new("exact-mathematical-integer"),
    )
    .with_obligation(BundleObligation::new(
        "bound",
        BundleObligationKind::Postcondition,
        "exact-mathematical-integer",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, predicate),
    ))
}

fn check(predicate: &str, expected: VerifyBundleStatus) {
    let request = question(predicate);
    let results = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(results.status, expected, "{predicate}: {results:#?}");
    assert_eq!(
        replay_verify_bundle_result_evidence(&request, &results).is_ok(),
        expected == VerifyBundleStatus::Verified
    );
}

#[test]
fn cancellation_cannot_negate_the_checked_wide_minimum() {
    for predicate in [
        format!("(x >= 0) ==> x >= x + {MIN}"),
        format!("(x >= 0) ==> x >= {MIN} + x"),
    ] {
        check(&predicate, VerifyBundleStatus::Unsupported);
    }
}

#[test]
fn exact_wide_constants_keep_both_sides_of_the_range() {
    for predicate in [
        format!("{MIN} < 0"),
        format!("{MAX} > 0"),
        "(4294967296 * 4294967296 - 1) > 9223372036854775807".into(),
    ] {
        check(&predicate, VerifyBundleStatus::Verified);
    }
}

#[test]
fn an_unrepresentable_maximum_cannot_supply_a_bound() {
    check(
        &format!("(-y + {MAX} >= 0) ==> x >= x + ((y + 1) / 2)"),
        VerifyBundleStatus::Unsupported,
    );
}

#[test]
fn an_independent_bound_survives_a_wide_negation_refusal() {
    for guards in [
        format!("-y + {MAX} >= 0 && -y - 1 >= 0"),
        format!("-y - 1 >= 0 && -y + {MAX} >= 0"),
    ] {
        check(
            &format!("({guards}) ==> x >= x + ((y + 1) / 2)"),
            VerifyBundleStatus::Verified,
        );
        let request = question(&format!("({guards}) ==> x > x + ((y + 1) / 2)"));
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
        assert_ne!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
        assert!(replay_verify_bundle_result_evidence(&request, &result).is_err());
    }
}

#[test]
fn checked_wide_scale_overflow_keeps_other_evidence() {
    check(
        &format!("(-2 * x >= 0 && -x >= 0) ==> (({MIN} * x) >= 0)"),
        VerifyBundleStatus::Verified,
    );
    check(
        &format!("(-x - y >= 0) ==> ({MIN} * x + {MIN} * y >= 0)"),
        VerifyBundleStatus::Unsupported,
    );
}

#[test]
fn overflowing_wide_intermediates_never_wrap_into_proofs() {
    for predicate in [
        format!("({MAX} + 1) <= 0"),
        format!("({MIN} * 2) >= 0"),
        format!("(x >= 0) ==> x < x + {MIN}"),
    ] {
        let request = question(&predicate);
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
        assert_ne!(
            result.status,
            VerifyBundleStatus::Verified,
            "{predicate}: {result:#?}"
        );
        assert!(replay_verify_bundle_result_evidence(&request, &result).is_err());
    }
}
