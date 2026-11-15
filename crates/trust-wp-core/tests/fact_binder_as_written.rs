// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A pointer summary fact is about the obligation's own values: a free name, or one the
//! claim's opening universal quantifiers bind AS WRITTEN. A quantifier under a `let` or a
//! `match` arm binds another value (contract-syntax.md), even when the `let` or the arm only
//! renames a name: `{ let r = q; forall<p: &Int> p != r }` says every `p` differs from `q`,
//! which the `p` that is `q` falsifies, and a disjointness fact on the obligation's `p`, `q`
//! says nothing of it. Alias resolution substitutes the `let` away and moves the quantifier to
//! the front, where the fact bound it; the parser binds facts before it resolves aliases.
use trust_wp_core::verify_bundle::{
    BundleClaim, BundleClaimFormat, BundleDigest, BundleObligation, BundleObligationKind,
    BundleProducer, BundleSummaryFact, BundleSummaryFactKind, BundleTarget,
    NativeTrustWpBundleVerifier, VerifyBundleEngine, VerifyBundleRequest, VerifyBundleStatus,
};

fn fact(kind: BundleSummaryFactKind) -> BundleSummaryFact {
    BundleSummaryFact::new(
        "f",
        "tMIR",
        "dep_crate",
        "dep_crate::summary_source",
        kind,
        BundleDigest::new("sha256", format!("{:0<64}", "f")),
    )
}

fn verify(payload: &str, fact: BundleSummaryFact) -> VerifyBundleStatus {
    let obligation = BundleObligation::new(
        "fact-binder",
        BundleObligationKind::Postcondition,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, payload),
    )
    .with_summary_fact(fact);
    NativeTrustWpBundleVerifier
        .verify_bundle(
            VerifyBundleRequest::new(
                "bundle-native",
                BundleProducer::new("tRust"),
                BundleTarget::new("demo"),
            )
            .with_obligation(obligation),
        )
        .status
}

#[test]
fn a_fact_does_not_reach_a_quantifier_under_a_binder() {
    let disjoint = || {
        fact(BundleSummaryFactKind::PointerProvenanceDisjointBinding {
            left: "p".into(),
            right: "q".into(),
        })
    };
    let equal = || {
        fact(BundleSummaryFactKind::PointerProvenanceEqBinding {
            left: "p".into(),
            right: "q".into(),
        })
    };
    // Control: the obligation's own binders.
    assert_eq!(
        verify("forall<p: &Int> forall<q: &Int> p != q", disjoint()),
        VerifyBundleStatus::Verified
    );
    let mut verified = Vec::new();
    for (payload, fact) in [
        ("{ let r = q; forall<p: &Int> p != r }", disjoint()),
        ("{ let r = q; forall<p: &Int> !(p == r) }", disjoint()),
        ("match q { r => forall<p: &Int> p != r }", disjoint()),
        (
            "if let r = q { forall<p: &Int> p != r } else { false }",
            disjoint(),
        ),
        ("match (q,) { (r,) => forall<p: &Int> p != r }", disjoint()),
        (
            "match (q, 0) { (r, _) => forall<p: &Int> p != r }",
            disjoint(),
        ),
        (
            "forall<q: &Int> { let r = q; forall<p: &Int> p != r }",
            disjoint(),
        ),
        ("{ let r = q; forall<p: &Int> p == r }", equal()),
    ] {
        if verify(payload, fact) == VerifyBundleStatus::Verified {
            verified.push(payload);
        }
    }
    assert!(verified.is_empty(), "verified: {verified:#?}");
}
