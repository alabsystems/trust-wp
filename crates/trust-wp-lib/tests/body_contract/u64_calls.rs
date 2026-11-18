//! Each original full-domain compiler question is retained unchanged.
use trust_wp_lib::trust_ir_body::{replay_trust_ir_body_contracts, verify_trust_ir_body_contracts};

#[path = "u64_controls.rs"]
mod controls;

use super::*;

const CAPTURES: &[(&str, &str)] = &[
    (
        "clamp_unsigned_to_width",
        include_str!("fixtures/u64_calls/clamp_unsigned_to_width.json"),
    ),
    (
        "signed_fits_magnitude",
        include_str!("fixtures/u64_calls/signed_fits_magnitude.json"),
    ),
    (
        "signed_fits_nonneg",
        include_str!("fixtures/u64_calls/signed_fits_nonneg.json"),
    ),
    (
        "signed_max",
        include_str!("fixtures/u64_calls/signed_max.json"),
    ),
    (
        "signed_min_magnitude",
        include_str!("fixtures/u64_calls/signed_min_magnitude.json"),
    ),
    (
        "unsigned_fits",
        include_str!("fixtures/u64_calls/unsigned_fits.json"),
    ),
];

#[test]
fn original_typed_u64_postconditions_prove_and_replay_without_narrowing() {
    let mut failures = Vec::new();
    for (name, text) in CAPTURES {
        if *name == "signed_min_magnitude" {
            // This original capture carries only source identity, not a goal.
            // Its explicit refusal is retained in the separate control below.
            continue;
        }
        let bundle = derived_v9_capture(text);
        bundle.validate().unwrap();
        let original = bundle.clone();
        match verify_trust_ir_body_contracts(&bundle) {
            Ok(results)
                if results.len() == 1 && results[0].status == VerifyBundleStatus::Verified =>
            {
                replay_trust_ir_body_contracts(&bundle, &results).unwrap();
            }
            other => failures.push(format!("{name}: {other:#?}")),
        }
        assert_eq!(bundle, original);
    }
    assert_eq!(
        failures,
        Vec::<String>::new(),
        "original U64 questions must each verify"
    );
}

#[test]
fn source_identity_alone_never_supplies_the_missing_unsigned_goal() {
    let (_, text) = CAPTURES
        .iter()
        .find(|(name, _)| *name == "signed_min_magnitude")
        .unwrap();
    let bundle = derived_v9_capture(text);
    assert_eq!(
        bundle.module.proof_obligations[0]
            .formula
            .as_ref()
            .unwrap()
            .schema,
        "trust.trust_ir.obligation-source.v1"
    );
    let original = bundle.clone();
    let refusal = verify_trust_ir_body_contracts(&bundle)
        .unwrap_err()
        .to_string();
    assert!(refusal.contains("unreadable claim names"), "{refusal}");
    assert_eq!(bundle, original);
}
