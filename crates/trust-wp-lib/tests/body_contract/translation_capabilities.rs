//! An untranslated semantic witness must not erase ordinary native capability.
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts, replay_trust_ir_body_translation_witnesses,
    trust_ir_native_bundle_to_body_translation_witnesses, verify_trust_ir_body_contracts,
    NativeBodyWpTranslationCoverage,
};

use super::*;

#[test]
fn untranslated_original_unsigned_and_call_questions_keep_their_native_proofs() {
    for text in [
        include_str!("fixtures/local_calls/width_is_supported.json"),
        include_str!("fixtures/local_calls/conversion_code.json"),
        include_str!("fixtures/u64_calls/clamp_unsigned_to_width.json"),
        include_str!("fixtures/u64_calls/signed_fits_magnitude.json"),
    ] {
        let bundle = derived_v9_capture(text);
        bundle.validate().unwrap();
        let original = bundle.clone();
        let witnesses = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
        assert_eq!(witnesses.len(), 1);
        assert!(witnesses.iter().all(|row| matches!(&row.coverage,
            NativeBodyWpTranslationCoverage::Untranslated { reasons } if !reasons.is_empty())));
        replay_trust_ir_body_translation_witnesses(&bundle, &witnesses).unwrap();
        let results = verify_trust_ir_body_contracts(&bundle).unwrap();
        assert_eq!(results.len(), 1);
        assert!(results
            .iter()
            .all(|row| row.status == VerifyBundleStatus::Verified));
        replay_trust_ir_body_contracts(&bundle, &results).unwrap();
        assert_eq!(bundle, original);
    }
    let missing =
        derived_v9_capture(include_str!("fixtures/u64_calls/signed_min_magnitude.json"));
    let original = missing.clone();
    assert!(trust_ir_native_bundle_to_body_translation_witnesses(&missing).is_err());
    assert!(verify_trust_ir_body_contracts(&missing).is_err());
    assert_eq!(missing, original);
}
