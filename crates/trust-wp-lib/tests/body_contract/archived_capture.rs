//! Archived captures remain exact inputs to a refused handshake. Separate test
//! untrusted test envelopes exercise their unchanged modules and contracts.
use super::*;
use trust_ir::NativeVerificationBundleError;

pub(super) fn derived_v9_capture(text: &str) -> NativeVerificationBundle {
    // A future schema change needs a new reviewed derivation, not an upgrade
    // loop that silently changes the meaning of archived compiler evidence.
    assert_eq!(NativeVerificationBundle::SCHEMA_VERSION, 9);
    let original: NativeVerificationBundle = serde_json::from_str(text).unwrap();
    assert_eq!(original.schema_version, 8);
    assert_eq!(original.serialization.schema_version, 8);
    assert_eq!(
        original.validate(),
        Err(vec![
            NativeVerificationBundleError::UnsupportedSchemaVersion(8),
            NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(8),
        ])
    );
    assert_eq!(
        original.module.stable_digest(),
        original.trust_ir_module_digest
    );

    // This is newly authored untrusted test input, never live lowering or a
    // source-authority mint. The canonical constructor owns the new headers;
    // modules, requests, lineage, provenance and policy options stay exact.
    let current = NativeVerificationBundle::new(
        original.producer.clone(),
        original.input.clone(),
        original.trust_ir_module_digest,
        original.module.clone(),
        original.lineage.clone(),
    );
    let mut derived = original.clone();
    derived.schema_version = current.schema_version;
    derived.serialization.schema_version = current.serialization.schema_version;
    derived.validate().unwrap();
    let mut restored = derived.clone();
    restored.schema_version = 8;
    restored.serialization.schema_version = 8;
    assert_eq!(restored, original);
    derived
}

#[test]
fn archived_captures_refuse_old_handshakes_and_preserve_every_other_field() {
    for text in [
        include_str!("fixtures/local_calls/width_is_supported.json"),
        include_str!("fixtures/local_calls/width_supported.json"),
        include_str!("fixtures/local_calls/conversion_code.json"),
        include_str!("fixtures/u64_calls/clamp_unsigned_to_width.json"),
        include_str!("fixtures/u64_calls/signed_fits_magnitude.json"),
        include_str!("fixtures/u64_calls/signed_fits_nonneg.json"),
        include_str!("fixtures/u64_calls/signed_max.json"),
        include_str!("fixtures/u64_calls/signed_min_magnitude.json"),
        include_str!("fixtures/u64_calls/unsigned_fits.json"),
        include_str!("fixtures/budget/megabytes_of.json"),
        include_str!("fixtures/budget/per_job_bytes.json"),
        include_str!("fixtures/budget/split_budget_ms.json"),
        include_str!("fixtures/widthconv/extension_bits.json"),
        include_str!("fixtures/widthconv/shift_mask.json"),
    ] {
        let derived = derived_v9_capture(text);
        let mut document = serde_json::to_value(derived).unwrap();
        document["schema_version"] = 8.into();
        document["serialization"]["schema_version"] = 8.into();
        let mut expected: serde_json::Value = serde_json::from_str(text).unwrap();
        // Current canonical encoding writes this previously omitted, empty
        // module collection. No captured layout or semantic digest is changed.
        let layouts = expected["module"]
            .as_object_mut()
            .unwrap()
            .entry("closure_layouts")
            .or_insert_with(|| serde_json::json!([]));
        assert_eq!(layouts, &serde_json::json!([]));
        assert!(document == expected, "derived envelope changed an archived field");
    }
}

#[test]
fn derivation_cannot_hide_other_invalid_capture_fields() {
    let text = include_str!("fixtures/local_calls/width_is_supported.json");
    let mut document: serde_json::Value = serde_json::from_str(text).unwrap();
    document["serialization"]["canonical_order"] = false.into();
    assert!(std::panic::catch_unwind(|| derived_v9_capture(&document.to_string())).is_err());
    document["serialization"]["canonical_order"] = true.into();
    document["schema_version"] = 7.into();
    assert!(std::panic::catch_unwind(|| derived_v9_capture(&document.to_string())).is_err());
}
