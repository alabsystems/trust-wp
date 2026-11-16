use trust_ir::{
    NativeVerifierSuite, TrustMcNativeRequest, TrustMcVerificationMode, TrustVcNativeRequest,
    TrustVcVerificationMode, ValidatedNativeBundle,
};
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_request_validated, trust_ir_native_bundle_to_body_translation_witnesses,
    verify_trust_ir_body_request_validated,
};

use super::*;

fn selected_id(bundle: &NativeVerificationBundle) -> NativeRequestId {
    bundle
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request.id),
            _ => None,
        })
        .unwrap()
}

fn mixed() -> NativeVerificationBundle {
    let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
    bundle.module.proof_obligations[0].site = Some(trust_ir::proof::ObligationSite::new(
        FuncId::new(0),
        BlockId::new(0),
        3,
    ));
    refresh_native_bundle_module_identity(&mut bundle);
    let wp = match &bundle.requests[0] {
        NativeVerificationRequest::TrustWp(request) => request.clone(),
        _ => panic!(),
    };
    let provenance = |suite, name: &str| {
        let mut p = wp.provenance.clone();
        p.verifier_suite = suite;
        p.expected_verifier.name = name.into();
        p.replay.as_mut().unwrap().engine = name.into();
        p
    };
    bundle
        .requests
        .push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(100),
            mode: TrustMcVerificationMode::BoundedModelCheck,
            function: wp.function,
            obligations: wp.obligations.clone(),
            lineage_roots: wp.lineage_roots.clone(),
            options: Default::default(),
            diagnostics: Default::default(),
            provenance: provenance(NativeVerifierSuite::TrustMc, "trust-mc"),
        }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
            id: NativeRequestId::new(101),
            mode: TrustVcVerificationMode::DischargeProofObligations,
            function: Some(wp.function),
            obligations: wp.obligations.clone(),
            lineage_roots: wp.lineage_roots.clone(),
            certificates: vec![],
            options: Default::default(),
            diagnostics: Default::default(),
            provenance: provenance(NativeVerifierSuite::TrustVc, "trust-vc"),
        }));
    bundle.validate().unwrap();
    bundle
}

#[test]
fn selected_verification_returns_the_actual_exact_question_over_all_siblings() {
    let bundle = mixed();
    let snapshot = bundle.clone();
    let id = selected_id(&bundle);
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let output = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
    assert_eq!(output.result().status, VerifyBundleStatus::Verified);
    let original = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
    assert_eq!(output.witness(), &original[0]);
    assert_eq!(
        output.witness().native_bundle_digest,
        bundle.stable_digest()
    );
    replay_verify_bundle_result_evidence(&output.witness().derived_request, output.result())
        .unwrap();
    replay_trust_ir_body_request_validated(&admitted, id, output.result(), Some(output.witness()))
        .unwrap();
    replay_trust_ir_body_request_validated(&admitted, id, output.result(), None).unwrap();
    assert_eq!(bundle, snapshot);
}

#[test]
fn unsupported_unselected_wp_remains_in_identity_without_blocking_selected_work() {
    let mut bundle = mixed();
    let id = selected_id(&bundle);
    let mut other = match &bundle.requests[0] {
        NativeVerificationRequest::TrustWp(request) => request.clone(),
        _ => panic!(),
    };
    other.id = NativeRequestId::new(102);
    other.mode = TrustWpVerificationMode::Abduction;
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(other));
    let snapshot = bundle.clone();
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    assert!(verify_trust_ir_body_contracts(&bundle).is_err());
    let output = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
    assert_eq!(output.result().status, VerifyBundleStatus::Verified);
    assert_eq!(
        output.witness().native_bundle_digest,
        bundle.stable_digest()
    );
    replay_trust_ir_body_request_validated(&admitted, id, output.result(), Some(output.witness()))
        .unwrap();
    assert!(verify_trust_ir_body_request_validated(&admitted, NativeRequestId::new(102)).is_err());
    assert_eq!(bundle, snapshot);
}

#[test]
fn changing_only_an_unselected_sibling_invalidates_the_old_full_question() {
    let bundle = mixed();
    let id = selected_id(&bundle);
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let output = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
    let mut changed = bundle.clone();
    let NativeVerificationRequest::TrustMc(request) = &mut changed.requests[1] else {
        panic!()
    };
    request.diagnostics.emit_counterexamples = !request.diagnostics.emit_counterexamples;
    let new = ValidatedNativeBundle::new(&changed).unwrap();
    let fresh = verify_trust_ir_body_request_validated(&new, id).unwrap();
    assert_eq!(
        fresh.witness().derived_request.obligations[0].claim.payload,
        output.witness().derived_request.obligations[0]
            .claim
            .payload
    );
    assert_ne!(
        fresh.witness().derived_request.bundle_id,
        output.witness().derived_request.bundle_id
    );
    assert!(replay_trust_ir_body_request_validated(
        &new,
        id,
        output.result(),
        Some(output.witness())
    )
    .is_err());
    assert!(replay_trust_ir_body_request_validated(&new, id, output.result(), None).is_err());
}

#[test]
fn selected_replay_checks_witness_data_and_native_evidence_independently() {
    let bundle = mixed();
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let id = selected_id(&bundle);
    let output = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
    for mutation in 0..6 {
        let mut witness = output.witness().clone();
        match mutation {
            0 => witness.native_bundle_digest = digest(0xEE),
            1 => witness.contracts[0].1.payload.push(' '),
            2 => witness.derived_request.obligations[0]
                .claim
                .payload
                .push(' '),
            3 => witness.parameters[0].1.push('_'),
            4 => witness.plan.position += 1,
            _ => witness.native_request_digest = digest(0xEF),
        }
        assert!(replay_trust_ir_body_request_validated(
            &admitted,
            id,
            output.result(),
            Some(&witness)
        )
        .is_err());
    }
    let false_bundle = boolean_function("(r : bool) != (x : bool)", false);
    let false_admitted = ValidatedNativeBundle::new(&false_bundle).unwrap();
    let failed =
        verify_trust_ir_body_request_validated(&false_admitted, selected_id(&false_bundle))
            .unwrap();
    assert_eq!(failed.result().status, VerifyBundleStatus::Failed);
    assert!(replay_trust_ir_body_request_validated(
        &admitted,
        id,
        failed.result(),
        Some(output.witness())
    )
    .is_err());
}

#[test]
fn explicit_selection_preserves_global_admission_and_the_original_proof_inventory() {
    let bundle = mixed();
    let id = selected_id(&bundle);
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    for wrong in [NativeRequestId::new(100), NativeRequestId::new(u32::MAX)] {
        assert!(verify_trust_ir_body_request_validated(&admitted, wrong).is_err());
    }
    let mut duplicate = bundle.clone();
    duplicate.requests.push(bundle.requests[1].clone());
    assert!(ValidatedNativeBundle::new(&duplicate).is_err());
    let mut empty = bundle.clone();
    let NativeVerificationRequest::TrustWp(request) = &mut empty.requests[0] else {
        panic!()
    };
    request.obligations.clear();
    if let Ok(view) = ValidatedNativeBundle::new(&empty) {
        assert!(verify_trust_ir_body_request_validated(&view, id).is_err());
    }
}
