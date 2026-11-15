use trust_ir::{
    request::validation_observer::ValidationObservation, NativeEvidenceBundle,
    ProofDigestAlgorithm, ValidatedNativeBundle,
};
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts_validated, trust_ir_native_bundle_to_body_verify_requests,
    trust_ir_native_bundle_to_body_verify_requests_validated,
    verify_trust_ir_body_contracts_validated,
};

use super::*;

#[test]
fn body_replay_refuses_unsupported_leaf_formats_on_the_same_fresh_input() {
    use trust_wp_lib::{ProofEvidenceFormat, VerifyBundleResult};

    let bundle = boolean_function("r == !x", true);
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let requests = trust_ir_native_bundle_to_body_verify_requests(&bundle).unwrap();
    let native = verify_trust_ir_body_contracts(&bundle).unwrap();
    assert_eq!(native.len(), 1);
    assert_eq!(native[0].status, VerifyBundleStatus::Verified);
    assert_eq!(
        verify_trust_ir_body_contracts_validated(&admitted).unwrap(),
        native
    );
    replay_trust_ir_body_contracts(&bundle, &native).unwrap();
    replay_trust_ir_body_contracts_validated(&admitted, &native).unwrap();
    replay_verify_bundle_result_evidence(&requests[0], &native[0]).unwrap();

    let mut accepted = Vec::new();
    for format in [
        ProofEvidenceFormat::AYProofCertificate,
        ProofEvidenceFormat::Lean5Term,
        ProofEvidenceFormat::ExternalCertificate("unsupported-checker".into()),
        ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1,
    ] {
        let mut leaves = native[0].obligation_results.clone();
        let BundleObligationStatus::Verified { evidence } = &mut leaves[0].status else {
            panic!("the positive native producer must supply a proof");
        };
        evidence.format = format.clone();
        assert!(
            evidence.is_proof_grade(),
            "structural metadata alone is insufficient"
        );
        let candidate =
            VerifyBundleResult::from_obligation_results(requests[0].clone(), leaves, Vec::new());
        let bytes = serde_json::to_vec(&candidate).unwrap();
        let candidate: VerifyBundleResult = serde_json::from_slice(&bytes).unwrap();
        let raw = replay_trust_ir_body_contracts(&bundle, std::slice::from_ref(&candidate));
        let reused =
            replay_trust_ir_body_contracts_validated(&admitted, std::slice::from_ref(&candidate));
        let generic = replay_verify_bundle_result_evidence(&requests[0], &candidate);
        if raw.is_ok() || reused.is_ok() || generic.is_ok() {
            eprintln!("unsupported format {format:?}: raw={raw:?}, reused={reused:?}, generic={generic:?}; candidate={}", String::from_utf8(bytes).unwrap());
            accepted.push(format);
        }
    }
    assert!(
        accepted.is_empty(),
        "unsupported leaf formats accepted: {accepted:?}"
    );
}

#[test]
fn immutable_admission_eliminates_one_actual_validation_with_identical_questions_and_results() {
    let bundle = boolean_function("r == !x", true);
    let original_bytes = serde_json::to_vec(&bundle).unwrap();
    let raw = ValidationObservation::start();
    let original_result = verify_trust_ir_body_contracts(&bundle).unwrap();
    replay_trust_ir_body_contracts(&bundle, &original_result).unwrap();
    assert_eq!(
        raw.calls(),
        2,
        "raw entry points each admit their own input"
    );
    drop(raw);

    let reused = ValidationObservation::start();
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let result = verify_trust_ir_body_contracts_validated(&admitted).unwrap();
    replay_trust_ir_body_contracts_validated(&admitted, &result).unwrap();
    assert_eq!(
        reused.calls(),
        1,
        "one actual canonical admission, two consumers"
    );
    assert_eq!(result, original_result);
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), original_bytes);
    drop(reused);

    assert_eq!(
        trust_ir_native_bundle_to_body_verify_requests(&bundle).unwrap(),
        trust_ir_native_bundle_to_body_verify_requests_validated(&admitted).unwrap(),
        "the typed proof question and complete obligation inventory are identical"
    );
}

#[test]
fn changed_program_claim_request_and_source_cannot_reuse_original_output() {
    let original = boolean_function("r == !x", true);
    let proof = verify_trust_ir_body_contracts(&original).unwrap();
    let mut wrong_request = original.clone();
    for request in &mut wrong_request.requests {
        if let NativeVerificationRequest::TrustWp(request) = request {
            request.id = NativeRequestId::new(999);
        }
    }
    let mut wrong_source = original.clone();
    wrong_source.provenance.source_digest = Some(digest(0xEE));
    for (name, changed) in [
        ("program", boolean_function("r == !x", false)),
        ("claim", boolean_function("r != !x", true)),
        ("request", wrong_request),
        ("source", wrong_source),
    ] {
        let observation = ValidationObservation::start();
        let accepted = ValidatedNativeBundle::new(&changed)
            .is_ok_and(|view| replay_trust_ir_body_contracts_validated(&view, &proof).is_ok());
        assert_eq!(
            observation.calls(),
            1,
            "the changed input is freshly checked"
        );
        drop(observation);
        let raw_accepted = replay_trust_ir_body_contracts(&changed, &proof).is_ok();
        assert!(
            !accepted && !raw_accepted,
            "original output transferred to changed {name}: validated={accepted}, raw={raw_accepted}"
        );
    }
}

#[test]
fn admitted_input_still_replays_and_refuses_changed_output_certificates() {
    let bundle = boolean_function("r == !x", true);
    let observation = ValidationObservation::start();
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let result = verify_trust_ir_body_contracts_validated(&admitted).unwrap();
    let mut wrong_identity = result.clone();
    wrong_identity[0].bundle_id.push_str("-other");
    let mut missing_artifacts = result.clone();
    missing_artifacts[0]
        .aggregate_evidence
        .as_mut()
        .unwrap()
        .artifacts
        .clear();
    let mut forged = result.clone();
    if let BundleObligationStatus::Verified { evidence } =
        &mut forged[0].obligation_results[0].status
    {
        evidence.artifacts[0] = evidence.artifacts[0]
            .clone()
            .with_utf8_bytes("forged proof payload");
    } else {
        panic!("positive fixture must carry evidence");
    }
    for changed in [wrong_identity, missing_artifacts, forged] {
        assert!(replay_trust_ir_body_contracts_validated(&admitted, &changed).is_err());
    }
    replay_trust_ir_body_contracts_validated(&admitted, &result).unwrap();
    assert_eq!(
        observation.calls(),
        1,
        "certificate replay stays independent of admission"
    );
}

#[test]
fn admitted_bundle_does_not_replace_the_shared_module_semantic_check() {
    let mut bundle = boolean_function("r == !x", true);
    let function = bundle.module.function_by_id_mut(FuncId::new(0)).unwrap();
    function.blocks[0].body = vec![
        InstrNode::new(Inst::UnOp {
            op: trust_ir::UnOp::Not,
            ty: Ty::Bool,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    refresh_native_bundle_module_identity(&mut bundle);
    let admitted =
        ValidatedNativeBundle::new(&bundle).expect("bundle admission is not instruction typing");
    let error = verify_trust_ir_body_contracts_validated(&admitted).unwrap_err();
    assert!(error.to_string().contains("UnOpNotOnScalarBool"), "{error}");
}

#[test]
fn body_identity_binds_input_evidence_without_absorbing_its_own_output() {
    let mut bundle = boolean_function("(r == !x) || !(r == !x)", true);
    let input = verify_trust_ir_native_bundle_and_record_evidence(&mut bundle).unwrap();
    assert_eq!(input.evidence_bundles.len(), 1);
    bundle.validate().unwrap();
    assert_eq!(
        bundle.stable_digest().algorithm,
        ProofDigestAlgorithm::Sha256
    );
    let before = serde_json::to_vec(&bundle).unwrap();
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    let proof = verify_trust_ir_body_contracts_validated(&admitted).unwrap();
    replay_trust_ir_body_contracts_validated(&admitted, &proof).unwrap();
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);

    // This is an admitted input descriptor, not authority for its missing
    // attachment bytes. Body WP does not assume any input evidence is true.
    let mut changed = bundle.clone();
    let NativeEvidenceBundle::TrustWp(input) = &mut changed.evidence_bundles[0] else {
        panic!("expected WP input evidence");
    };
    input.artifacts[0].digest = digest(0xEF);
    changed.validate().unwrap();
    assert_ne!(bundle.stable_digest(), changed.stable_digest());
    let changed = ValidatedNativeBundle::new(&changed).unwrap();
    assert!(replay_trust_ir_body_contracts_validated(&changed, &proof).is_err());
    assert!(replay_trust_ir_body_contracts(changed.bundle(), &proof).is_err());
}

#[test]
fn legacy_body_identity_remains_readable_but_is_not_admitted() {
    let bundle = boolean_function("r == !x", true);
    let mut legacy = trust_ir_native_bundle_to_body_verify_requests(&bundle).unwrap();
    for request in &mut legacy {
        request.bundle_id = request.bundle_id.split(":input:").next().unwrap().replacen(
            TRUST_IR_BODY_WP_SCHEMA,
            "trust-wp.trust-ir-body-wp.v1",
            1,
        );
    }
    let legacy: Vec<_> = legacy
        .into_iter()
        .map(trust_wp_lib::verify_bundle)
        .collect();
    assert_eq!(legacy[0].status, VerifyBundleStatus::Verified);
    let bytes = serde_json::to_vec(&legacy).unwrap();
    let legacy: Vec<trust_wp_lib::VerifyBundleResult> = serde_json::from_slice(&bytes).unwrap();
    assert!(replay_trust_ir_body_contracts(&bundle, &legacy).is_err());
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    assert!(replay_trust_ir_body_contracts_validated(&admitted, &legacy).is_err());
}
