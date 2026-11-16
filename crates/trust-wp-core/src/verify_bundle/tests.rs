// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn claim() -> BundleClaim {
    BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result > 0")
        .with_digest(BundleDigest::new("sha256", "abc123"))
}

fn obligation(id: &str) -> BundleObligation {
    BundleObligation::new(
        id,
        BundleObligationKind::Postcondition,
        "demo::verified",
        claim(),
    )
    .with_location(BundleSourceSpan::new("src/lib.rs", 10, 5))
}

fn request() -> VerifyBundleRequest {
    VerifyBundleRequest::new(
        "bundle-1",
        BundleProducer::new("tRust")
            .with_version("0.1.0")
            .with_revision("rev123"),
        BundleTarget::new("demo")
            .with_package_name("demo")
            .with_target_triple("x86_64-unknown-linux-gnu"),
    )
    .with_obligation(obligation("obl-1"))
}

fn evidence() -> ProofEvidence {
    let digest = BundleDigest::new("sha256", "proof123");
    ProofEvidence::checked(
        "ay",
        ProofEvidenceFormat::AYProofCertificate,
        "ay-proof-checker",
    )
    .with_strength(ProofStrength::Certified)
    .with_digest(digest.clone())
    .with_artifact(EvidenceArtifact::new(
        EvidenceArtifactKind::ProofCertificate,
        digest,
        "test proof certificate",
    ))
}

fn native_verified_evidence(request: &VerifyBundleRequest) -> ProofEvidence {
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    evidence.clone()
}

fn single_obligation_request(obligation: BundleObligation) -> VerifyBundleRequest {
    VerifyBundleRequest::new(
        "bundle-native",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    )
    .with_obligation(obligation)
}

fn typed_obligation(id: &str, kind: BundleObligationKind, payload: &str) -> BundleObligation {
    BundleObligation::new(
        id,
        kind,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, payload),
    )
}

fn trust_formula_obligation(
    id: &str,
    kind: BundleObligationKind,
    payload: &str,
) -> BundleObligation {
    BundleObligation::new(
        id,
        kind,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::TrustFormulaV1, payload),
    )
}

fn typed_obligation_with_claim_digest(
    id: &str,
    kind: BundleObligationKind,
    payload: &str,
    digest: BundleDigest,
) -> BundleObligation {
    let mut obligation = typed_obligation(id, kind, payload);
    obligation.claim = obligation.claim.with_digest(digest);
    obligation
}

fn summary_digest(label: &str) -> BundleDigest {
    BundleDigest::new("sha256", format!("{label:0<64}"))
}

fn pointer_summary_fact(id: &str, left: &str, right: &str) -> BundleSummaryFact {
    BundleSummaryFact::new(
        id,
        "tMIR",
        "dep_crate",
        "dep_crate::summary_source",
        BundleSummaryFactKind::PointerProvenanceEq {
            left: left.to_string(),
            right: right.to_string(),
        },
        summary_digest(id),
    )
}

fn fat_pointer_summary_fact(id: &str, left: &str, right: &str) -> BundleSummaryFact {
    BundleSummaryFact::new(
        id,
        "tMIR",
        "dep_crate",
        "dep_crate::slice_summary_source",
        BundleSummaryFactKind::FatPointerMetadataEq {
            left: left.to_string(),
            right: right.to_string(),
        },
        summary_digest(id),
    )
}

fn pointer_binding_summary_fact(id: &str, left: &str, right: &str) -> BundleSummaryFact {
    BundleSummaryFact::new(
        id,
        "tMIR",
        "dep_crate",
        "dep_crate::summary_source",
        BundleSummaryFactKind::PointerProvenanceEqBinding {
            left: left.to_string(),
            right: right.to_string(),
        },
        summary_digest(id),
    )
}

fn pointer_disjoint_binding_summary_fact(id: &str, left: &str, right: &str) -> BundleSummaryFact {
    BundleSummaryFact::new(
        id,
        "tMIR",
        "dep_crate",
        "dep_crate::summary_source",
        BundleSummaryFactKind::PointerProvenanceDisjointBinding {
            left: left.to_string(),
            right: right.to_string(),
        },
        summary_digest(id),
    )
}

fn fat_pointer_disjoint_binding_summary_fact(
    id: &str,
    left: &str,
    right: &str,
) -> BundleSummaryFact {
    BundleSummaryFact::new(
        id,
        "tMIR",
        "dep_crate",
        "dep_crate::slice_summary_source",
        BundleSummaryFactKind::FatPointerMetadataDisjointBinding {
            left: left.to_string(),
            right: right.to_string(),
        },
        summary_digest(id),
    )
}

fn native_tmir_origin_obligation(id: &str) -> BundleObligation {
    typed_obligation(id, BundleObligationKind::Postcondition, "true")
        .with_native_origin(
            BundleNativeOrigin::new(
                "tmir.native-verification-bundle.v2",
                BundleNativeVerificationMode::WeakestPrecondition,
                7,
                2,
                0,
            )
            .with_lineage_roots([0])
            .with_tmir_module_digest(BundleDigest::new("sha256", "c".repeat(64))),
        )
        .with_tmir_source_span(BundleTmirSourceSpan::new(4, 29, 7))
        .with_native_verifier(
            BundleNativeToolIdentity::new("trust-wp")
                .with_version("native-schema-v2")
                .with_revision("6dfb614"),
        )
        .with_native_replay(BundleNativeReplayIdentity::new(
            "trust-wp",
            "trust-wp verify --native-bundle test",
            BundleDigest::new("sha256", "d".repeat(64)),
        ))
        .with_native_solver(
            BundleNativeToolIdentity::new("ay")
                .with_version("0.9.0")
                .with_revision("solver-rev"),
        )
        .with_tmir_obligation_source(
            BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
                .with_function_id(2),
        )
}

fn native_replay_metadata_input() -> TrustWpNativeReplayEvidenceInput {
    TrustWpNativeReplayEvidenceInput::from_obligation(
        &native_tmir_origin_obligation("obl-native-replay-metadata")
            .with_proof_context(BundleProofContext::new(
                vec![BundleProofAtom::new(
                    0,
                    BundleProofAtomRole::Assumption,
                    BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
                )
                .with_native_replay_atom_id(7)
                .with_native_obligation_id(0)
                .with_native_span(BundleTmirSourceSpan::new(4, 29, 7))],
                vec![BundleProofAtom::new(
                    1,
                    BundleProofAtomRole::Assertion,
                    BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
                )
                .with_native_replay_atom_id(8)
                .with_native_obligation_id(0)
                .with_native_span(BundleTmirSourceSpan::new(4, 29, 7))],
            ))
            .with_summary_fact(pointer_binding_summary_fact(
                "summary-1",
                "left_ptr",
                "right_ptr",
            )),
    )
    .expect("test obligation has complete native replay metadata")
    .with_claim_digest(BundleDigest::new("sha256", "claim-digest"))
}

#[test]
fn test_trust_wp_metadata_key_constants_match_trust_adapter_contract() {
    assert_eq!(
        TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
        "trust.trust-wp.native-origin.v1"
    );
    assert_eq!(
        TRUST_WP_CLAIM_DIGEST_METADATA_KEY,
        "trust.trust-wp.claim-digest.v1"
    );
    assert_eq!(
        TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
        "trust.trust-wp.tmir-source-span.v1"
    );
    assert_eq!(
        TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
        "trust.trust-wp.native-verifier.v1"
    );
    assert_eq!(
        TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
        "trust.trust-wp.native-replay.v1"
    );
    assert_eq!(
        TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
        "trust.trust-wp.native-solver.v1"
    );
    assert_eq!(
        TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
        "trust.trust-wp.tmir-obligation-source.v1"
    );
    assert_eq!(
        TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
        "trust.trust-wp.proof-context.v1"
    );
    assert_eq!(
        TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
        "trust.trust-wp.summary-fact.v1"
    );
}

#[test]
fn test_native_replay_metadata_input_roundtrips_through_stable_entries() {
    let input = native_replay_metadata_input();
    let entries = input
        .to_metadata_entries()
        .expect("typed native replay metadata should serialize");

    assert!(entries
        .iter()
        .any(|entry| entry.key == TRUST_WP_NATIVE_ORIGIN_METADATA_KEY));
    assert!(entries
        .iter()
        .any(|entry| entry.key == TRUST_WP_CLAIM_DIGEST_METADATA_KEY));
    assert!(entries
        .iter()
        .any(|entry| entry.key == TRUST_WP_NATIVE_SOLVER_METADATA_KEY));
    assert!(entries
        .iter()
        .any(|entry| entry.key == TRUST_WP_PROOF_CONTEXT_METADATA_KEY));
    assert!(entries
        .iter()
        .any(|entry| entry.key == TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY));

    let parsed = TrustWpNativeReplayEvidenceInput::from_metadata_pairs(
        entries
            .iter()
            .map(|entry| (entry.key.as_str(), entry.value.as_str())),
    )
    .expect("stable metadata entries should parse");

    assert_eq!(parsed, input);

    let bare_obligation = typed_obligation(
        "obl-native-replay-metadata",
        BundleObligationKind::Postcondition,
        "true",
    );
    let trust_wp_obligation = parsed.apply_to_obligation(bare_obligation);
    assert_eq!(
        TrustWpNativeReplayEvidenceInput::from_obligation(&trust_wp_obligation)
            .expect("applied obligation should expose native replay input"),
        input
    );
    assert_eq!(
        input.validation_diagnostics_for_obligation(&typed_obligation(
            "obl-native-replay-metadata",
            BundleObligationKind::Postcondition,
            "true",
        )),
        Vec::new()
    );
}

#[test]
fn test_native_replay_metadata_input_rejects_missing_solver_identity() {
    let input = native_replay_metadata_input();
    let mut entries = input
        .to_metadata_entries()
        .expect("typed native replay metadata should serialize");
    entries.retain(|entry| entry.key != TRUST_WP_NATIVE_SOLVER_METADATA_KEY);

    let err = TrustWpNativeReplayEvidenceInput::from_metadata_pairs(
        entries
            .iter()
            .map(|entry| (entry.key.as_str(), entry.value.as_str())),
    )
    .expect_err("missing solver metadata should fail closed");

    assert_eq!(
        err,
        TrustWpNativeReplayMetadataError::Missing {
            key: TRUST_WP_NATIVE_SOLVER_METADATA_KEY
        }
    );
}

#[test]
fn test_public_native_replay_result_helper_matches_engine_output() {
    let obligation = native_replay_metadata_input().apply_to_obligation(typed_obligation(
        "obl-native-replay-helper",
        BundleObligationKind::Postcondition,
        "true",
    ));
    let request = single_obligation_request(obligation);

    let helper_result = create_native_pure_replay_result(&request, &request.obligations[0])
        .expect("helper should create verified replay result");
    let helper_evidence = create_native_pure_replay_evidence(&request, &request.obligations[0])
        .expect("helper should create proof evidence");
    let engine_result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(engine_result.status, VerifyBundleStatus::Verified);
    assert_eq!(
        engine_result.obligation_results,
        vec![helper_result.clone()]
    );
    let BundleObligationStatus::Verified { evidence } = &helper_result.status else {
        panic!("expected verified helper result");
    };
    assert_eq!(evidence, &helper_evidence);
    assert!(helper_result.metadata.solver.is_some());
    assert!(helper_result.metadata.evidence.is_some());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_fail_closed_bundle_verifier_valid_request_returns_unsupported() {
    let result = FailClosedBundleVerifier.verify_bundle(request());

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.status.as_str(), "unsupported");
    assert_eq!(result.exit_code(), 2);
    assert!(!result.is_verified());
    assert_eq!(result.obligation_results.len(), 1);
    assert_eq!(result.obligation_results[0].status.as_str(), "unsupported");
    assert!(matches!(
        result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { .. }
    ));
}

#[test]
fn test_fail_closed_bundle_verifier_empty_bundle_is_invalid() {
    let request = VerifyBundleRequest::new(
        "bundle-empty",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    );

    let result = FailClosedBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert_eq!(result.exit_code(), 3);
    assert_eq!(result.obligation_results, vec![]);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligations"));
    assert_eq!(BundleDiagnosticSeverity::Invalid.as_str(), "invalid");
}

#[test]
fn test_bundle_result_all_verified_requires_complete_results() {
    let request = single_obligation_request(typed_obligation(
        "obl-1",
        BundleObligationKind::Postcondition,
        "x == x",
    ));
    let evidence = native_verified_evidence(&request);
    let result = VerifyBundleResult::from_obligation_results(
        request,
        vec![BundleObligationResult::verified("obl-1", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    assert!(result.is_verified());
}

#[test]
fn test_bundle_result_verified_without_checked_evidence_is_invalid() {
    let mut evidence = evidence();
    evidence.checked_by = None;

    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "proof_evidence"));
}

#[test]
fn test_bundle_result_verified_with_unchecked_strength_is_invalid() {
    let mut evidence = evidence();
    evidence.strength = ProofStrength::Unchecked;

    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "proof_evidence"));
    assert_eq!(ProofStrength::Unchecked.as_str(), "unchecked");
}

#[test]
fn test_bundle_result_verified_without_hash_addressed_artifact_is_invalid() {
    let mut evidence = evidence();
    evidence.artifacts.clear();

    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "proof_evidence"));
}

#[test]
fn test_bundle_result_verified_with_unstable_artifact_id_is_invalid() {
    let mut evidence = evidence();
    evidence.artifacts[0].id.push_str("-tampered");

    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "proof_evidence"));
}

#[test]
fn test_bundle_result_invalid_obligation_diagnostic_fails_closed() {
    let mut obligation_result = BundleObligationResult::verified("obl-1", evidence());
    obligation_result
        .diagnostics
        .push(BundleDiagnostic::invalid(
            "engine",
            "malformed proof artifact",
        ));

    let result =
        VerifyBundleResult::from_obligation_results(request(), vec![obligation_result], Vec::new());

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert_eq!(result.exit_code(), 3);
}

#[test]
fn test_bundle_result_unsupported_diagnostic_fails_closed() {
    let request = single_obligation_request(typed_obligation(
        "obl-1",
        BundleObligationKind::Postcondition,
        "x == x",
    ));
    let evidence = native_verified_evidence(&request);
    let result = VerifyBundleResult::from_obligation_results(
        request,
        vec![BundleObligationResult::verified("obl-1", evidence)],
        vec![BundleDiagnostic::unsupported(
            "engine",
            "unsupported claim fragment",
        )],
    );

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(!result.is_verified());
}

#[test]
fn test_bundle_result_missing_result_is_invalid() {
    let result = VerifyBundleResult::from_obligation_results(request(), Vec::new(), Vec::new());

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert_eq!(result.exit_code(), 3);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("missing result")));
}

#[test]
fn test_bundle_result_duplicate_result_is_invalid() {
    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![
            BundleObligationResult::verified("obl-1", evidence()),
            BundleObligationResult::verified("obl-1", evidence()),
        ],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("duplicate result")));
}

#[test]
fn test_bundle_result_failed_precedence_over_unknown() {
    let request = request().with_obligation(BundleObligation::new(
        "obl-2",
        BundleObligationKind::ArithmeticSafety,
        "demo::verified",
        claim(),
    ));

    let result = VerifyBundleResult::from_obligation_results(
        request,
        vec![
            BundleObligationResult::unknown("obl-1", "timeout"),
            BundleObligationResult::failed("obl-2", "counterexample"),
        ],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Failed);
    assert_eq!(result.exit_code(), 1);
}

#[test]
fn test_bundle_result_unknown_fails_closed() {
    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::unknown(
            "obl-1",
            "solver incomplete",
        )],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Unknown);
    assert_eq!(result.exit_code(), 2);
    assert!(!result.is_verified());
}

#[test]
fn test_request_validation_duplicate_obligation_id_is_invalid() {
    let request = request().with_obligation(obligation("obl-1"));
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("duplicate obligation id")));
}

#[test]
fn test_native_predicate_converter_parses_trust_wp_pure_expr_claim() {
    let predicate = native_predicate_for_obligation(&obligation("obl-parse")).unwrap();

    assert_eq!(predicate.obligation_id, "obl-parse");
    assert_eq!(predicate.claim_format, NativeClaimFormat::TrustWpPureExprV1);
    assert!(matches!(
        predicate.predicate,
        crate::formula::PureExpr::BinOp(_, crate::formula::BinOp::Gt, _)
    ));
}

#[test]
fn test_native_predicate_converter_decodes_trust_formula_v1_claim() {
    let predicate = native_predicate_for_obligation(&trust_formula_obligation(
        "obl-trust-formula-parse",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "result": {"sort": "int"},
            "body": {
                "op": "implies",
                "lhs": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}},
                "rhs": {
                    "op": "gt",
                    "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                    "rhs": {"int": 0}
                }
            }
        }"#,
    ))
    .unwrap();

    assert_eq!(predicate.obligation_id, "obl-trust-formula-parse");
    assert_eq!(predicate.claim_format, NativeClaimFormat::TrustFormulaV1);
    assert!(matches!(
        predicate.predicate,
        crate::formula::PureExpr::BinOp(_, crate::formula::BinOp::Implies, _)
    ));
}

#[test]
fn test_public_trust_formula_decoder_decodes_structural_payload() {
    let predicate = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "body": {"op": "eq", "lhs": {"var": "x"}, "rhs": {"var": "x"}}
        }"#,
    )
    .unwrap();

    assert!(matches!(
        predicate,
        crate::formula::PureExpr::BinOp(_, crate::formula::BinOp::Eq, _)
    ));
}

#[test]
fn test_public_trust_formula_decoder_rejects_duplicate_json_keys() {
    let duplicate_body = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "body": {"bool": false},
            "body": {"bool": true}
        }"#,
    )
    .expect_err("duplicate top-level proof fields must be rejected");
    assert!(
        duplicate_body
            .to_string()
            .contains("duplicate JSON object key `body`"),
        "{duplicate_body}"
    );

    let duplicate_operator = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "add",
                "op": "eq",
                "lhs": {"var": "x"},
                "rhs": {"var": "x"}
            }
        }"#,
    )
    .expect_err("duplicate nested proof operators must be rejected");
    assert!(
        duplicate_operator
            .to_string()
            .contains("duplicate JSON object key `op`"),
        "{duplicate_operator}"
    );
}

#[test]
fn test_public_trust_formula_decoder_decodes_scoped_let_payload() {
    let predicate = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "let",
                "name": "witness",
                "sort": "int",
                "value": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                "body": {"op": "gt", "lhs": {"var": "witness"}, "rhs": {"var": "x"}}
            }
        }"#,
    )
    .unwrap();

    assert!(matches!(predicate, crate::formula::PureExpr::Let { .. }));
}

#[test]
fn test_public_trust_formula_decoder_rejects_unguarded_division() {
    let err = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "numerator", "sort": "int"},
                {"name": "denominator", "sort": "int"}
            ],
            "result": {"sort": "int"},
            "body": {
                "op": "eq",
                "lhs": {"result": true},
                "rhs": {
                    "op": "div",
                    "lhs": {"var": "numerator"},
                    "rhs": {"var": "denominator"}
                }
            }
        }"#,
    )
    .unwrap_err();

    assert!(err.to_string().contains("divisor must"), "{err}");
}

#[test]
fn test_public_trust_formula_decoder_accepts_guarded_division() {
    let predicate = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "numerator", "sort": "int"},
                {"name": "denominator", "sort": "int"}
            ],
            "result": {"sort": "int"},
            "body": {
                "op": "and",
                "lhs": {"op": "ne", "lhs": {"var": "denominator"}, "rhs": {"int": 0}},
                "rhs": {
                    "op": "eq",
                    "lhs": {"result": true},
                    "rhs": {
                        "op": "div",
                        "lhs": {"var": "numerator"},
                        "rhs": {"var": "denominator"}
                    }
                }
            }
        }"#,
    )
    .unwrap();

    assert!(matches!(
        predicate,
        crate::formula::PureExpr::BinOp(_, crate::formula::BinOp::And, _)
    ));
}

#[test]
fn test_public_trust_formula_decoder_rejects_current_guard_for_old_division() {
    let err = decode_trust_formula_v1_claim(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "denominator", "sort": "int"}],
            "body": {
                "op": "implies",
                "lhs": {
                    "op": "ne",
                    "lhs": {"var": "denominator"},
                    "rhs": {"int": 0}
                },
                "rhs": {
                    "op": "eq",
                    "lhs": {
                        "old": {
                            "op": "div",
                            "lhs": {"int": 1},
                            "rhs": {"var": "denominator"}
                        }
                    },
                    "rhs": {
                        "old": {
                            "op": "div",
                            "lhs": {"int": 1},
                            "rhs": {"var": "denominator"}
                        }
                    }
                }
            }
        }"#,
    )
    .expect_err("a current-state guard cannot establish old-state definedness");

    assert!(err.to_string().contains("divisor must"), "{err}");
}

#[test]
fn test_public_trust_formula_decoder_rejects_source_text_payload() {
    let err = decode_trust_formula_v1_claim(r#""result > 0""#).unwrap_err();

    assert_eq!(err.to_string(), "claim payload must be a JSON object");
}

#[test]
fn test_request_validation_rejects_opaque_claim_formats_as_native_input() {
    let request = VerifyBundleRequest::new(
        "bundle-opaque",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    )
    .with_obligation(BundleObligation::new(
        "obl-opaque",
        BundleObligationKind::Postcondition,
        "demo::verified",
        BundleClaim::new(
            BundleClaimFormat::Other("application/x-opaque-claim".to_string()),
            r#"{"Bool":true}"#,
        ),
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.format"
            && diagnostic.message.contains("opaque claim format")
    }));
}

#[test]
fn test_request_validation_rejects_unsupported_trust_formula_v1_op() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-shl",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "eq",
                "lhs": {"op": "shl", "lhs": {"var": "x"}, "rhs": {"int": 2}},
                "rhs": {"int": 0}
            }
        }"#,
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic
                .message
                .contains("outside the trust-formula v1 native int/bool fragment")
    }));
}

#[test]
fn test_request_validation_rejects_undeclared_trust_formula_v1_variable() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-undeclared",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "body": {"op": "eq", "lhs": {"var": "x"}, "rhs": {"int": 0}}
        }"#,
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic
                .message
                .contains("references undeclared binding `x`")
    }));
}

#[test]
fn test_request_validation_rejects_ambiguous_trust_formula_v1_node() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-ambiguous",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "body": {"bool": true, "var": "x"}
        }"#,
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic
                .message
                .contains("contains unsupported field `var`")
    }));
}

#[test]
fn test_request_validation_rejects_trust_formula_v1_let_shadowing() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-let-shadow",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "let",
                "name": "x",
                "sort": "int",
                "value": {"int": 0},
                "body": {"op": "eq", "lhs": {"var": "x"}, "rhs": {"int": 0}}
            }
        }"#,
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic.message.contains("shadows existing binding `x`")
    }));
}

#[test]
fn test_bundle_result_verified_with_opaque_claim_fails_closed() {
    let request = VerifyBundleRequest::new(
        "bundle-opaque",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    )
    .with_obligation(BundleObligation::new(
        "obl-opaque",
        BundleObligationKind::Postcondition,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::SmtLib2, "(assert true)"),
    ));

    let result = VerifyBundleResult::from_obligation_results(
        request,
        vec![BundleObligationResult::verified("obl-opaque", evidence())],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.claim.format"));
}

#[test]
fn test_request_validation_rejects_unparsed_trust_wp_pure_expr_claim() {
    let request = VerifyBundleRequest::new(
        "bundle-bad-syntax",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    )
    .with_obligation(BundleObligation::new(
        "obl-bad-syntax",
        BundleObligationKind::Postcondition,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result >"),
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic.message.contains("invalid TrustWpPureExprV1")
    }));
}

#[test]
fn test_request_validation_rejects_non_boolean_trust_wp_pure_expr_claim() {
    let request = VerifyBundleRequest::new(
        "bundle-non-bool",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    )
    .with_obligation(BundleObligation::new(
        "obl-non-bool",
        BundleObligationKind::Postcondition,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result + 1"),
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic.message.contains("not a typed boolean predicate")
    }));
}

#[test]
fn test_request_validation_rejects_undefined_trust_wp_pure_expr_arithmetic() {
    for payload in [
        "1 / 0 == 1 / 0",
        "denominator != 0 ==> old(1 / denominator) == old(1 / denominator)",
    ] {
        let request = single_obligation_request(typed_obligation(
            "obl-undefined-pure-expr",
            BundleObligationKind::Postcondition,
            payload,
        ));
        let diagnostics = request.validation_diagnostics();

        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "obligation.claim.payload"
                    && diagnostic.message.contains("divisor must")
            }),
            "{payload}: {diagnostics:?}"
        );
    }
}

#[test]
fn test_request_validation_accepts_current_guard_for_current_division() {
    let request = single_obligation_request(typed_obligation(
        "obl-defined-pure-expr",
        BundleObligationKind::Postcondition,
        "denominator != 0 ==> 1 / denominator == 1 / denominator",
    ));

    assert_eq!(request.validation_diagnostics(), vec![]);
}

#[test]
fn test_request_validation_rejects_malformed_claim_digest() {
    let request = single_obligation_request(typed_obligation_with_claim_digest(
        "obl-bad-claim-digest",
        BundleObligationKind::Postcondition,
        "true",
        BundleDigest::new("", ""),
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.claim.digest"));
}

#[test]
fn test_request_validation_rejects_ill_typed_boolean_comparison() {
    let request = VerifyBundleRequest::new(
        "bundle-ill-typed",
        BundleProducer::new("tRust"),
        BundleTarget::new("demo"),
    )
    .with_obligation(BundleObligation::new(
        "obl-ill-typed",
        BundleObligationKind::Postcondition,
        "demo::verified",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true < false"),
    ));

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.claim.payload"
            && diagnostic.message.contains("not a typed boolean predicate")
    }));
}

#[test]
fn test_request_validation_accepts_typed_tmir_source_and_fact_metadata() {
    let obligation = typed_obligation(
        "obl-typed-tmir-metadata",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    )
    .with_tmir_source_span(BundleTmirSourceSpan::new(4, 29, 7))
    .with_native_verifier(
        BundleNativeToolIdentity::new("trust-wp")
            .with_version("native-schema-v2")
            .with_revision("6dfb614"),
    )
    .with_native_solver(
        BundleNativeToolIdentity::new("ay")
            .with_version("0.9.0")
            .with_revision("solver-rev"),
    )
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
            .with_function_id(2)
            .with_monomorphization_id(5)
            .with_compiler_fact_refs([
                BundleTmirCompilerFactRef::monomorphization(5),
                BundleTmirCompilerFactRef::cast(9),
            ]),
    );
    let request = single_obligation_request(obligation);

    assert_eq!(request.validation_diagnostics(), Vec::new());
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_request_validation_rejects_malformed_typed_tmir_metadata() {
    let obligation = typed_obligation(
        "obl-bad-tmir-metadata",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_native_verifier(BundleNativeToolIdentity::new(""))
    .with_native_solver(BundleNativeToolIdentity::new(""))
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Other(String::new()))
            .with_compiler_fact_refs([
                BundleTmirCompilerFactRef::monomorphization(7),
                BundleTmirCompilerFactRef::monomorphization(7),
                BundleTmirCompilerFactRef::cast(9).with_digest(BundleDigest::new("", "")),
                BundleTmirCompilerFactRef {
                    kind: BundleTmirCompilerFactKind::Other(String::new()),
                    id: 8,
                    digest: None,
                },
            ]),
    );
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.code == "obligation.metadata.native_verifier.name" }));
    assert!(diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.code == "obligation.metadata.native_solvers.name" }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.cause"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs.kind"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs.digest"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs"
    }));
}

#[test]
fn test_native_trust_wp_replay_rejects_tampered_compiler_fact_digest() {
    let obligation = typed_obligation(
        "obl-compiler-fact-digest",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    )
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
            .with_function_id(2)
            .with_monomorphization_id(5)
            .with_compiler_fact_refs([BundleTmirCompilerFactRef::monomorphization(5)
                .with_digest(BundleDigest::new("sha256", "a".repeat(64)))]),
    );
    let request = single_obligation_request(obligation);
    let evidence = native_verified_evidence(&request);
    let mut tampered_request = request.clone();
    tampered_request.obligations[0]
        .metadata
        .tmir_obligation_source
        .as_mut()
        .expect("test fixture has tMIR source metadata")
        .compiler_fact_refs[0]
        .digest = Some(BundleDigest::new("sha256", "b".repeat(64)));

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(
        err.message.contains("normalized-obligation"),
        "compiler fact drift should identify normalized metadata: {}",
        err.message
    );
    assert!(
        err.message.contains("tMIR metadata"),
        "compiler fact drift should describe the tMIR metadata scope: {}",
        err.message
    );
}

#[test]
fn test_native_trust_wp_replay_rejects_reordered_native_solvers() {
    let obligation = typed_obligation(
        "obl-native-solver-order",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    )
    .with_native_solvers([
        BundleNativeToolIdentity::new("ay")
            .with_version("0.9.0")
            .with_revision("solver-rev"),
        BundleNativeToolIdentity::new("proof-checker")
            .with_version("1.0.0")
            .with_revision("checker-rev"),
    ]);
    let request = single_obligation_request(obligation);
    let evidence = native_verified_evidence(&request);
    let mut tampered_request = request.clone();
    tampered_request.obligations[0]
        .metadata
        .native_solvers
        .swap(0, 1);

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(
        err.message.contains("normalized-obligation"),
        "native solver order drift should identify the normalized artifact: {}",
        err.message
    );
    assert!(
        err.message
            .contains("native replay/verifier/solver identities"),
        "native solver order drift should describe the solver identity scope: {}",
        err.message
    );
}

#[test]
fn test_request_validation_rejects_native_tmir_origin_without_obligation_source() {
    let obligation = typed_obligation(
        "obl-native-tmir-missing-source",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_native_origin(
        BundleNativeOrigin::new(
            "tmir.native-verification-bundle.v2",
            BundleNativeVerificationMode::WeakestPrecondition,
            7,
            2,
            0,
        )
        .with_tmir_module_digest(BundleDigest::new("sha256", "c".repeat(64))),
    );
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source"
            && diagnostic.message.contains("native tMIR origin metadata")
    }));
}

#[test]
fn test_request_validation_rejects_native_tmir_origin_without_source_span_or_toolchain() {
    let obligation = typed_obligation(
        "obl-native-tmir-missing-span-toolchain",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_native_origin(
        BundleNativeOrigin::new(
            "tmir.native-verification-bundle.v2",
            BundleNativeVerificationMode::WeakestPrecondition,
            7,
            2,
            0,
        )
        .with_lineage_roots([0])
        .with_tmir_module_digest(BundleDigest::new("sha256", "c".repeat(64))),
    )
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
            .with_function_id(2),
    );
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.metadata.tmir_source_span"));
    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.metadata.native_verifier"));
    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.metadata.native_solvers"));
    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.metadata.native_replay"));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_rejects_foreign_native_tmir_verifier_identity() {
    let mut obligation = native_tmir_origin_obligation("obl-native-tmir-foreign-verifier");
    obligation.metadata.native_verifier =
        Some(BundleNativeToolIdentity::new("trust-mc").with_version("chc-v1"));
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.native_verifier.name"
            && diagnostic.message.contains("trust-mc")
            && diagnostic.message.contains("trust-wp")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_rejects_placeholder_native_tmir_solver_identity() {
    let mut obligation = native_tmir_origin_obligation("obl-native-tmir-placeholder-solver");
    obligation.metadata.native_solvers = vec![BundleNativeToolIdentity::new("unknown")];
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.native_solvers"
            && diagnostic.message.contains("solver identity 0")
            && diagnostic.message.contains("empty placeholder")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_rejects_native_tmir_replay_atom_binding_drift() {
    let obligation = native_tmir_origin_obligation("obl-native-tmir-replay-atom-drift")
        .with_proof_context(BundleProofContext::new(
            vec![BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
            )
            .with_native_replay_atom_id(0)
            .with_native_obligation_id(99)],
            vec![BundleProofAtom::new(
                1,
                BundleProofAtomRole::Assertion,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result == result"),
            )
            .with_native_replay_atom_id(1)
            .with_native_obligation_id(99)
            .with_native_assertion_id(7)
            .with_native_span(BundleTmirSourceSpan::new(4, 30, 7))],
        ));
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.native_obligation_id"
            && diagnostic.message.contains("expected 0")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.native_assertion_id"
            && diagnostic.message.contains("assertion id 7")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.native_span"
            && diagnostic.message.contains("span")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_rejects_unbound_native_tmir_monomorphization_source() {
    let obligation = typed_obligation(
        "obl-native-tmir-unbound-mono",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_native_origin(
        BundleNativeOrigin::new(
            "tmir.native-verification-bundle.v2",
            BundleNativeVerificationMode::WeakestPrecondition,
            7,
            2,
            0,
        )
        .with_tmir_module_digest(BundleDigest::new("sha256", "c".repeat(64))),
    )
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
            .with_function_id(2)
            .with_monomorphization_id(5)
            .with_compiler_fact_refs([BundleTmirCompilerFactRef::monomorphization(5)]),
    );
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs"
            && diagnostic
                .message
                .contains("matching hash-addressed compiler fact ref")
    }));
}

#[test]
fn test_request_validation_rejects_unbound_native_tmir_compiler_fact_refs() {
    let obligation = typed_obligation(
        "obl-native-tmir-unbound-fact",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_native_origin(
        BundleNativeOrigin::new(
            "tmir.native-verification-bundle.v2",
            BundleNativeVerificationMode::WeakestPrecondition,
            7,
            2,
            0,
        )
        .with_tmir_module_digest(BundleDigest::new("sha256", "c".repeat(64))),
    )
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::CastCheck)
            .with_function_id(2)
            .with_compiler_fact_refs([BundleTmirCompilerFactRef::cast(9)]),
    );
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs"
            && diagnostic.message.contains("`cast`/9")
            && diagnostic
                .message
                .contains("hash-addressed compiler fact digest")
    }));
}

#[test]
fn test_request_validation_rejects_native_tmir_source_cause_kind_drift() {
    let obligation = typed_obligation(
        "obl-native-tmir-cause-kind-drift",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_native_origin(
        BundleNativeOrigin::new(
            "tmir.native-verification-bundle.v2",
            BundleNativeVerificationMode::WeakestPrecondition,
            7,
            2,
            0,
        )
        .with_lineage_roots([0])
        .with_tmir_module_digest(BundleDigest::new("sha256", "c".repeat(64))),
    )
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Precondition)
            .with_function_id(2),
    );
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.tmir_obligation_source.cause"
            && diagnostic.message.contains("precondition")
            && diagnostic.message.contains("postcondition")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_accepts_typed_proof_context_and_replay_binds_it() {
    let obligation = typed_obligation(
        "obl-typed-proof-context",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_proof_context(BundleProofContext::new(
        vec![BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assumption,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
        )],
        vec![BundleProofAtom::new(
            1,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result == result"),
        )],
    ));
    let request = single_obligation_request(obligation);

    assert_eq!(request.validation_diagnostics(), Vec::new());
    let evidence = native_verified_evidence(&request);

    let mut tampered_request = request.clone();
    tampered_request.obligations[0]
        .metadata
        .proof_context
        .assertions[0]
        .claim
        .payload = "false".to_string();
    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(err.message.contains("proof context"));
}

#[test]
fn test_request_validation_rejects_ambiguous_or_ill_typed_proof_context() {
    let obligation = typed_obligation(
        "obl-bad-proof-context",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_proof_context(BundleProofContext::new(
        vec![
            BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
            ),
            BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true < false"),
            ),
        ],
        Vec::new(),
    ));
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.metadata.proof_context.index"));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.claim.payload"
            && diagnostic
                .message
                .contains("typed boolean native proof claim")
    }));
}

#[test]
fn test_request_validation_rejects_cross_role_proof_context_index_reuse() {
    let obligation = typed_obligation(
        "obl-cross-role-proof-context-index",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_proof_context(BundleProofContext::new(
        vec![BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assumption,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
        )],
        vec![BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result == result"),
        )],
    ));
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.index"
            && diagnostic
                .message
                .contains("unique across assumptions and assertions")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_rejects_sparse_proof_context_indexes() {
    let obligation = typed_obligation(
        "obl-sparse-proof-context-indexes",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_proof_context(BundleProofContext::new(
        vec![BundleProofAtom::new(
            1,
            BundleProofAtomRole::Assumption,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
        )],
        vec![BundleProofAtom::new(
            3,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result == result"),
        )],
    ));
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.index"
            && diagnostic.message.contains("not canonical")
            && diagnostic.message.contains("expected contiguous index 0")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.index"
            && diagnostic.message.contains("expected contiguous index 1")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_request_validation_rejects_out_of_order_proof_context_indexes() {
    let obligation = typed_obligation(
        "obl-out-of-order-proof-context-indexes",
        BundleObligationKind::Postcondition,
        "true",
    )
    .with_proof_context(BundleProofContext::new(
        vec![
            BundleProofAtom::new(
                1,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
            ),
            BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "result == result"),
            ),
        ],
        Vec::new(),
    ));
    let request = single_obligation_request(obligation);
    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.index"
            && diagnostic
                .message
                .contains("assumption atom index 1 is not canonical")
            && diagnostic.message.contains("expected contiguous index 0")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.metadata.proof_context.index"
            && diagnostic
                .message
                .contains("assumption atom index 0 is not canonical")
            && diagnostic.message.contains("expected contiguous index 1")
    }));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    assert_eq!(result.status, VerifyBundleStatus::Invalid);
}

#[test]
fn test_proof_context_exposes_canonical_identity() {
    let context = BundleProofContext::new(
        vec![BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assumption,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x >= 0"),
        )],
        vec![BundleProofAtom::new(
            1,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x + 1 > 0"),
        )],
    );
    let digest = context
        .canonical_digest()
        .expect("non-empty proof context has an identity");
    let identity = context
        .canonical_identity()
        .expect("non-empty proof context has a stable identity");

    assert!(digest.is_hash_addressed());
    assert!(identity.contains("trust-wp.proof-evidence.v1/proof-context/sha256/"));
    assert_eq!(
        context.canonical_digest(),
        context.clone().canonical_digest()
    );
    let native_context = BundleProofContext::new(
        vec![BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assumption,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x >= 0"),
        )
        .with_native_replay_atom_id(7)
        .with_native_obligation_id(3)],
        vec![BundleProofAtom::new(
            1,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x + 1 > 0"),
        )
        .with_native_replay_atom_id(8)
        .with_native_obligation_id(3)
        .with_native_assertion_id(2)],
    );
    assert_ne!(
        context.canonical_digest(),
        native_context.canonical_digest(),
        "native replay atom bindings participate in proof-context identity"
    );

    let empty = BundleProofContext::default();
    assert_eq!(empty.canonical_digest(), None);
    assert_eq!(empty.canonical_identity(), None);
}

#[test]
fn test_verified_bundle_result_carries_aggregate_replay_evidence() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-aggregate-proof",
            BundleObligationKind::Postcondition,
            "x >= 0 ==> x + 1 > 0",
        )
        .with_proof_context(BundleProofContext::new(
            vec![BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x >= 0"),
            )],
            vec![BundleProofAtom::new(
                1,
                BundleProofAtomRole::Assertion,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x + 1 > 0"),
            )],
        )),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert!(result.is_verified());
    let aggregate = result
        .aggregate_evidence
        .as_ref()
        .expect("verified result carries aggregate evidence");
    assert_eq!(
        aggregate.format,
        ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1
    );
    assert!(aggregate.is_proof_grade());
    assert!(aggregate.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::AggregateProofManifest
            && artifact.has_stable_identity()
    }));
    replay_verify_bundle_result_evidence(&request, &result).unwrap();
}

#[test]
fn test_verified_bundle_result_without_aggregate_evidence_fails_closed() {
    let request = single_obligation_request(typed_obligation(
        "obl-missing-aggregate-proof",
        BundleObligationKind::Postcondition,
        "true",
    ));
    let mut result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    result.aggregate_evidence = None;

    assert!(!result.is_verified());
    let err = replay_verify_bundle_result_evidence(&request, &result).unwrap_err();
    assert_eq!(err.code, "proof_replay.aggregate_evidence");
}

/// tRust #1152/#1157: a verified aggregate replay must not accept a result
/// with per-obligation fail-closed diagnostics attached after evidence was
/// generated.
#[test]
fn test_verified_bundle_result_with_obligation_invalid_diagnostic_fails_closed() {
    let request = single_obligation_request(typed_obligation(
        "obl-diagnostic-drift",
        BundleObligationKind::Postcondition,
        "true",
    ));
    let mut result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert!(result.is_verified());

    result.obligation_results[0]
        .diagnostics
        .push(BundleDiagnostic::invalid(
            "proof_evidence.replay",
            "injected replay rejection",
        ));

    assert!(!result.is_verified());
    let err = replay_verify_bundle_result_evidence(&request, &result).unwrap_err();
    assert_eq!(err.code, "proof_replay.aggregate_obligation_diagnostics");
}

#[test]
fn test_aggregate_replay_rejects_tampered_proof_context_identity() {
    let context = BundleProofContext::new(
        vec![BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assumption,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x >= 0"),
        )],
        vec![BundleProofAtom::new(
            1,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x + 1 > 0"),
        )],
    );
    let request = single_obligation_request(
        typed_obligation(
            "obl-proof-context-aggregate-drift",
            BundleObligationKind::Postcondition,
            "x >= 0 ==> x + 1 > 0",
        )
        .with_proof_context(context),
    );
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    let mut tampered_request = request.clone();
    tampered_request.obligations[0]
        .metadata
        .proof_context
        .assertions[0]
        .claim
        .payload = "x + 2 > 0".to_string();

    let err = replay_verify_bundle_result_evidence(&tampered_request, &result).unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(err.message.contains("proof context"));
}

#[test]
fn test_native_trust_wp_verifier_proves_typed_postcondition_with_replay_evidence() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    let result_again = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    let BundleObligationStatus::Verified {
        evidence: evidence_again,
    } = &result_again.obligation_results[0].status
    else {
        panic!("expected verified obligation");
    };

    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert_eq!(evidence.strength, ProofStrength::Sound);
    assert!(evidence.is_proof_grade());
    assert_eq!(evidence.schema_version, PROOF_EVIDENCE_SCHEMA_VERSION);
    assert_eq!(evidence.digest, evidence_again.digest);
    assert_eq!(evidence.to_stable_wire(), evidence_again.to_stable_wire());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
    assert!(evidence.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::RequestDigest
            && artifact.kind.as_str() == "request-digest"
            && artifact.has_stable_identity()
    }));
    assert!(evidence.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::NormalizedObligation
            && artifact.kind.as_str() == "normalized-obligation"
            && artifact.has_stable_identity()
    }));
    assert!(evidence.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::ReplayLog
            && artifact.kind.as_str() == "replay-log"
            && artifact.has_stable_identity()
    }));
    assert!(evidence.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::SolverTranscript
            && artifact.kind.as_str() == "solver-transcript"
            && artifact.has_stable_identity()
            && artifact
                .inline_bytes
                .as_ref()
                .is_some_and(|bytes| bytes.data.contains("actual-digest=sha256:"))
    }));
    assert!(
        evidence
            .artifacts
            .iter()
            .all(|artifact| artifact.has_transport() && artifact.inline_bytes_digest_matches()),
        "native trust-wp evidence should expose digest-checked transport bytes"
    );
}

#[test]
fn test_inline_artifact_bytes_are_digest_checked_for_proof_grade_evidence() {
    let mut evidence = evidence();
    evidence.artifacts[0] = EvidenceArtifact::new(
        EvidenceArtifactKind::ProofCertificate,
        BundleDigest::new("sha256", "bad-digest"),
        "tampered proof certificate",
    )
    .with_utf8_bytes("proof certificate bytes");

    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "proof_evidence"));
}

#[test]
fn test_native_trust_wp_verifier_proves_simple_linear_implication_postcondition() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-implication",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 1 > 0",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert_eq!(evidence.strength, ProofStrength::Sound);
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_trust_formula_v1_result_postcondition() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-result-post",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "result": {"sort": "int"},
            "body": {
                "op": "implies",
                "lhs": {"op": "ge", "lhs": {"result": true}, "rhs": {"int": 0}},
                "rhs": {
                    "op": "gt",
                    "lhs": {"op": "add", "lhs": {"result": true}, "rhs": {"int": 1}},
                    "rhs": {"int": 0}
                }
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_trust_formula_v1_variable_precondition() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-variable-pre",
        BundleObligationKind::Precondition {
            callee: "demo::callee".to_string(),
        },
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "x", "sort": "int"},
                {"name": "flag", "sort": "bool"}
            ],
            "body": {
                "op": "and",
                "lhs": {"op": "eq", "lhs": {"var": "x"}, "rhs": {"var": "x"}},
                "rhs": {"op": "implies", "lhs": {"var": "flag"}, "rhs": {"var": "flag"}}
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_trust_formula_v1_nonnegative_division() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-nonnegative-div",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "numerator", "sort": "int"},
                {"name": "denominator", "sort": "int"}
            ],
            "result": {"sort": "int"},
            "body": {
                "op": "implies",
                "lhs": {
                    "op": "and",
                    "lhs": {
                        "op": "and",
                        "lhs": {"op": "ge", "lhs": {"var": "numerator"}, "rhs": {"int": 0}},
                        "rhs": {"op": "gt", "lhs": {"var": "denominator"}, "rhs": {"int": 0}}
                    },
                    "rhs": {
                        "op": "eq",
                        "lhs": {"result": true},
                        "rhs": {
                            "op": "div",
                            "lhs": {"var": "numerator"},
                            "rhs": {"var": "denominator"}
                        }
                    }
                },
                "rhs": {"op": "ge", "lhs": {"result": true}, "rhs": {"int": 0}}
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_trust_formula_v1_nonnegative_modulo() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-nonnegative-mod",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "value", "sort": "int"},
                {"name": "divisor", "sort": "int"}
            ],
            "body": {
                "op": "implies",
                "lhs": {
                    "op": "and",
                    "lhs": {"op": "ge", "lhs": {"var": "value"}, "rhs": {"int": 0}},
                    "rhs": {"op": "gt", "lhs": {"var": "divisor"}, "rhs": {"int": 0}}
                },
                "rhs": {
                    "op": "ge",
                    "lhs": {
                        "op": "mod",
                        "lhs": {"var": "value"},
                        "rhs": {"var": "divisor"}
                    },
                    "rhs": {"int": 0}
                }
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_trust_formula_v1_midpoint_no_underflow_shape() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-midpoint-no-underflow",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "low", "sort": "int"},
                {"name": "high", "sort": "int"}
            ],
            "body": {
                "op": "implies",
                "lhs": {"op": "le", "lhs": {"var": "low"}, "rhs": {"var": "high"}},
                "rhs": {
                    "op": "ge",
                    "lhs": {
                        "op": "add",
                        "lhs": {"var": "low"},
                        "rhs": {
                            "op": "div",
                            "lhs": {
                                "op": "sub",
                                "lhs": {"var": "high"},
                                "rhs": {"var": "low"}
                            },
                            "rhs": {"int": 2}
                        }
                    },
                    "rhs": {"var": "low"}
                }
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_trust_formula_v1_let_alias_postcondition() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-let-alias",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "result": {"sort": "int"},
            "body": {
                "op": "let",
                "name": "ret",
                "sort": "int",
                "value": {"result": true},
                "body": {
                    "op": "implies",
                    "lhs": {"op": "ge", "lhs": {"result": true}, "rhs": {"int": 0}},
                    "rhs": {"op": "ge", "lhs": {"var": "ret"}, "rhs": {"int": 0}}
                }
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_conjunctive_requires_linear_postcondition() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-conjunctive-requires",
        BundleObligationKind::Postcondition,
        "x >= 0 && y >= 0 ==> x + 1 > 0",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_projects_conjunctive_typed_assumption() {
    let request = single_obligation_request(typed_obligation(
        "obl-assumption-projection",
        BundleObligationKind::Postcondition,
        "x >= 0 && y == x ==> 0 <= x && x == y",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_projects_trust_formula_v1_assumption() {
    let request = single_obligation_request(trust_formula_obligation(
        "obl-trust-formula-assumption-projection",
        BundleObligationKind::Postcondition,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [
                {"name": "x", "sort": "int"},
                {"name": "y", "sort": "int"}
            ],
            "body": {
                "op": "implies",
                "lhs": {
                    "op": "and",
                    "lhs": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}},
                    "rhs": {"op": "eq", "lhs": {"var": "y"}, "rhs": {"var": "x"}}
                },
                "rhs": {
                    "op": "and",
                    "lhs": {"op": "le", "lhs": {"int": 0}, "rhs": {"var": "x"}},
                    "rhs": {"op": "eq", "lhs": {"var": "x"}, "rhs": {"var": "y"}}
                }
            }
        }"#,
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_constant_scaled_linear_implication() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-constant-scale",
        BundleObligationKind::Postcondition,
        "x >= 1 ==> 2 * x >= 2",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_upper_bound_linear_implication() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-upper-bound",
        BundleObligationKind::Postcondition,
        "x <= 10 ==> x + 1 <= 11",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_checked_bitwise_identity_facts() {
    let request = single_obligation_request(typed_obligation(
        "obl-checked-bitwise-identities",
        BundleObligationKind::Postcondition,
        "~0 == -1 && x & 0 == 0 && x | 0 == x && x ^ x == 0 && x << 0 == x",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_proves_checked_bitwise_constant_facts() {
    let request = single_obligation_request(typed_obligation(
        "obl-checked-bitwise-constants",
        BundleObligationKind::Postcondition,
        "1 & 3 == 1 && 1 | 2 == 3 && 7 ^ 3 == 4 && 1 << 3 == 8 && 8 >> 1 == 4",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_keeps_invalid_bitwise_shift_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-invalid-bitwise-shift",
        BundleObligationKind::Postcondition,
        "1 << 64 == 0",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("bitwise shift count")
    ));
}

#[test]
fn test_native_trust_wp_verifier_keeps_symbolic_bitwise_shift_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-symbolic-bitwise-shift",
        BundleObligationKind::Postcondition,
        "x << k == x << k",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("bitwise shift count")
    ));
}

#[test]
fn test_native_trust_wp_verifier_proves_reflexive_pointer_equality() {
    let request = single_obligation_request(typed_obligation(
        "obl-reflexive-pointer-equality",
        BundleObligationKind::Postcondition,
        "forall<p: &T> p == p",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_keeps_nonreflexive_pointer_equality_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-nonreflexive-pointer-equality",
        BundleObligationKind::Postcondition,
        "forall<p: &T, q: &T> p == q",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("pointer replay requires alias/provenance")
    ));
}

#[test]
fn test_native_trust_wp_verifier_keeps_fat_pointer_metadata_equality_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-fat-pointer-metadata-equality",
        BundleObligationKind::Postcondition,
        "forall<p: &[T], q: &[T]> p == q",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("fat-pointer metadata replay")
    ));
}

#[test]
fn test_native_trust_wp_verifier_uses_pointer_summary_evidence_for_equality() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-pointer-summary-equality",
            BundleObligationKind::Postcondition,
            "forall<p: &T, q: &T> p == q",
        )
        .with_summary_fact(pointer_summary_fact("summary-pointer-p-q", "p", "q")),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    assert!(evidence
        .artifacts
        .iter()
        .any(|artifact| artifact.kind == EvidenceArtifactKind::SummaryEvidence));
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_uses_typed_pointer_binding_summary_for_equality() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-pointer-binding-summary-equality",
            BundleObligationKind::Postcondition,
            "forall<p: &T, q: &T> p == q",
        )
        .with_summary_fact(pointer_binding_summary_fact(
            "summary-binding-p-q",
            "p",
            "q",
        )),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_uses_typed_pointer_disjoint_summary_for_neq() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-pointer-binding-summary-disjoint",
            BundleObligationKind::Postcondition,
            "forall<p: &T, q: &T> p != q",
        )
        .with_summary_fact(pointer_disjoint_binding_summary_fact(
            "summary-disjoint-p-q",
            "p",
            "q",
        )),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_uses_fat_pointer_summary_evidence_for_equality() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-fat-pointer-summary-equality",
            BundleObligationKind::Postcondition,
            "forall<p: &[T], q: &[T]> p == q",
        )
        .with_summary_fact(fat_pointer_summary_fact("summary-fat-p-q", "p", "q")),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_uses_typed_fat_pointer_disjoint_summary_for_neq() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-fat-pointer-binding-summary-disjoint",
            BundleObligationKind::Postcondition,
            "forall<p: &[T], q: &[T]> p != q",
        )
        .with_summary_fact(fat_pointer_disjoint_binding_summary_fact(
            "summary-fat-disjoint-p-q",
            "p",
            "q",
        )),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_rejects_wrong_pointer_summary_kind() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-fat-pointer-wrong-summary-kind",
            BundleObligationKind::Postcondition,
            "forall<p: &[T], q: &[T]> p == q",
        )
        .with_summary_fact(pointer_summary_fact("summary-thin-for-fat-p-q", "p", "q")),
    );

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("fat-pointer metadata replay")
    ));
}

#[test]
fn test_native_trust_wp_replay_rejects_tampered_summary_evidence_digest() {
    let obligation = typed_obligation(
        "obl-pointer-summary-equality",
        BundleObligationKind::Postcondition,
        "forall<p: &T, q: &T> p == q",
    )
    .with_summary_fact(pointer_summary_fact("summary-pointer-p-q", "p", "q"));
    let request = single_obligation_request(obligation.clone());
    let evidence = native_verified_evidence(&request);

    let mut tampered_obligation = obligation;
    tampered_obligation.summary_facts[0].digest = summary_digest("tampered");
    let tampered_request = single_obligation_request(tampered_obligation);

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
}

#[test]
fn test_request_validation_rejects_malformed_summary_evidence() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-bad-summary",
            BundleObligationKind::Postcondition,
            "forall<p: &T, q: &T> p == q",
        )
        .with_summary_fact(BundleSummaryFact::new(
            "summary-bad",
            "",
            "dep_crate",
            "dep_crate::summary_source",
            BundleSummaryFactKind::PointerProvenanceEq {
                left: "p".to_string(),
                right: "q".to_string(),
            },
            BundleDigest::new("", ""),
        )),
    );

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.summary_facts.producer"));
    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.summary_facts.digest"));
}

#[test]
fn test_request_validation_rejects_malformed_typed_summary_binding() {
    let request = single_obligation_request(
        typed_obligation(
            "obl-bad-summary-binding",
            BundleObligationKind::Postcondition,
            "forall<p: &T, q: &T> p == q",
        )
        .with_summary_fact(pointer_binding_summary_fact(
            "summary-bad-binding",
            "p.left",
            "q",
        )),
    );

    let diagnostics = request.validation_diagnostics();

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "obligation.summary_facts.binding"
            && diagnostic.message.contains("p.left")
    }));
}

#[test]
fn test_native_trust_wp_verifier_refutes_nonlinear_symbolic_product() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-nonlinear-product",
        BundleObligationKind::Postcondition,
        "x >= 1 ==> x * y >= 1",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Failed);
    assert_eq!(result.exit_code(), 1);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Failed { reason }
            if reason.contains("checked whole-predicate counterexample")
                && reason.contains("x=1")
                && reason.contains("y=0")
    ));
}

#[test]
fn test_native_trust_wp_verifier_proves_compiler_lowered_result_alias_ensures_fact() {
    let request = single_obligation_request(typed_obligation(
        "obl-result-alias-ensures",
        BundleObligationKind::Postcondition,
        "{ let ret = result; result >= 0 ==> ret >= 0 }",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert_eq!(result.exit_code(), 0);
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("expected verified obligation");
    };
    assert_eq!(
        evidence.format,
        ProofEvidenceFormat::TrustWpNativePureReplayV1
    );
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
}

#[test]
fn test_native_trust_wp_verifier_refutes_false_result_alias() {
    let request = single_obligation_request(typed_obligation(
        "obl-result-alias-unproved",
        BundleObligationKind::Postcondition,
        "{ let ret = result; result >= 0 ==> ret > 0 }",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Failed);
    assert_eq!(result.exit_code(), 1);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Failed { reason }
            if reason.contains("checked whole-predicate counterexample")
                && reason.contains("result=0")
    ));
}

#[test]
fn test_native_trust_wp_replay_rejects_tampered_linear_postcondition_payload() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-implication",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 1 > 0",
    ));
    let evidence = native_verified_evidence(&request);
    let tampered_request = single_obligation_request(typed_obligation(
        "obl-linear-implication",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 2 > 0",
    ));

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
}

/// tRust #1040/#1043/#1063: native Requires/Ensures evidence must bind the
/// compiler-owned claim digest, not only the parsed predicate facade.
#[test]
fn test_native_trust_wp_replay_rejects_tampered_claim_digest() {
    let request = single_obligation_request(typed_obligation_with_claim_digest(
        "obl-linear-claim-digest",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 1 > 0",
        BundleDigest::new("sha256", "a".repeat(64)),
    ));
    let evidence = native_verified_evidence(&request);
    let tampered_request = single_obligation_request(typed_obligation_with_claim_digest(
        "obl-linear-claim-digest",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 1 > 0",
        BundleDigest::new("sha256", "b".repeat(64)),
    ));

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
}

/// tRust #1040/#1043/#1063: replay evidence is scoped to the typed bundle
/// envelope so a matching predicate cannot be replayed under a different target.
#[test]
fn test_native_trust_wp_replay_rejects_tampered_target_metadata() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-target-metadata",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 1 > 0",
    ));
    let evidence = native_verified_evidence(&request);
    let mut tampered_request = request.clone();
    tampered_request.target = BundleTarget::new("different_demo");

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
}

/// tRust #2753: replay evidence must bind the full request envelope, including
/// verification options that are outside the normalized predicate payload.
#[test]
fn test_native_trust_wp_replay_rejects_tampered_request_options() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-request-options",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x + 1 > 0",
    ));
    let evidence = native_verified_evidence(&request);
    let mut tampered_request = request.clone();
    tampered_request.options.timeout_ms = Some(1);

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(
        err.message.contains("request-digest"),
        "request envelope mismatch should identify the changed artifact: {}",
        err.message
    );
}

/// Re: #2754. Replay diagnostics should expose artifact-level drift instead
/// of only reporting a generic canonical-evidence mismatch.
#[test]
fn test_native_trust_wp_replay_mismatch_diagnostic_lists_summary_artifact() {
    let obligation = typed_obligation(
        "obl-pointer-summary-equality",
        BundleObligationKind::Postcondition,
        "forall<p: &T, q: &T> p == q",
    )
    .with_summary_fact(pointer_summary_fact("summary-pointer-p-q", "p", "q"));
    let request = single_obligation_request(obligation.clone());
    let evidence = native_verified_evidence(&request);

    let mut tampered_obligation = obligation;
    tampered_obligation.summary_facts[0].digest = summary_digest("tampered");
    let tampered_request = single_obligation_request(tampered_obligation);

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(
        err.message.contains("summary-evidence"),
        "summary mismatch should identify the changed artifact: {}",
        err.message
    );
}

/// Re: #2754. Typed replay drift should tell native adapters when the
/// normalized-obligation artifact is the one binding changed tMIR metadata.
#[test]
fn test_native_trust_wp_replay_mismatch_diagnostic_names_tmir_metadata_scope() {
    let obligation = typed_obligation(
        "obl-tmir-metadata-drift",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    )
    .with_tmir_source_span(BundleTmirSourceSpan::new(4, 29, 7))
    .with_native_verifier(
        BundleNativeToolIdentity::new("trust-wp")
            .with_version("native-schema-v2")
            .with_revision("6dfb614"),
    )
    .with_native_solver(BundleNativeToolIdentity::new("ay").with_version("0.9.0"))
    .with_tmir_obligation_source(
        BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
            .with_function_id(2)
            .with_compiler_fact_refs([BundleTmirCompilerFactRef::monomorphization(5)]),
    );
    let request = single_obligation_request(obligation.clone());
    let evidence = native_verified_evidence(&request);

    let tampered_obligation = obligation.with_tmir_source_span(BundleTmirSourceSpan::new(4, 30, 7));
    let tampered_request = single_obligation_request(tampered_obligation);

    let err = replay_native_pure_evidence(
        &tampered_request,
        &tampered_request.obligations[0],
        &evidence,
    )
    .unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
    assert!(
        err.message.contains("normalized-obligation"),
        "tMIR metadata drift should identify the normalized artifact: {}",
        err.message
    );
    assert!(
        err.message.contains("tMIR metadata"),
        "tMIR metadata drift should describe the artifact scope: {}",
        err.message
    );
}

#[test]
fn test_native_trust_wp_verifier_leaves_disjunctive_requires_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-disjunctive-requires",
        BundleObligationKind::Postcondition,
        "x >= 0 || y >= 0 ==> x + 1 > 0",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert_eq!(result.exit_code(), 2);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("cannot prove or refute")
    ));
}

#[test]
fn test_native_trust_wp_verifier_refutes_false_linear_implication() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-unproved",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x - 1 >= 0",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Failed);
    assert_eq!(result.exit_code(), 1);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Failed { reason }
            if reason.contains("checked whole-predicate counterexample")
                && reason.contains("x=0")
    ));
}

#[test]
fn test_native_trust_wp_replay_evidence_serialization_is_stable() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let evidence = native_verified_evidence(&request);
    let wire = evidence.to_stable_wire();
    let parsed = ProofEvidence::from_stable_wire(&wire).unwrap();

    assert!(wire.starts_with("TRUST_WP_PROOF_EVIDENCE:v1\n"));
    assert!(wire.ends_with('\n'));
    assert!(wire.contains("format=trust_wp.native-pure-replay.v1\n"));
    assert!(wire.contains("strength=sound\n"));
    assert!(wire.contains("digest.algorithm=736861323536\n"));
    assert!(wire.contains("artifact.0.digest.algorithm=736861323536\n"));
    assert!(wire.contains("artifact.1.digest.algorithm=736861323536\n"));
    assert_eq!(parsed.schema_version, evidence.schema_version);
    assert_eq!(parsed.producer, evidence.producer);
    assert_eq!(parsed.format, evidence.format);
    assert_eq!(parsed.strength, evidence.strength);
    assert_eq!(parsed.digest, evidence.digest);
    assert_eq!(parsed.artifacts.len(), evidence.artifacts.len());
    assert!(parsed
        .artifacts
        .iter()
        .all(|artifact| !artifact.has_transport()));
    assert_eq!(parsed.to_stable_wire(), wire);
    replay_native_pure_evidence(&request, &request.obligations[0], &parsed).unwrap();
}

#[test]
fn test_native_trust_wp_replay_evidence_wire_parser_rejects_extra_fields() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let evidence = native_verified_evidence(&request);
    let mut wire = evidence.to_stable_wire();
    wire.push_str("extra=field\n");

    let err = ProofEvidence::from_stable_wire(&wire).unwrap_err();

    assert_eq!(err.code, "proof_evidence_wire.unknown_field");
}

#[test]
fn test_native_trust_wp_replay_evidence_wire_parser_rejects_malformed_hex() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let evidence = native_verified_evidence(&request);
    // The wire encodes schema_version as hex bytes of "trust-wp.proof-evidence.v1".
    // First three chars `tru` = 0x74 0x72 0x75 → "747275". Replace the leading
    // hex pair with an invalid hex digit "zz" so the parser raises a hex error.
    let wire = evidence
        .to_stable_wire()
        .replace("schema_version=747275", "schema_version=zz7275");

    let err = ProofEvidence::from_stable_wire(&wire).unwrap_err();

    assert_eq!(err.code, "proof_evidence_wire.hex");
}

#[test]
fn test_native_trust_wp_replay_rejects_missing_artifact() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let mut evidence = native_verified_evidence(&request);
    evidence.artifacts.remove(0);

    let err =
        replay_native_pure_evidence(&request, &request.obligations[0], &evidence).unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
}

/// tRust #1040/#1043: aggregation must check native replay evidence, not only
/// proof-grade envelope shape, before reporting a Requires/Ensures proof.
#[test]
fn test_bundle_result_rejects_tampered_native_replay_evidence() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let mut evidence = native_verified_evidence(&request);
    evidence.artifacts.remove(0);

    let result = VerifyBundleResult::from_obligation_results(
        request,
        vec![BundleObligationResult::verified("obl-post-true", evidence)],
        Vec::new(),
    );

    assert_eq!(result.status, VerifyBundleStatus::Invalid);
    assert_eq!(result.exit_code(), 3);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "proof_evidence.replay"));
}

#[test]
fn test_native_trust_wp_replay_rejects_reordered_artifacts() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let mut evidence = native_verified_evidence(&request);
    evidence.artifacts.swap(0, 1);

    let err =
        replay_native_pure_evidence(&request, &request.obligations[0], &evidence).unwrap_err();

    assert_eq!(err.code, "proof_replay.mismatch");
}

#[test]
fn test_native_trust_wp_replay_rejects_false_predicate_even_with_valid_evidence_shape() {
    let true_request = single_obligation_request(typed_obligation(
        "obl-post-true",
        BundleObligationKind::Postcondition,
        "1 + 1 == 2",
    ));
    let evidence = native_verified_evidence(&true_request);
    let false_request = single_obligation_request(typed_obligation(
        "obl-post-false",
        BundleObligationKind::Postcondition,
        "1 + 1 == 3",
    ));

    let err = replay_native_pure_evidence(&false_request, &false_request.obligations[0], &evidence)
        .unwrap_err();

    assert_eq!(err.code, "proof_replay.result");
    assert!(err.message.contains("does not replay to verified"));
}

#[test]
fn test_native_trust_wp_verifier_rejects_false_typed_postcondition() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-false",
        BundleObligationKind::Postcondition,
        "1 + 1 == 3",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Failed);
    assert_eq!(result.exit_code(), 1);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Failed { reason }
            if reason.contains("typed predicate is false")
    ));
}

#[test]
fn test_native_trust_wp_verifier_proves_typed_precondition_reflexivity() {
    let request = single_obligation_request(typed_obligation(
        "obl-pre-true",
        BundleObligationKind::Precondition {
            callee: "demo::callee".to_string(),
        },
        "x == x",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert!(result.is_verified());
}

#[test]
fn test_native_trust_wp_verifier_refutes_unconstrained_symbolic_postcondition() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-unknown",
        BundleObligationKind::Postcondition,
        "result > x",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Failed);
    assert_eq!(result.exit_code(), 1);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Failed { reason }
            if reason.contains("checked whole-predicate counterexample")
                && reason.contains("result=0")
                && reason.contains("x=0")
    ));
}

#[test]
fn test_native_trust_wp_verifier_rejects_non_trust_wp_obligation_kind() {
    let request = single_obligation_request(typed_obligation(
        "obl-arithmetic",
        BundleObligationKind::ArithmeticSafety,
        "true",
    ));

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);

    assert_eq!(result.status, VerifyBundleStatus::Unsupported);
    assert!(matches!(
        &result.obligation_results[0].status,
        BundleObligationStatus::Unsupported { reason }
            if reason.contains("does not own")
    ));
}

/// A claim's decoded predicate is its goal whatever its shape. Every claim
/// here is false at some integer, and each verified while a top-level `!` or a
/// negated conjunct was rewritten into the positive goal it negates.
#[test]
fn test_native_negated_claim_is_proved_as_written() {
    for payload in [
        "!true",
        "!(x + 1 > x)",
        "x >= 0 && !(x + 1 > x)",
        "x >= 0 && !(x >= 0)",
        "!(old(m) == old(m))",
    ] {
        for kind in [
            BundleObligationKind::Postcondition,
            BundleObligationKind::Precondition {
                callee: "demo::verified".to_string(),
            },
            BundleObligationKind::LoopInvariant,
        ] {
            let obligation = typed_obligation("negated", kind.clone(), payload);
            let expected = crate::contract_parser::parse_contract(payload).expect("payload parses");
            assert_eq!(
                native_predicate_for_obligation(&obligation)
                    .expect("negated claim decodes")
                    .predicate,
                expected,
                "`{payload}` is proved as written"
            );
            let result =
                NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(obligation));
            assert_ne!(
                result.status,
                VerifyBundleStatus::Verified,
                "`{payload}` ({kind:?}) is false at some integer and must not verify"
            );
            assert_ne!(result.exit_code(), 0, "`{payload}` ({kind:?})");
        }
    }

    // The same convention proves a valid negation, which the rewrite refuted.
    for payload in ["!false", "!(x > x)", "!(x + 1 > x) ==> false"] {
        let result =
            NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(typed_obligation(
                "negated-valid",
                BundleObligationKind::Postcondition,
                payload,
            )));
        assert_eq!(
            result.status,
            VerifyBundleStatus::Verified,
            "`{payload}` is valid"
        );
    }
}

/// The same over a trust-formula payload, where `not` is an explicit node.
#[test]
fn test_native_negated_trust_formula_claim_is_proved_as_written() {
    let not_true =
        r#"{"schema":"trust-wp.trust-formula.v1","body":{"op":"not","expr":{"bool":true}}}"#;
    let not_false =
        r#"{"schema":"trust-wp.trust-formula.v1","body":{"op":"not","expr":{"bool":false}}}"#;
    for (payload, verified) in [(not_true, false), (not_false, true)] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            trust_formula_obligation("not", BundleObligationKind::Postcondition, payload),
        ));
        assert_eq!(
            result.status == VerifyBundleStatus::Verified,
            verified,
            "{payload}"
        );
    }
}

fn claim_name(
    name: &str,
    declared: Option<crate::formula::ExprSort>,
    used: NativeNameUse,
) -> NativeClaimName {
    NativeClaimName {
        name: name.to_string(),
        declared,
        used,
    }
}

/// A consumer reads a claim's names through the decoder, so it sees the
/// default `result` name the decoder gives an unnamed result record, and never
/// a name bound inside the claim or declared and never used.
#[test]
fn test_native_claim_names_are_the_decoders() {
    let unnamed_result = BundleClaim::new(
        BundleClaimFormat::TrustFormulaV1,
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [{"name": "x", "sort": "int"}, {"name": "unused", "sort": "int"}],
            "result": {"sort": "bool"},
            "body": {
                "op": "let",
                "name": "t",
                "sort": "int",
                "value": {"var": "x"},
                "body": {"op": "implies", "lhs": {"result": true}, "rhs": {"op": "ge", "lhs": {"var": "t"}, "rhs": {"var": "x"}}}
            }
        }"#,
    );
    assert_eq!(
        native_claim_names(&unnamed_result),
        Some(vec![
            claim_name(
                "x",
                Some(crate::formula::ExprSort::Int),
                NativeNameUse::Sort(NativeUseSort::Int)
            ),
            claim_name(
                "result",
                Some(crate::formula::ExprSort::Bool),
                NativeNameUse::Sort(NativeUseSort::Bool)
            ),
        ])
    );

    let pure = BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "y > old(x) - 1");
    assert_eq!(
        native_claim_names(&pure),
        Some(vec![
            claim_name("y", None, NativeNameUse::Sort(NativeUseSort::Int)),
            claim_name("x", None, NativeNameUse::Sort(NativeUseSort::Int)),
        ])
    );

    assert_eq!(
        native_claim_names(&BundleClaim::new(
            BundleClaimFormat::SmtLib2,
            "(assert true)"
        )),
        None
    );
    assert_eq!(
        native_claim_names(&BundleClaim::new(
            BundleClaimFormat::TrustWpPureExprV1,
            "result >"
        )),
        None
    );
}

/// A pure-expr predicate declares no sorts, so a name's sort is read off its
/// uses: arithmetic and ordering read an integer, a connective a boolean, an
/// equality makes its two sides one sort, and a name no use fixes is read as
/// the AST's default `Int`. Uses that disagree, or that the inference does not
/// model, are reported as such rather than resolved.
#[test]
fn test_native_claim_names_read_pure_expr_sorts_from_uses() {
    let uses = |payload: &str| {
        native_claim_names(&BundleClaim::new(
            BundleClaimFormat::TrustWpPureExprV1,
            payload,
        ))
        .expect("the predicate decodes")
        .into_iter()
        .map(|name| {
            assert_eq!(name.declared, None, "{payload}");
            (name.name, name.used)
        })
        .collect::<Vec<_>>()
    };
    let int = NativeNameUse::Sort(NativeUseSort::Int);
    let bool_ = NativeNameUse::Sort(NativeUseSort::Bool);
    let reads = |pairs: &[(&str, &NativeNameUse)]| {
        pairs
            .iter()
            .map(|(name, used)| ((*name).to_string(), (*used).clone()))
            .collect::<Vec<_>>()
    };

    assert_eq!(uses("x + 1 > x"), reads(&[("x", &int)]));
    assert_eq!(uses("!(x > x)"), reads(&[("x", &int)]));
    assert_eq!(uses("x == x"), reads(&[("x", &NativeNameUse::Unfixed)]));
    assert_eq!(uses("b ==> b"), reads(&[("b", &bool_)]));
    assert_eq!(uses("b == true"), reads(&[("b", &bool_)]));
    // Equality carries a sort from one side to the other, through `old`.
    assert_eq!(
        uses("x == old(y) && y * 2 >= 0"),
        reads(&[("x", &int), ("y", &int)])
    );
    assert_eq!(
        uses("(b == c) && c"),
        reads(&[("b", &bool_), ("c", &bool_)])
    );
    // An `if` makes its branches one sort, and its condition a boolean.
    assert_eq!(
        uses("(if c { x } else { -y }) >= z % 3"),
        reads(&[("c", &bool_), ("x", &int), ("y", &int), ("z", &int)])
    );
    assert_eq!(
        uses("x > 0 && x"),
        reads(&[(
            "x",
            &NativeNameUse::Conflicting(NativeUseSort::Int, NativeUseSort::Bool)
        )])
    );
    assert_eq!(
        uses("(x > 0) == x"),
        reads(&[(
            "x",
            &NativeNameUse::Conflicting(NativeUseSort::Int, NativeUseSort::Bool)
        )])
    );
    assert_eq!(
        uses("v.len() > n"),
        reads(&[
            (
                "v",
                &NativeNameUse::Sort(NativeUseSort::Other("a method-call operand".to_string()))
            ),
            ("n", &int),
        ])
    );
    // A quantifier's own name is not one of the claim's.
    assert_eq!(
        uses("forall<i: Int> i >= x ==> i + 1 > x"),
        reads(&[("x", &int)])
    );
}

/// A dereferenced name is a reference, to the sort its dereference is read
/// at, and one read at two referent sorts, or both as a reference and as a
/// value, has no one reading. The operand of `*` was read at an opaque
/// "a reference" that no binder's reference sort agreed with, and the
/// conflict was dropped.
#[test]
fn test_native_claim_names_read_a_dereferenced_name_as_a_reference() {
    let uses = |payload: &str| {
        native_claim_names(&BundleClaim::new(
            BundleClaimFormat::TrustWpPureExprV1,
            payload,
        ))
        .expect("the predicate decodes")
        .into_iter()
        .map(|name| (name.name, name.used))
        .collect::<Vec<_>>()
    };
    let reads = |pairs: &[(&str, &NativeNameUse)]| {
        pairs
            .iter()
            .map(|(name, used)| ((*name).to_string(), (*used).clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        uses("*m > 0"),
        reads(&[(
            "m",
            &NativeNameUse::Sort(NativeUseSort::Other("a reference to Int".to_string()))
        )])
    );
    assert_eq!(
        uses("**m == **m"),
        reads(&[(
            "m",
            &NativeNameUse::Sort(NativeUseSort::Other(
                "a reference to a reference".to_string()
            ))
        )])
    );
    // A reference read as an integer, or at two referent sorts, conflicts.
    assert_eq!(
        uses("(*m > 0) && m > 0"),
        reads(&[(
            "m",
            &NativeNameUse::Conflicting(
                NativeUseSort::Int,
                NativeUseSort::Other("a reference".to_string())
            )
        )])
    );
    assert_eq!(
        uses("*m > 0 && *m"),
        reads(&[(
            "m",
            &NativeNameUse::Conflicting(
                NativeUseSort::Other("a reference to Bool".to_string()),
                NativeUseSort::Other("a reference to Int".to_string())
            )
        )])
    );
}

/// The claims measured VERIFIED at exit 0, weakest-precondition and
/// strongest-postcondition: `*e` was read as an integer whatever `e` is, the
/// two-sort check kept only `Int` against `Bool`, an ascription on a `*`
/// operand was dropped, and native replay proved `e + k > e` by its shape.
/// Each must be refused before any verdict, naming why.
const MEASURED_DEREFERENCE_FALSE_ACCEPTS: [(&str, &str); 18] = [
    (
        "forall<p: &bool> (0 < 1 ==> *p + 1 > *p)",
        "reads `p` at both a reference to Bool and a reference to Int",
    ),
    (
        "forall<p: &T> (0 < 1 ==> *p + 1 > *p)",
        "reads the referent of `p` at sort TypeParam(T)",
    ),
    (
        "forall<p: &[Int]> (0 < 1 ==> *p + 1 > *p)",
        "reads the referent of `p` at sort Seq",
    ),
    (
        "forall<p: &bool> { let t: Int = *p; 0 < 1 ==> t + 1 > t }",
        "`let` annotation `: Int` on `*p`",
    ),
    (
        "forall<p: &bool> { let t = *p; 0 < 1 ==> (t : Int) + 1 > (t : Int) }",
        "`t` is annotated at sort Int where it is bound at sort Bool",
    ),
    (
        "forall<p: &T> { let t = *p; 0 < 1 ==> t + 1 > t }",
        "reads the referent of `p` at sort TypeParam(T)",
    ),
    (
        "forall<v: bool> (0 < 1 ==> *v + 1 > *v)",
        "`*v` dereferences `v`, which is not a reference: its sort is Bool",
    ),
    (
        "forall<v: bool> { let t: Int = *v; 0 < 1 ==> t + 1 > t }",
        "`let` annotation `: Int` on `*v`",
    ),
    (
        "forall<v: bool> (0 < 1 ==> *&v + 1 > *&v)",
        "reads `v` at both Int and Bool",
    ),
    (
        "exists<v: bool> (0 < 1 ==> *v + 1 > *v)",
        "`*v` dereferences `v`, which is not a reference: its sort is Bool",
    ),
    (
        "forall<p: &&bool> (0 < 1 ==> **p + 1 > **p)",
        "reads `p` at both a reference to a reference to Bool and a reference to a reference to Int",
    ),
    (
        "forall<p: &mut bool> (0 < 1 ==> *p + 1 > *p)",
        "reads `p` at both a reference to Bool and a reference to Int",
    ),
    (
        "forall<p: &T> exists<v: Int> (0 < 1 ==> *p + 1 > *p)",
        "reads the referent of `p` at sort TypeParam(T)",
    ),
    (
        "(0 < 1 ==> *b + 1 > *b) && ((b : bool) || true)",
        "`*b` dereferences `b`, which is not a reference: its sort is Bool",
    ),
    (
        "forall<p: &bool> (0 < 1 ==> (*p : Int) + 1 > (*p : Int))",
        "type ascription `: Int` on `*p`",
    ),
    (
        "forall<v: bool> (0 < 1 ==> (*v : Int) + 1 > (*v : Int))",
        "type ascription `: Int` on `*v`",
    ),
    (
        "forall<p: &T> (0 < 1 ==> (*p : Int) + 1 > (*p : Int))",
        "type ascription `: Int` on `*p`",
    ),
    (
        "forall<p: &bool> { let t: Int = (*p : Int); 0 < 1 ==> t + 1 > t }",
        "type ascription `: Int` on `*p`",
    ),
];

/// `*e` reads the sort `e` references: every measured claim is refused
/// before a verdict, naming the dereference, the annotation it drops or the
/// name read at two sorts; its well-sorted twins still verify.
#[test]
fn test_native_dereference_reads_the_referent_sort() {
    for (payload, named) in MEASURED_DEREFERENCE_FALSE_ACCEPTS {
        let obligation = typed_obligation("deref", BundleObligationKind::Postcondition, payload);
        let refusal = native_predicate_for_obligation(&obligation)
            .expect_err(&format!("`{payload}` must not be native proof input"));
        assert!(
            refusal.message.contains(named),
            "`{payload}` must be refused naming `{named}`: {}",
            refusal.message
        );
        let result =
            NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(obligation));
        assert_ne!(result.status, VerifyBundleStatus::Verified, "{payload}");
        assert_ne!(result.exit_code(), 0, "{payload}");
    }

    for payload in [
        "forall<p: &Int> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &mut Int> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &&Int> (0 < 1 ==> **p + 1 > **p)",
        "forall<p: &Int> { let t = *p; 0 < 1 ==> t + 1 > t }",
        "forall<v: Int> (0 < 1 ==> *&v + 1 > *&v)",
        "forall<p: &bool> *p == *p",
        "forall<p: &mut Int> (0 < 1 ==> ^p + 1 > ^p)",
    ] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            typed_obligation("deref-valid", BundleObligationKind::Postcondition, payload),
        ));
        assert_eq!(
            result.status,
            VerifyBundleStatus::Verified,
            "`{payload}` is valid"
        );
    }
    for payload in [
        "forall<p: &Int> (0 < 1 ==> *p + 1 > *p + 1)",
        "forall<p: &Int> (0 < 1 ==> *p > *p)",
    ] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            typed_obligation("deref-false", BundleObligationKind::Postcondition, payload),
        ));
        assert_ne!(
            result.status,
            VerifyBundleStatus::Verified,
            "`{payload}` is false"
        );
    }
}

/// Native replay's integer rules alone, fed the measured claims without the
/// claim-side checks that refuse them first: a shape rule (`e + k > e`,
/// `e ^ e == 0`, a negated order) reads an operand as an integer only where
/// replay knows it to be one. Each of these was proved by its shape.
#[test]
fn test_native_replay_integer_rules_read_only_integers() {
    let prove = |payload: &str| {
        let predicate = crate::contract_parser::parse_contract(payload).expect("parses");
        super::proof::prove_native_pure_predicate(
            &predicate,
            NativeClaimFormat::TrustWpPureExprV1,
            &[],
        )
    };
    let verified = |payload: &str| {
        matches!(
            prove(payload),
            super::proof::NativePureProofOutcome::Verified(_)
        )
    };
    for payload in [
        "forall<p: &bool> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &T> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &[Int]> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &&bool> (0 < 1 ==> **p + 1 > **p)",
        "forall<p: &mut bool> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &Int> (0 < 1 ==> p + 1 > p)",
        "forall<v: bool> (0 < 1 ==> *v + 1 > *v)",
        "forall<v: bool> (0 < 1 ==> v + 1 > v)",
        "forall<v: bool> v + 1 > v",
        "forall<v: bool> (v ^ v) == 0",
        "forall<p: &bool> (!(*p < 0) ==> *p >= 0)",
        "forall<p: &Int> (0 < 1 ==> ^p + 1 > ^p)",
        "0 < 1 ==> *b + 1 > *b",
        "0 < 1 ==> ^b + 1 > ^b",
        "forall<v: bool> (v == x && x > 0 ==> v + 1 > v)",
    ] {
        assert!(
            !verified(payload),
            "`{payload}` reads a non-integer as an integer: {:?}",
            prove(payload)
        );
    }
    for payload in [
        "forall<p: &Int> (0 < 1 ==> *p + 1 > *p)",
        "forall<p: &&Int> (0 < 1 ==> **p + 1 > **p)",
        "forall<p: &mut Int> (0 < 1 ==> ^p + 1 > ^p)",
        "forall<v: Int> (0 < 1 ==> v + 1 > v)",
        "forall<v: Int> (v ^ v) == 0",
        "forall<p: &Int> (!(*p < 0) ==> *p >= 0)",
        "0 < 1 ==> x + 1 > x",
        "forall<v: Int> (v == x && x > 0 ==> v + 1 > v)",
    ] {
        assert!(
            verified(payload),
            "`{payload}` is valid: {:?}",
            prove(payload)
        );
    }
}

/// A pointer summary fact equates the values it names only at the pointer
/// kind those values have, and `*e`/`^e` have the kind of the sort `e`
/// references, as claim decoding reads them. `pointer_kind_for_expr` read
/// `^e` and `old(^e)` at `e`'s own kind, so a thin fact proved `^p == ^q` of
/// two `&mut Int`s (integers, which no pointer fact equates) and of two
/// `&mut &[Int]`s (slices, which a thin fact, the same data address at any
/// length, does not equate). Each verified at exit 0.
#[test]
fn test_native_pointer_summary_reads_the_referent_kind() {
    let verify = |payload: &str, fact: BundleSummaryFact| {
        NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            typed_obligation(
                "pointer-referent",
                BundleObligationKind::Postcondition,
                payload,
            )
            .with_summary_fact(fact),
        ))
    };
    for (payload, left, right) in [
        (
            "forall<p: &mut &[Int]> forall<q: &mut &[Int]> ^p == ^q",
            "^p",
            "^q",
        ),
        (
            "forall<p: &mut Int> forall<q: &mut Int> ^p == ^q",
            "^p",
            "^q",
        ),
        (
            "forall<p: &mut bool> forall<q: &mut bool> ^p == ^q",
            "^p",
            "^q",
        ),
        (
            "forall<p: &mut Int> forall<q: &mut Int> old(^p) == old(^q)",
            "old(^p)",
            "old(^q)",
        ),
        (
            "forall<p: &mut Int> forall<q: &mut Int> (0 < 1 ==> ^p == ^q)",
            "^p",
            "^q",
        ),
        ("forall<p: &&[Int]> forall<q: &&[Int]> *p == *q", "*p", "*q"),
    ] {
        let result = verify(payload, pointer_summary_fact("thin", left, right));
        assert_ne!(
            result.status,
            VerifyBundleStatus::Verified,
            "`{payload}` with a thin fact on `{left}`, `{right}`"
        );
        assert_ne!(result.exit_code(), 0, "{payload}");
    }
    // Integers are no pointers, whichever fact names them.
    let result = verify(
        "forall<p: &mut Int> forall<q: &mut Int> ^p == ^q",
        fat_pointer_summary_fact("fat", "^p", "^q"),
    );
    assert_ne!(result.status, VerifyBundleStatus::Verified);

    // Controls: a fact of the referent's kind equates the pointers it names.
    for (payload, fact) in [
        (
            "forall<p: &mut &[Int]> forall<q: &mut &[Int]> ^p == ^q",
            fat_pointer_summary_fact("fat", "^p", "^q"),
        ),
        (
            "forall<p: &&[Int]> forall<q: &&[Int]> *p == *q",
            fat_pointer_summary_fact("fat", "*p", "*q"),
        ),
        (
            "forall<p: &mut &Int> forall<q: &mut &Int> ^p == ^q",
            pointer_summary_fact("thin", "^p", "^q"),
        ),
    ] {
        let request = single_obligation_request(
            typed_obligation(
                "pointer-referent",
                BundleObligationKind::Postcondition,
                payload,
            )
            .with_summary_fact(fact),
        );
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
        assert_eq!(result.status, VerifyBundleStatus::Verified, "{payload}");
        let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status
        else {
            panic!("expected verified obligation");
        };
        replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
    }
}

/// Native replay alone substitutes an assumption's equality only between
/// values of one `Int` or `Bool` sort, and refuses a claim reading one name
/// at two sorts, by the inference claim decoding refuses it with. Replay
/// alone proved each of these by `forall-true-body` or `and-true`: a `&bool`
/// (`&T`, `&[Int]`, `bool`) name replaced by a `&Int` one, a `&Int` by a
/// `&mut Int` under `^`, a free `b` read as an integer in one conjunct and a
/// `bool` in the other, and `p := if true {q} else {q}` for two `&mut Int`s,
/// whose final values the pointer reading of `==` (one address) does not
/// equate. The last also verified at exit 0 through the whole pipeline.
#[test]
fn test_native_replay_substitutes_only_a_like_sorted_value() {
    let prove = |payload: &str| {
        let predicate = crate::contract_parser::parse_contract(payload).expect("parses");
        super::proof::prove_native_pure_predicate(
            &predicate,
            NativeClaimFormat::TrustWpPureExprV1,
            &[],
        )
    };
    let verified = |payload: &str| {
        matches!(
            prove(payload),
            super::proof::NativePureProofOutcome::Verified(_)
        )
    };
    for payload in [
        "forall<p: &Int> forall<q: &bool> (p == q && 0 < 1 ==> *q + 1 > *q)",
        "forall<p: &Int> forall<q: &T> (p == q && 0 < 1 ==> *q + 1 > *q)",
        "forall<p: &Int> forall<q: &[Int]> (q == p && 0 < 1 ==> *q + 1 > *q)",
        "forall<p: &Int> forall<v: bool> (v == p && 0 < 1 ==> *v + 1 > *v)",
        "forall<p: &mut Int> forall<q: &Int> (q == p && 0 < 1 ==> ^q + 1 > ^q)",
        "forall<p: &Int> forall<q: &bool> (p == q && 0 < 1 ==> *q >= *q + 0)",
        "forall<p: &Int> forall<q: &bool> ((q == p && 0 < 1) ==> (*q - *q) >= 0)",
        "(0 < 1 ==> b + 1 > b) && ((b : bool) || true)",
        "(0 < 1 ==> b@ + 1 > b@) && ((b : bool) || true)",
        "(0 < 1 ==> view(b) + 1 > view(b)) && (b || true)",
        "forall<p: &mut Int> forall<q: &mut Int> ((p == (if true {q} else {q}) && 0 < 1) ==> \
         ^p + 1 > ^(if true {q} else {q}))",
    ] {
        assert!(
            !verified(payload),
            "`{payload}` reads a value at a sort it does not have: {:?}",
            prove(payload)
        );
    }
    let ite = "forall<p: &mut Int> forall<q: &mut Int> ((p == (if true {q} else {q}) && 0 < 1) \
               ==> ^p + 1 > ^(if true {q} else {q}))";
    let result =
        NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(typed_obligation(
            "final-substitution",
            BundleObligationKind::Postcondition,
            ite,
        )));
    assert_ne!(result.status, VerifyBundleStatus::Verified, "{ite}");

    // Controls: an `Int` name replaced by an `Int` value.
    for payload in [
        "forall<p: &mut Int> forall<x: Int> ((x == ^p && 0 < 1) ==> x + 1 > ^p)",
        "forall<v: Int> (v == x && x > 0 ==> v + 1 > v)",
        "0 < 1 ==> b@ + 1 > b@",
    ] {
        assert!(
            verified(payload),
            "`{payload}` is valid: {:?}",
            prove(payload)
        );
    }
}

/// Native replay alone, over the raw parse, reads every reference level the
/// text writes: a reference pattern, a binding by reference, a borrow a `let`
/// binds and a nested borrow under `*`. Each of these was proved by replay
/// alone (`forall-true-body`), the parser having read the level off: `let &t
/// = p` bound `t` to `p`, `let ref t = p` and `let r = &p` bound the name to
/// `p` so `^t`/`^r` read `^p`, and `**(& &v)` read `*v`. The claim side
/// refused only the last two, by recording a dropped borrow. A view read at
/// two sorts was proved too: every `b@` had a sort of its own.
#[test]
fn test_native_replay_reads_every_reference_level() {
    let outcome = |payload: &str| {
        crate::contract_parser::parse_contract(payload).map(|predicate| {
            super::proof::prove_native_pure_predicate(
                &predicate,
                NativeClaimFormat::TrustWpPureExprV1,
                &[],
            )
        })
    };
    let verified = |payload: &str| {
        matches!(
            outcome(payload),
            Ok(super::proof::NativePureProofOutcome::Verified(_))
        )
    };
    for payload in [
        "forall<p: &mut Int> { let ref t = p; 0 < 1 ==> ^t + 1 > ^t }",
        "forall<p: &mut Int> { let ref mut t = p; 0 < 1 ==> ^t + 1 > ^t }",
        "forall<p: &Int> { let &t = p; 0 < 1 ==> *t + 1 > *t }",
        "forall<p: &mut Int> { let &mut t = p; 0 < 1 ==> *t + 1 > *t }",
        "forall<p: &mut Int> { let &mut t = p; 0 < 1 ==> ^t + 1 > ^t }",
        "forall<p: &mut Int> { let r = &p; 0 < 1 ==> ^r + 1 > ^r }",
        "forall<p: &mut Int> { let r = &mut p; 0 < 1 ==> ^r + 1 > ^r }",
        "forall<v: &Int> (0 < 1 ==> **(& &v) + 1 > **(& &v))",
        "forall<v: &Int> { let r = & &v; 0 < 1 ==> **r + 1 > **r }",
        "(b@ == true && 0 < 1) ==> b@ + 1 > b@",
        "(0 < 1 ==> b@ + 1 > b@) && (b@ == true || true)",
        "(0 < 1 ==> view(b) + 1 > view(b)) && (view(b) == true || true)",
        "(0 < 1 ==> view(b) + 1 > b@) && (b@ == true || true)",
    ] {
        assert!(!verified(payload), "`{payload}`: {:?}", outcome(payload));
    }
    // Controls: each level read where the text puts it.
    for payload in [
        "forall<p: &Int> { let &t = p; 0 < 1 ==> t + 1 > t }",
        "forall<p: &&Int> { let &t = p; 0 < 1 ==> *t + 1 > *t }",
        "forall<p: &mut Int> { let &mut t = p; 0 < 1 ==> t + 1 > t }",
        "forall<p: &mut Int> { let ref t = p; 0 < 1 ==> ^*t + 1 > ^*t }",
        "forall<v: Int> { let r = &v; 0 < 1 ==> *r + 1 > *r }",
        "forall<v: Int> (0 < 1 ==> **(& &v) + 1 > **(& &v))",
        "0 < 1 ==> b@ + 1 > b@",
        "0 < 1 ==> view(b) + 1 > b@",
    ] {
        assert!(
            verified(payload),
            "`{payload}` is valid: {:?}",
            outcome(payload)
        );
    }
}

/// A pointer fact names the values it relates. `let &t = p` bound `t` to `p`
/// itself, so with a disjointness fact on `p`, `q` the claim `{ let &t = p;
/// let &u = q; t != u }` over two `&&Int`s verified at exit 0: it reads
/// `*p != *q`, which two distinct pointers to one `&Int` falsify.
#[test]
fn test_native_reference_pattern_is_not_the_matched_pointer() {
    let verify = |payload: &str| {
        NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            typed_obligation(
                "reference-pattern",
                BundleObligationKind::Postcondition,
                payload,
            )
            .with_summary_fact(pointer_disjoint_binding_summary_fact("disjoint", "p", "q")),
        ))
    };
    for payload in [
        "forall<p: &&Int> forall<q: &&Int> { let &t = p; let &u = q; t != u }",
        "forall<p: &&Int> forall<q: &&Int> { let &t = p; let &u = q; !(t == u) }",
        "forall<p: &&Int> forall<q: &&Int> { let &t = p; let &u = q; 0 < 1 ==> t != u }",
        "forall<p: &mut &Int> forall<q: &mut &Int> { let &mut t = p; let &mut u = q; t != u }",
        "forall<p: &&Int> forall<q: &&Int> { let (&t, &u) = (p, q); t != u }",
    ] {
        let result = verify(payload);
        assert_ne!(result.status, VerifyBundleStatus::Verified, "{payload}");
        assert_ne!(result.exit_code(), 0, "{payload}");
    }
    // Control: the fact is about `p` and `q`.
    let result = verify("forall<p: &&Int> forall<q: &&Int> p != q");
    assert_eq!(result.status, VerifyBundleStatus::Verified);
}

/// `==` of two references in a bundle claim is the same address: the final
/// values of two `&mut` at one address need not agree (a Creusot pair
/// equality would equate them), so equality substitution never carries `p ==
/// q` into `^p`, however `q` is spelled, and no pointer fact on `p`, `q` says
/// anything of `^p`, `^q`.
#[test]
fn test_native_reference_equality_is_the_address_not_the_final_value() {
    let prove = |payload: &str| {
        let predicate = crate::contract_parser::parse_contract(payload).expect("parses");
        super::proof::prove_native_pure_predicate(
            &predicate,
            NativeClaimFormat::TrustWpPureExprV1,
            &[pointer_binding_summary_fact("eq", "p", "q")],
        )
    };
    for payload in [
        "forall<p: &mut Int> forall<q: &mut Int> ((p == q && 0 < 1) ==> ^p + 1 > ^q)",
        "forall<p: &mut Int> forall<q: &mut Int> (p == q ==> ^p == ^q)",
        "forall<p: &mut Int> forall<q: &mut Int> ((p == (if true {q} else {q}) && 0 < 1) ==> \
         ^p + 1 > ^(if true {q} else {q}))",
        "forall<p: &mut Int> forall<q: &mut Int> ^p == ^q",
        "forall<p: &mut Int> forall<q: &mut Int> old(^p) == old(^q)",
    ] {
        assert!(
            !matches!(
                prove(payload),
                super::proof::NativePureProofOutcome::Verified(_)
            ),
            "`{payload}`: {:?}",
            prove(payload)
        );
    }
    // Control: the fact is the address.
    assert!(matches!(
        prove("forall<p: &mut Int> forall<q: &mut Int> p == q"),
        super::proof::NativePureProofOutcome::Verified(_)
    ));
}

/// In `ref a @ t` only `a` binds by reference: `t` binds the matched value
/// itself (Rust's identifier pattern `ref? mut? IDENT @ subpattern`). Reading
/// `t` as a borrow of the value read every `*t` one level off: with a
/// disjointness fact on `p`, `q`, `{ let ref a @ t = p; let ref b @ u = q; *t
/// != *u }` over two `&&Int`s read `p != q` and verified at exit 0, and `**t`
/// of a `p: &Int` was read as `*p` and verified with no fact at all.
#[test]
fn test_native_binding_by_reference_binds_only_its_name() {
    let verify = |payload: &str, fact: Option<BundleSummaryFact>| {
        let mut obligation =
            typed_obligation("ref-alias", BundleObligationKind::Postcondition, payload);
        if let Some(fact) = fact {
            obligation = obligation.with_summary_fact(fact);
        }
        NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(obligation))
    };
    let replay = |payload: &str| {
        crate::contract_parser::parse_contract(payload).map(|predicate| {
            super::proof::prove_native_pure_predicate(
                &predicate,
                NativeClaimFormat::TrustWpPureExprV1,
                &[],
            )
        })
    };
    for payload in [
        "forall<p: &&Int> forall<q: &&Int> { let ref a @ t = p; let ref b @ u = q; *t != *u }",
        "forall<p: &&Int> forall<q: &&Int> { let ref mut a @ t = p; let ref mut b @ u = q; *t != *u }",
        "forall<p: &&Int> forall<q: &&Int> { let ref a @ t = p; let ref b @ u = q; !(*t == *u) }",
        "forall<p: &mut &mut Int> forall<q: &mut &mut Int> { let ref a @ t = p; let ref b @ u = q; *t != *u }",
    ] {
        let result = verify(
            payload,
            Some(pointer_disjoint_binding_summary_fact("disjoint", "p", "q")),
        );
        assert_ne!(result.status, VerifyBundleStatus::Verified, "{payload}");
        assert_ne!(result.exit_code(), 0, "{payload}");
    }
    // `t` is `p`: `**t` of a `&Int` and `^*t` of a `&mut Int` have no reading.
    for payload in [
        "forall<p: &Int> { let ref a @ t = p; 0 < 1 ==> **t + 1 > **t }",
        "forall<p: &mut Int> { let ref a @ t = p; 0 < 1 ==> ^*t + 1 > ^*t }",
        "forall<p: &mut Int> { let ref mut a @ t = p; 0 < 1 ==> ^*t + 1 > ^*t }",
        "forall<p: &Int> { let ref a @ b @ t = p; 0 < 1 ==> **t + 1 > **t }",
        "forall<p: &mut Int> { let ref a @ t = p; 0 < 1 ==> ^**&t + 1 > ^**&t }",
    ] {
        assert_ne!(
            verify(payload, None).status,
            VerifyBundleStatus::Verified,
            "{payload}"
        );
        assert!(
            !matches!(
                replay(payload),
                Ok(super::proof::NativePureProofOutcome::Verified(_))
            ),
            "replay alone: `{payload}`: {:?}",
            replay(payload)
        );
    }
    // Controls: `t` is the value, `a` a borrow of it.
    for payload in [
        "forall<p: &Int> { let ref a @ t = p; 0 < 1 ==> *t + 1 > *t }",
        "forall<p: &Int> { let ref a @ t = p; 0 < 1 ==> **a + 1 > **a }",
        "forall<p: &mut Int> { let ref a @ t = p; 0 < 1 ==> ^t + 1 > ^t }",
    ] {
        assert!(
            matches!(
                replay(payload),
                Ok(super::proof::NativePureProofOutcome::Verified(_))
            ),
            "`{payload}` is valid: {:?}",
            replay(payload)
        );
    }
}

/// `x @ y` binds both names to the value, read once. The subpattern was
/// matched against the value after the alias rebound its names, so `{ let x
/// @ y = x + 1; .. }` read `y` as the new `x` plus one and replay proved the
/// false `y + 1 > x + 1`.
#[test]
fn test_native_alias_pattern_reads_the_value_once() {
    let replay = |payload: &str| {
        let predicate = crate::contract_parser::parse_contract(payload).expect("parses");
        super::proof::prove_native_pure_predicate(
            &predicate,
            NativeClaimFormat::TrustWpPureExprV1,
            &[],
        )
    };
    for payload in [
        "forall<x: Int> { let x @ y = x + 1; 0 < 1 ==> y + 1 > x + 1 }",
        "forall<x: Int> { let x @ y = x + 1; y == x + 1 }",
    ] {
        assert!(
            !matches!(
                replay(payload),
                super::proof::NativePureProofOutcome::Verified(_)
            ),
            "`{payload}`: {:?}",
            replay(payload)
        );
    }
    assert!(matches!(
        replay("forall<x: Int> { let x @ y = x + 1; y == x }"),
        super::proof::NativePureProofOutcome::Verified(_)
    ));
}

/// A pointer fact relates the values its names have at the obligation's
/// binders. Replay matched a fact by name, so a binder that rebinds `p` or
/// `q` read the fact about another value: with a disjointness fact on `p`,
/// `q`, `forall<p: &Int> forall<q: &Int> forall<p: &Int> p != q` verified at
/// exit 0. The claims are generated: each relation the facts decide, under
/// each binder that shadows either name, at each reference sort. Each
/// unshadowed claim is the control.
#[test]
fn test_native_pointer_fact_does_not_reach_a_shadowing_binder() {
    let verify = |payload: &str, fact: BundleSummaryFact| {
        NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            typed_obligation("shadow", BundleObligationKind::Postcondition, payload)
                .with_summary_fact(fact),
        ))
    };
    let mut checked = 0;
    let mut violations = Vec::new();
    for sort in ["&Int", "&mut Int", "&&Int"] {
        let prefix = format!("forall<p: {sort}> forall<q: {sort}> forall<r: {sort}>");
        for (relation, fact) in [
            (
                "p != q",
                pointer_disjoint_binding_summary_fact("d", "p", "q"),
            ),
            ("p == q", pointer_binding_summary_fact("e", "p", "q")),
            (
                "!(p == q)",
                pointer_disjoint_binding_summary_fact("d", "p", "q"),
            ),
        ] {
            let control = format!("{prefix} {relation}");
            assert_eq!(
                verify(&control, fact.clone()).status,
                VerifyBundleStatus::Verified,
                "control `{control}`"
            );
            for name in ["p", "q"] {
                for shadowed in [
                    format!("forall<{name}: {sort}> {relation}"),
                    format!("(0 < 1 ==> forall<{name}: {sort}> {relation})"),
                    format!("{{ let {name} = r; {relation} }}"),
                    format!("{{ let s = &{name}; forall<{name}: {sort}> *s == *s && {relation} }}"),
                    format!("({relation} && forall<{name}: {sort}> {relation})"),
                    format!("({relation} && {{ let {name} = r; {relation} }})"),
                ] {
                    let payload = format!("{prefix} {shadowed}");
                    let result = verify(&payload, fact.clone());
                    if result.status == VerifyBundleStatus::Verified || result.exit_code() == 0 {
                        violations.push(payload);
                    }
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 108);
    assert!(
        violations.is_empty(),
        "{} of {checked} verified:\n{}",
        violations.len(),
        violations.join("\n")
    );
    // A free name bound once inside the claim is another value too.
    let result = verify(
        "p != q && forall<p: &Int> forall<q: &Int> p != q",
        pointer_disjoint_binding_summary_fact("d", "p", "q"),
    );
    assert_ne!(result.status, VerifyBundleStatus::Verified);
}

/// A pointer fact is about the values its names have at the obligation's
/// binders: a free name, or one the predicate's opening universal quantifiers
/// bind. A name bound once elsewhere is another value: `forall<q: &Int>
/// !(exists<p: &Int> p == q)` is false (the `p` that is `q`), and with a
/// disjointness fact on `p`, `q` replay read the fact into the `exists` body
/// and verified it at exit 0. The claims are generated: each relation the
/// facts decide, under each binder of a fact's name that is not the
/// obligation's, at each reference sort; none may verify. The obligation's
/// own binders are the control.
#[test]
fn test_native_pointer_fact_binds_the_obligation_binder_only() {
    let verify = |payload: &str, fact: BundleSummaryFact| {
        NativeTrustWpBundleVerifier.verify_bundle(single_obligation_request(
            typed_obligation("fact-binder", BundleObligationKind::Postcondition, payload)
                .with_summary_fact(fact),
        ))
    };
    let mut checked = 0;
    let mut violations = Vec::new();
    for sort in ["&Int", "&mut Int", "&&Int"] {
        for (relation, fact, false_claims) in [
            (
                "p != q",
                pointer_disjoint_binding_summary_fact("d", "p", "q"),
                [
                    format!("forall<q: {sort}> !(exists<p: {sort}> p == q)"),
                    format!("forall<p: {sort}> !(exists<q: {sort}> p == q)"),
                    format!("!(exists<p: {sort}> exists<q: {sort}> p == q)"),
                    format!("forall<q: {sort}> (0 < 1 ==> !(exists<p: {sort}> p == q))"),
                    format!("forall<q: {sort}> !(exists<p: {sort}> !(p != q))"),
                    format!("forall<q: {sort}> (true && !(exists<p: {sort}> p == q))"),
                ],
            ),
            (
                "p == q",
                pointer_binding_summary_fact("e", "p", "q"),
                [
                    format!("forall<q: {sort}> !(exists<p: {sort}> p != q)"),
                    format!("forall<p: {sort}> !(exists<q: {sort}> p != q)"),
                    format!("!(exists<p: {sort}> exists<q: {sort}> p != q)"),
                    format!("forall<q: {sort}> (0 < 1 ==> !(exists<p: {sort}> p != q))"),
                    format!("forall<q: {sort}> !(exists<p: {sort}> !(p == q))"),
                    format!("forall<q: {sort}> (true && !(exists<p: {sort}> p != q))"),
                ],
            ),
        ] {
            let control = format!("forall<p: {sort}> forall<q: {sort}> {relation}");
            assert_eq!(
                verify(&control, fact.clone()).status,
                VerifyBundleStatus::Verified,
                "control `{control}`"
            );
            for payload in false_claims {
                let result = verify(&payload, fact.clone());
                if result.status == VerifyBundleStatus::Verified || result.exit_code() == 0 {
                    violations.push(payload);
                }
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 36);
    assert!(
        violations.is_empty(),
        "{} of {checked} verified:\n{}",
        violations.len(),
        violations.join("\n")
    );
}
