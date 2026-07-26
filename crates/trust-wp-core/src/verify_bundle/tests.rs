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
    assert!(result.obligation_results.is_empty());
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligations"));
    assert_eq!(BundleDiagnosticSeverity::Invalid.as_str(), "invalid");
}

#[test]
fn test_bundle_result_all_verified_requires_complete_results() {
    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence())],
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
    let result = VerifyBundleResult::from_obligation_results(
        request(),
        vec![BundleObligationResult::verified("obl-1", evidence())],
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

    assert!(request.validation_diagnostics().is_empty());
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
fn test_native_trust_wp_verifier_keeps_nonlinear_symbolic_product_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-nonlinear-product",
        BundleObligationKind::Postcondition,
        "x >= 1 ==> x * y >= 1",
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
fn test_native_trust_wp_verifier_leaves_unproved_result_alias_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-result-alias-unproved",
        BundleObligationKind::Postcondition,
        "{ let ret = result; result >= 0 ==> ret > 0 }",
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
fn test_native_trust_wp_verifier_leaves_unproved_linear_implication_unsupported() {
    let request = single_obligation_request(typed_obligation(
        "obl-linear-unproved",
        BundleObligationKind::Postcondition,
        "x >= 0 ==> x - 1 >= 0",
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
fn test_native_trust_wp_verifier_unknown_symbolic_postcondition_fails_closed() {
    let request = single_obligation_request(typed_obligation(
        "obl-post-unknown",
        BundleObligationKind::Postcondition,
        "result > x",
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
