#![cfg(feature = "trust-ir-native")]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fmt::Write as _;

use trust_ir::{
    Block, BlockId, CastLayoutEvidence, CastOp, Constant, FatPtrKind, FieldDef, FuncId, FuncTy,
    Function, Inst, InstrNode, Module, NativeAdapterInput, NativeAdtLayoutFact, NativeAssertionId,
    NativeBundleProducer, NativeCastFact, NativeCompilerFactId, NativeCompilerFactRef,
    NativeDiagnosticsPolicy, NativeEvidenceArtifactKind, NativeFatPointerFact,
    NativeMonomorphizationFact, NativeMonomorphizationId, NativeObligationCause,
    NativeObligationSource, NativeReplayAtom, NativeReplayAtomId, NativeReplayContext,
    NativeRequestId, NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
    NativeVerificationRequest, ObligationKind, PointerLayoutShape, PointerMetadataShape,
    ProofDigest, ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
    ProofObligation, ProofObligationSourceIdentity, ProofReplayIdentity, ProofStatus,
    ProofTransform, ProofTransformStage, PublicObligationIdentity, SourceSpan, StructDef, StructId,
    StructRepr, TrustWpNativeRequest, TrustWpRequestOptions, TrustWpVerificationMode, Ty, ValueId,
    NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION,
};
use trust_wp_lib::{
    replay_verify_bundle_result_evidence, trust_ir_native_bundle_to_verify_requests,
    verify_trust_ir_native_bundle, verify_trust_ir_native_bundle_and_record_evidence,
    BundleClaimFormat, BundleDigest, BundleNativeVerificationMode, BundleObligation,
    BundleObligationStatus, BundleProofAtomRole, BundleResultMetadata, BundleTmirCompilerFactKind,
    BundleTmirObligationCause, BundleTmirSourceSpan, EvidenceArtifactKind,
    TrustIrNativeBundleError, TrustIrTrustWpMode, TrustIrUnsupportedModeReason, VerifyBundleStatus,
    TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
};

fn digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

fn bundle_digest_from_tmir(digest: ProofDigest) -> BundleDigest {
    BundleDigest::new(digest.algorithm.to_string(), hex_digest(&digest.bytes))
}

fn hex_digest(bytes: &[u8; 32]) -> String {
    let mut output = String::with_capacity(64);
    for byte in bytes {
        let _ = write!(output, "{byte:02x}");
    }
    output
}

fn trust_formula_true() -> &'static str {
    r#"{"schema":"trust-wp.trust-formula.v1","variables":[],"body":{"bool":true}}"#
}

fn trust_formula_linear_variable() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "implies",
            "lhs": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}},
            "rhs": {
                "op": "gt",
                "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                "rhs": {"int": 0}
            }
        }
    }"#
}

/// Trust #23 (body-bound ensures lowering) conformance pin: the compiler's
/// golden envelope for `fn ge_refl(x: u64) -> u64 ensures result >= x { x }` —
/// `result` LET-BOUND to the exact defining expression (here the parameter
/// itself), no top-level result record. The Trust-side builder
/// (trust_ir_bridge::trust_wp_claim) emits exactly these bytes.
fn trust_formula_body_bound_ge_refl() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "let",
            "name": "result",
            "sort": "int",
            "value": {"var": "x"},
            "body": {"op": "ge", "lhs": {"var": "result"}, "rhs": {"var": "x"}}
        }
    }"#
}

/// The FALSE variant: `ensures result > x { x }` body-binds to `x > x`, which
/// never holds — the verifier must NOT report Verified.
fn trust_formula_body_bound_gt_refl_false() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "let",
            "name": "result",
            "sort": "int",
            "value": {"var": "x"},
            "body": {"op": "gt", "lhs": {"var": "result"}, "rhs": {"var": "x"}}
        }
    }"#
}

fn trust_formula_linear_assumption_atom() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}}
    }"#
}

fn trust_formula_linear_assertion_atom() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "gt",
            "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
            "rhs": {"int": 0}
        }
    }"#
}

fn native_bundle_with_trust_wp_formula(formula: ProofFormula) -> NativeVerificationBundle {
    native_bundle_with_trust_wp_formula_and_mode(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
    )
}

fn native_bundle_with_trust_wp_formula_and_mode(
    formula: ProofFormula,
    mode: TrustWpVerificationMode,
) -> NativeVerificationBundle {
    let semantic_identity = format!("{}\0{}", formula.schema, formula.payload);
    let mut module = Module::new("trust_wp_trust_ir_native_direct");
    let func_ty = module.add_func_type(FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: false,
    });
    let mut function = Function::new(
        FuncId::new(0),
        "demo::verified_from_tmir_native",
        func_ty,
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(0))
        .with_span(SourceSpan {
            file: 3,
            line: 17,
            col: 11,
        }),
    );
    function.blocks.push(entry);
    module.add_function(function);
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "trust-wp proves the tMIR-carried postcondition",
        )
        .with_formula(formula)
        .with_function(FuncId::new(0))
        .with_source(
            ProofObligationSourceIdentity::new(
                "rust:demo::verified_from_tmir_native",
                "assertion:0",
            )
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:trust-wp:postcondition:0".to_string(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-wp.native-test.public-obligation.v1",
                    semantic_identity.as_bytes(),
                ),
            }),
        ),
    );

    let module_digest = module.stable_digest();

    let mut lineage_node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::SolverAdapter,
            "trust-ir-native-to-trust-wp",
            "tMIR",
            "native-request-schema-v1",
        ),
        digest(0x11),
        module_digest,
    );
    lineage_node.obligations.push(ProofId::new(0));

    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lineage_node],
        roots: vec![ProofLineageId::new(0)],
    };

    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::TrustIrModule,
        module_digest,
        module,
        lineage,
    );
    attach_schema_v2_compiler_facts(&mut bundle);
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(trust_wp_request(mode)));
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

fn refresh_native_bundle_module_identity(bundle: &mut NativeVerificationBundle) {
    let digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = digest;
    for node in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&node.id) {
            node.target_module = digest;
        }
    }
}

fn attach_schema_v2_compiler_facts(bundle: &mut NativeVerificationBundle) {
    let pair_struct = StructId::new(0);
    bundle.module.add_struct(StructDef {
        id: pair_struct,
        name: "PairI64".to_string(),
        fields: vec![FieldDef {
            name: "value".to_string(),
            ty: Ty::I64,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
    });
    let u8_ty = bundle.module.add_type(Ty::U8);
    let pair_layout = bundle
        .module
        .ty_layout_shape(&Ty::Struct(pair_struct))
        .expect("test struct layout is valid");
    let slice_layout = PointerLayoutShape::fat(
        bundle.module.pointer_bits(),
        PointerMetadataShape::SliceLen { elem: u8_ty },
    );

    bundle.compiler_facts.adt_layouts.push(NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(0),
        ty: Ty::Struct(pair_struct),
        layout: pair_layout,
        enum_layout: None,
    });
    bundle
        .compiler_facts
        .fat_pointers
        .push(NativeFatPointerFact {
            id: NativeCompilerFactId::new(1),
            ty: Ty::FatPtr(FatPtrKind::Slice(u8_ty)),
            layout: slice_layout,
        });
    bundle.compiler_facts.casts.push(NativeCastFact {
        id: NativeCompilerFactId::new(2),
        function: FuncId::new(0),
        result: None,
        op: CastOp::ZExt,
        source_ty: Ty::I32,
        target_ty: Ty::I64,
        evidence: CastLayoutEvidence::NotLayoutSensitive,
        span: Some(SourceSpan {
            file: 3,
            line: 17,
            col: 11,
        }),
        obligations: vec![ProofId::new(0)],
    });
    bundle
        .compiler_facts
        .monomorphizations
        .push(NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "demo::verified_from_tmir_native".to_string(),
            symbol: "_RNvCtrust_wp_trust_ir_native_direct_verified_from_tmir_native".to_string(),
            generic_args: Vec::new(),
            function: Some(FuncId::new(0)),
            stable_digest: digest(0x55),
        });
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: "vc:trust-wp:postcondition:0".to_string(),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan {
                file: 3,
                line: 17,
                col: 11,
            }),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::Postcondition,
            monomorphization: Some(NativeMonomorphizationId::new(0)),
            facts: vec![
                NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(0)),
                NativeCompilerFactRef::FatPointer(NativeCompilerFactId::new(1)),
                NativeCompilerFactRef::Cast(NativeCompilerFactId::new(2)),
                NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0)),
            ],
        });
}

fn trust_wp_request(mode: TrustWpVerificationMode) -> TrustWpNativeRequest {
    let span = SourceSpan {
        file: 3,
        line: 17,
        col: 11,
    };
    let mut provenance = NativeRequestProvenance::trust_wp(
        NativeToolIdentity::new("trust-wp")
            .with_version("native-schema-v2")
            .with_revision("0cbaad5b"),
    )
    .with_solver(
        NativeToolIdentity::new("ay")
            .with_version("0.9.0")
            .with_revision("solver-rev")
            .with_digest(digest(0x66)),
    )
    .with_replay(
        ProofReplayIdentity::new(
            "trust-wp",
            "trust-wp verify --native-bundle trust_wp_trust_ir_native_direct --function demo::verified_from_tmir_native",
        )
        .with_transcript_digest(digest(0x77)),
    );
    if mode == TrustWpVerificationMode::StrongestPostcondition {
        provenance = provenance.with_replay_context(
            NativeReplayContext::default()
                .with_atom(
                    NativeReplayAtom::assumption(
                        NativeReplayAtomId::new(0),
                        ProofFormula::new(
                            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
                            trust_formula_linear_assumption_atom(),
                        ),
                    )
                    .with_obligation(ProofId::new(0))
                    .with_span(span),
                )
                .with_atom(
                    NativeReplayAtom::assertion(
                        NativeReplayAtomId::new(1),
                        ProofFormula::new(
                            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
                            trust_formula_linear_assertion_atom(),
                        ),
                    )
                    .with_obligation(ProofId::new(0))
                    .with_assertion_id(NativeAssertionId::new(0))
                    .with_span(span),
                ),
        );
    }

    TrustWpNativeRequest {
        id: NativeRequestId::new(7),
        mode,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(0)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustWpRequestOptions::default(),
        diagnostics: NativeDiagnosticsPolicy::default(),
        provenance,
    }
}

fn assert_strongest_postcondition_obligation_metadata(obligation: &BundleObligation) {
    assert_native_request_origin_metadata(obligation);
    assert_native_replay_toolchain_metadata(obligation);
    assert_tmir_source_metadata(obligation);
    assert_native_replay_proof_context(obligation);
}

fn assert_native_request_origin_metadata(obligation: &BundleObligation) {
    let origin = obligation
        .metadata
        .native_origin
        .as_ref()
        .expect("typed native origin is preserved");
    // Pin the exact canonical origin schema spelling. trust-wp-core's STRICT
    // fail-closed native-origin gate (`validate_tmir_native_origin_metadata`
    // in crates/trust-wp-core/src/verify_bundle/types.rs) only engages for
    // schemas prefixed `tmir.native-verification-bundle.`; the historical
    // `trust-ir.` / `trust_ir.` spellings silently bypassed placeholder-solver
    // rejection and atom-binding checks. Never respell this literal without
    // moving core's gate in lockstep.
    assert_eq!(
        origin.schema,
        format!("tmir.native-verification-bundle.v{NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION}")
    );
    assert_eq!(origin.request_id, 7);
    assert_eq!(origin.function_id, 0);
    assert_eq!(origin.obligation_id, 0);
    assert_eq!(
        origin.mode,
        BundleNativeVerificationMode::StrongestPostcondition
    );
    assert_eq!(origin.lineage_roots, vec![0]);
    assert!(origin.tmir_module_digest.is_some());
    assert_eq!(
        obligation.location.as_ref().map(|span| span.file.as_str()),
        Some("trust-ir://file/3")
    );
    assert_eq!(
        obligation.metadata.tmir_source_span,
        Some(BundleTmirSourceSpan::new(3, 17, 11))
    );
}

fn assert_native_replay_toolchain_metadata(obligation: &BundleObligation) {
    let verifier = obligation
        .metadata
        .native_verifier
        .as_ref()
        .expect("typed verifier provenance is preserved");
    assert_eq!(verifier.name, "trust-wp");
    assert_eq!(verifier.version.as_deref(), Some("native-schema-v2"));
    assert_eq!(verifier.revision.as_deref(), Some("0cbaad5b"));

    let replay = obligation
        .metadata
        .native_replay
        .as_ref()
        .expect("typed replay identity is preserved");
    assert_eq!(replay.engine, "trust-wp");
    assert!(replay.invocation.contains("trust-wp verify"));
    assert_eq!(replay.transcript_digest.value, "77".repeat(32));

    assert_eq!(obligation.metadata.native_solvers.len(), 1);
    let solver = &obligation.metadata.native_solvers[0];
    assert_eq!(solver.name, "ay");
    assert_eq!(solver.version.as_deref(), Some("0.9.0"));
    assert_eq!(solver.revision.as_deref(), Some("solver-rev"));
    let expected_solver_digest = "66".repeat(32);
    assert_eq!(
        solver.digest.as_ref().map(|digest| digest.value.as_str()),
        Some(expected_solver_digest.as_str())
    );
}

fn assert_tmir_source_metadata(obligation: &BundleObligation) {
    let source = obligation
        .metadata
        .tmir_obligation_source
        .as_ref()
        .expect("typed tMIR obligation source is preserved");
    assert_eq!(source.cause, BundleTmirObligationCause::Postcondition);
    assert_eq!(source.function_id, Some(0));
    assert_eq!(source.assertion_id, Some(0));
    assert_eq!(source.monomorphization_id, Some(0));
    assert_eq!(source.compiler_fact_refs.len(), 4);
    assert!(source.compiler_fact_refs.iter().all(|fact_ref| fact_ref
        .digest
        .as_ref()
        .is_some_and(BundleDigest::is_hash_addressed)));
    assert!(
        source.compiler_fact_refs.iter().any(|fact_ref| {
            matches!(&fact_ref.kind, BundleTmirCompilerFactKind::Monomorphization)
                && fact_ref.id == 0
                && fact_ref
                    .digest
                    .as_ref()
                    .is_some_and(|digest| digest == &BundleDigest::new("sha256", "55".repeat(32)))
        }),
        "monomorphization fact should keep its producer-stable fact digest"
    );
}

fn assert_native_replay_proof_context(obligation: &BundleObligation) {
    assert_eq!(obligation.metadata.proof_context.assumptions.len(), 1);
    assert_eq!(obligation.metadata.proof_context.assertions.len(), 1);
    assert_eq!(
        obligation.metadata.proof_context.assumptions[0].role,
        BundleProofAtomRole::Assumption
    );
    assert_eq!(
        obligation.metadata.proof_context.assumptions[0].index, 0,
        "assumption atom keeps the first proof-context identity"
    );
    assert_eq!(
        obligation.metadata.proof_context.assumptions[0].native_replay_atom_id,
        Some(0)
    );
    assert_eq!(
        obligation.metadata.proof_context.assumptions[0].native_obligation_id,
        Some(0)
    );
    assert_eq!(
        obligation.metadata.proof_context.assertions[0].role,
        BundleProofAtomRole::Assertion
    );
    assert_eq!(
        obligation.metadata.proof_context.assertions[0].index, 1,
        "assertion atom identity must not alias the assumption atom"
    );
    assert_eq!(
        obligation.metadata.proof_context.assertions[0].native_replay_atom_id,
        Some(1)
    );
    assert_eq!(
        obligation.metadata.proof_context.assertions[0].native_assertion_id,
        Some(0)
    );
    assert_eq!(
        obligation.metadata.proof_context.assumptions[0]
            .claim
            .format,
        BundleClaimFormat::TrustFormulaV1
    );
    assert!(
        obligation.metadata.proof_context.assertions[0]
            .claim
            .digest
            .as_ref()
            .is_some_and(BundleDigest::is_hash_addressed),
        "tMIR replay atom payload digest is preserved on the proof atom"
    );
}

#[test]
fn test_trust_ir_native_trust_wp_request_verifies_directly() {
    let bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));

    let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect("typed trust-wp request converts");
    assert_eq!(requests.len(), 1);
    assert_eq!(
        requests[0].bundle_id,
        "trust-ir-native:trust_wp_trust_ir_native_direct:trust-wp:7"
    );
    assert_eq!(requests[0].obligations.len(), 1);
    assert_eq!(
        requests[0].obligations[0].claim.format,
        BundleClaimFormat::TrustFormulaV1
    );

    let results = verify_trust_ir_native_bundle(&bundle).expect("typed trust-wp request verifies");

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
    assert_eq!(results[0].exit_code(), 0);
    assert_eq!(results[0].obligation_results.len(), 1);
}

#[test]
fn test_trust_ir_native_trust_wp_strongest_postcondition_request_verifies_directly() {
    let bundle = native_bundle_with_trust_wp_formula_and_mode(
        ProofFormula::new(
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            trust_formula_linear_variable(),
        ),
        TrustWpVerificationMode::StrongestPostcondition,
    );

    let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect("typed trust-wp request converts");
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].obligations.len(), 1);
    assert_eq!(
        requests[0].obligations[0].claim.format,
        BundleClaimFormat::TrustFormulaV1
    );
    let obligation = &requests[0].obligations[0];
    assert_strongest_postcondition_obligation_metadata(obligation);

    let results = verify_trust_ir_native_bundle(&bundle)
        .expect("strongest-postcondition trust-wp request verifies");

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
    assert!(results[0].is_verified());
    replay_verify_bundle_result_evidence(&requests[0], &results[0])
        .expect("tMIR native aggregate evidence replays");
    assert_eq!(results[0].exit_code(), 0);
    assert_eq!(results[0].obligation_results.len(), 1);
    let BundleObligationStatus::Verified { evidence } = &results[0].obligation_results[0].status
    else {
        panic!("expected verified strongest-postcondition obligation");
    };
    assert!(evidence.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::RequestDigest && artifact.has_stable_identity()
    }));
    assert!(
        evidence
            .artifacts
            .iter()
            .all(|artifact| artifact.has_transport() && artifact.inline_bytes_digest_matches()),
        "tMIR native trust-wp evidence should expose digest-checked transport bytes"
    );
    let BundleResultMetadata {
        solver: Some(solver),
        evidence: Some(evidence_metadata),
        ..
    } = &results[0].obligation_results[0].metadata
    else {
        panic!("expected typed solver/evidence metadata");
    };
    assert_eq!(solver.engine, "trust-wp-core.native-pure-replay");
    assert_eq!(solver.claim_format, "TrustFormulaV1");
    assert_eq!(solver.assumptions, 1);
    assert_eq!(solver.assertions, 1);
    assert_eq!(evidence_metadata.artifact_count, evidence.artifacts.len());
}

#[test]
fn test_trust_ir_native_origin_schema_engages_core_strict_native_gate() {
    let bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));

    let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect("typed trust-wp request converts");
    let request = requests
        .into_iter()
        .next()
        .expect("bundle produces one verify request");

    // The emitted request must pass trust-wp-core's strict schema gate as-is.
    let diagnostics = request.validation_diagnostics();
    assert!(
        diagnostics.is_empty(),
        "trust-wp-lib emission fails core validation: {diagnostics:?}"
    );

    // And the strict tMIR native-origin gate must actually ENGAGE for the
    // emitted schema spelling: stripping metadata the gate requires has to
    // fail closed. Under the bypassed `trust-ir.` spelling this produced no
    // diagnostics because `validate_tmir_native_origin_metadata` returned
    // early on the prefix mismatch.
    let mut stripped = request;
    stripped.obligations[0]
        .metadata
        .native_origin
        .as_mut()
        .expect("typed native origin is preserved")
        .lineage_roots
        .clear();
    let diagnostics = stripped.validation_diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "obligation.metadata.native_origin.lineage_roots"),
        "core strict native-origin gate did not engage for the emitted schema: {diagnostics:?}"
    );
}

#[test]
fn test_trust_ir_native_trust_wp_records_response_evidence_artifacts_over_bytes() {
    let mut bundle = native_bundle_with_trust_wp_formula_and_mode(
        ProofFormula::new(
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            trust_formula_linear_variable(),
        ),
        TrustWpVerificationMode::StrongestPostcondition,
    );

    let output = verify_trust_ir_native_bundle_and_record_evidence(&mut bundle)
        .expect("verified trust-wp request should record native response evidence");

    assert_eq!(output.results.len(), 1);
    assert_eq!(output.results[0].status, VerifyBundleStatus::Verified);
    assert_eq!(output.evidence_bundles.len(), 1);
    assert_eq!(bundle.evidence_bundles, output.evidence_bundles);
    assert!(
        bundle.validate().is_ok(),
        "recorded trust-wp NativeEvidenceBundle should validate: {:?}",
        bundle.validate().err()
    );

    let evidence = &bundle.evidence_bundles[0];
    assert!(evidence.artifacts().iter().any(|artifact| {
        artifact.kind == NativeEvidenceArtifactKind::TrustWpVerificationCondition
    }));
    assert!(evidence
        .artifacts()
        .iter()
        .any(|artifact| artifact.kind == NativeEvidenceArtifactKind::TrustWpReplayTrace));
    assert!(evidence
        .artifacts()
        .iter()
        .any(|artifact| artifact.kind == NativeEvidenceArtifactKind::ReplayTranscript));

    for artifact in evidence.artifacts() {
        let key = trust_ir::NativeEvidenceArtifactAttachmentKey::for_artifact(
            evidence.request(),
            artifact,
        );
        let resolution =
            bundle.resolve_evidence_artifact_attachment(key, &output.artifact_attachments);
        assert!(
            resolution.is_authoritative(),
            "artifact {} should resolve to authoritative bytes: {:?}",
            artifact.name,
            resolution
        );
        assert_eq!(resolution.report.actual_digest, Some(artifact.digest));
        assert!(resolution
            .authoritative_bytes()
            .is_some_and(|bytes| !bytes.is_empty()));
    }

    let proof_check_transcript = output
        .artifact_attachments
        .iter()
        .find(|attachment| {
            attachment.key.kind == NativeEvidenceArtifactKind::ReplayTranscript
                && String::from_utf8_lossy(&attachment.bytes)
                    .contains("trust-wp.native-pure-proof-check-transcript.v1")
        })
        .expect("trust-wp response should attach a proof-check transcript");
    let transcript_text = String::from_utf8_lossy(&proof_check_transcript.bytes);
    assert!(transcript_text.contains("actual-digest=sha256:"));
    assert_ne!(
        hex_digest(&proof_check_transcript.key.digest.bytes),
        "77".repeat(32),
        "response transcript digest should be derived from actual transcript bytes, not the request fixture placeholder"
    );
}

#[test]
fn test_trust_ir_native_bundle_binds_all_compiler_fact_refs_to_stable_digests() {
    let bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let expected_compiler_facts_digest =
        bundle_digest_from_tmir(bundle.compiler_facts.stable_digest());
    let expected_monomorphization_digest =
        bundle_digest_from_tmir(bundle.compiler_facts.monomorphizations[0].stable_digest);

    let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect("typed trust-wp request converts");
    let source = requests[0].obligations[0]
        .metadata
        .tmir_obligation_source
        .as_ref()
        .expect("typed tMIR source metadata is preserved");

    for (kind, id) in [
        (BundleTmirCompilerFactKind::AdtLayout, 0),
        (BundleTmirCompilerFactKind::FatPointer, 1),
        (BundleTmirCompilerFactKind::Cast, 2),
    ] {
        let fact_ref = source
            .compiler_fact_refs
            .iter()
            .find(|fact_ref| fact_ref.kind.as_str() == kind.as_str() && fact_ref.id == id)
            .expect("schema-v2 source fact ref is preserved");
        assert_eq!(
            fact_ref.digest.as_ref(),
            Some(&expected_compiler_facts_digest),
            "non-monomorphization compiler fact refs bind the tMIR compiler-facts table digest"
        );
    }

    let monomorphization_ref = source
        .compiler_fact_refs
        .iter()
        .find(|fact_ref| {
            matches!(&fact_ref.kind, BundleTmirCompilerFactKind::Monomorphization)
                && fact_ref.id == 0
        })
        .expect("monomorphization fact ref is preserved");
    assert_eq!(
        monomorphization_ref.digest.as_ref(),
        Some(&expected_monomorphization_digest),
        "monomorphization fact refs keep their producer-stable fact digest"
    );

    let results = verify_trust_ir_native_bundle(&bundle).expect("typed trust-wp request verifies");
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
}

#[test]
fn test_trust_ir_native_trust_wp_abduction_request_fails_closed_before_verification() {
    let bundle = native_bundle_with_trust_wp_formula_and_mode(
        ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, trust_formula_true()),
        TrustWpVerificationMode::Abduction,
    );

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("abduction mode is not a replay-only verifier mode");

    assert!(matches!(
        err,
        TrustIrNativeBundleError::UnsupportedTrustWpMode {
            request_id: 7,
            mode: TrustIrTrustWpMode::Abduction,
            reason: TrustIrUnsupportedModeReason::RequiresSynthesizerResult,
        }
    ));
}

#[test]
fn test_trust_ir_native_bundle_rejects_missing_solver_identities_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] else {
        panic!("expected trust-wp request");
    };
    request.provenance.solvers.clear();

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("missing solver identities must fail trust-wp admission");

    assert!(matches!(
        err,
        TrustIrNativeBundleError::MissingSolverIdentities { request_id: 7 }
    ));
}

#[test]
fn test_trust_ir_native_bundle_rejects_empty_solver_identity_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] else {
        panic!("expected trust-wp request");
    };
    request.provenance.solvers = vec![NativeToolIdentity::default()];

    bundle
        .validate()
        .expect("generic tMIR validation accepts the default unknown placeholder identity");
    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("placeholder solver identities must fail trust-wp admission");

    assert!(matches!(
        err,
        TrustIrNativeBundleError::EmptySolverIdentity {
            request_id: 7,
            solver_index: 0,
        }
    ));
}

#[test]
fn test_trust_ir_native_bundle_rejects_missing_replay_identity_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] else {
        panic!("expected trust-wp request");
    };
    request.provenance.replay = None;

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("native trust-wp admission requires replay identity");

    assert!(matches!(
        err,
        TrustIrNativeBundleError::MissingReplayIdentity { request_id: 7 }
    ));
}

#[test]
fn test_trust_ir_native_bundle_rejects_missing_replay_transcript_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] else {
        panic!("expected trust-wp request");
    };
    request
        .provenance
        .replay
        .as_mut()
        .expect("replay identity")
        .transcript_digest = None;

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("native trust-wp admission requires replay transcript digests");

    assert!(matches!(
        err,
        TrustIrNativeBundleError::MissingReplayTranscriptDigest { request_id: 7 }
    ));
}

#[test]
fn test_trust_ir_native_bundle_rejects_mismatched_expected_verifier_identity() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] else {
        panic!("expected trust-wp request");
    };
    request.provenance.expected_verifier =
        NativeToolIdentity::new("trust-mc").with_version("chc-v1");

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("mismatched verifier identity must fail trust-wp admission");

    let TrustIrNativeBundleError::MismatchedExpectedVerifierIdentity {
        request_id,
        expected,
        found,
    } = err
    else {
        panic!("expected mismatched expected verifier identity error");
    };
    assert_eq!(request_id, 7);
    assert_eq!(expected, "trust-wp");
    assert_eq!(found, "trust-mc@chc-v1");
}

#[test]
fn test_trust_ir_native_trust_wp_request_preserves_opaque_smtlib_fail_closed() {
    let bundle =
        native_bundle_with_trust_wp_formula(ProofFormula::smtlib2("(assert true)", "Bool"));

    let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect("typed trust-wp request converts");
    assert_eq!(
        requests[0].obligations[0].claim.format,
        BundleClaimFormat::SmtLib2
    );

    let results =
        verify_trust_ir_native_bundle(&bundle).expect("typed trust-wp request is consumed");

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, VerifyBundleStatus::Invalid);
    assert!(results[0]
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == "obligation.claim.format"));
}

#[test]
fn test_trust_ir_native_bundle_rejects_stale_module_digest_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.trust_ir_module_digest = digest(0x99);

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("stale tMIR digest must fail native bundle validation");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected InvalidNativeBundle for stale digest");
    };
    assert!(errors.iter().any(|error| error.contains("digest")));
}

#[test]
fn test_trust_ir_native_bundle_rejects_stale_compiler_fact_reference_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.compiler_facts.obligation_sources[0].facts =
        vec![NativeCompilerFactRef::Monomorphization(
            NativeMonomorphizationId::new(99),
        )];

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("stale tMIR compiler fact reference must fail validation");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected InvalidNativeBundle for stale compiler fact reference");
    };
    assert!(errors
        .iter()
        .any(|error| error.contains("unknown compiler fact")));
}

#[test]
fn test_trust_ir_native_bundle_rejects_missing_obligation_source_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.compiler_facts.obligation_sources.clear();

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("trust-wp native replay requires typed obligation source metadata");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected generic tMIR validation to reject the missing source map");
    };
    assert!(errors
        .iter()
        .any(|error| error.contains("obligation") && error.contains("source")));
}

#[test]
fn test_trust_ir_native_bundle_rejects_unbound_monomorphization_fact_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.compiler_facts.obligation_sources[0].facts.clear();

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("trust-wp native replay requires digest-bound monomorphization facts");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected generic tMIR validation to reject the unbound monomorphization fact");
    };
    assert!(errors
        .iter()
        .any(|error| error.contains("monomorphization")));
}

#[test]
fn test_trust_ir_native_bundle_rejects_source_cause_kind_drift_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.compiler_facts.obligation_sources[0].cause = NativeObligationCause::Precondition;

    bundle
        .validate()
        .expect("generic tMIR validation permits source cause/kind drift");
    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("trust-wp native replay requires source cause/kind consistency");

    let TrustIrNativeBundleError::MismatchedObligationSourceCause {
        request_id,
        obligation_id,
        obligation_kind,
        source_cause,
    } = err
    else {
        panic!("expected source cause/kind drift rejection");
    };
    assert_eq!(request_id, 7);
    assert_eq!(obligation_id, 0);
    assert_eq!(obligation_kind, "postcondition");
    assert_eq!(source_cause, "precondition");
}

#[test]
fn test_trust_ir_native_bundle_rejects_missing_source_function_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.compiler_facts.obligation_sources[0].function = None;

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("trust-wp native replay requires source functions to bind request functions");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected generic tMIR validation to reject the missing source function");
    };
    assert!(errors
        .iter()
        .any(|error| error.contains("function") && error.contains("obligation")));
}

#[test]
fn test_trust_ir_native_bundle_rejects_missing_source_span_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    bundle.compiler_facts.obligation_sources[0].span = None;

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("trust-wp native replay requires source spans to bind evidence");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected generic tMIR validation to reject the missing source span");
    };
    assert!(errors.iter().any(|error| error.contains("source span")));
}

#[test]
fn test_trust_ir_native_bundle_rejects_stale_trust_wp_lineage_root_before_verification() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let current_digest = bundle.trust_ir_module_digest;
    let stale_digest = digest(0x33);
    let mut current_root = bundle.lineage.nodes[0].clone();

    bundle.lineage.nodes[0].target_module = stale_digest;
    current_root.id = ProofLineageId::new(1);
    current_root.source_module = digest(0x44);
    current_root.target_module = current_digest;
    bundle.lineage.nodes.push(current_root);
    bundle.lineage.roots.push(ProofLineageId::new(1));

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("trust-wp request root must target the current tMIR digest");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected generic tMIR validation to reject stale trust-wp lineage roots");
    };
    assert!(errors
        .iter()
        .any(|error| error.contains("lineage root") && error.contains("target")));
}

/// Trust #23 conformance pin (positive): the compiler's body-bound golden
/// envelope for `ensures result >= x { x }` VERIFIES through the aggregate
/// bundle verifier — the sibling's let-inlining + reflexive-comparison rule
/// proves `x >= x` for all valuations.
#[test]
fn test_trust_ir_native_body_bound_ge_refl_verifies() {
    let bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_body_bound_ge_refl(),
    ));

    let results = verify_trust_ir_native_bundle(&bundle)
        .expect("body-bound ge_refl envelope converts and verifies");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
    assert_eq!(results[0].exit_code(), 0);
}

/// Trust #23 conformance pin (falsification): the FALSE body-bound envelope
/// (`ensures result > x { x }` == `x > x`) must NOT verify. A Verified here
/// would be a false proof — the load-bearing refusal for the whole lowering
/// wire.
#[test]
fn test_trust_ir_native_body_bound_gt_refl_false_does_not_verify() {
    let bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_body_bound_gt_refl_false(),
    ));

    let results = verify_trust_ir_native_bundle(&bundle)
        .expect("false body-bound envelope converts; the verdict must be non-Verified");
    assert_eq!(results.len(), 1);
    assert_ne!(
        results[0].status,
        VerifyBundleStatus::Verified,
        "x > x must never verify — a Verified here is a false proof"
    );
    assert_ne!(results[0].exit_code(), 0);
}
