#![cfg(feature = "trust-ir-native")]
#[path = "body_contract/cases.rs"]
mod body_contract_cases;
#[path = "body_contract/compiler_memory.rs"]
mod compiler_memory_cases;
#[path = "body_contract/explicit_branches.rs"]
mod explicit_branch_cases;
#[path = "body_contract/shared_codec_sp.rs"]
mod shared_codec_sp;
#[path = "body_contract/translation_capabilities.rs"]
mod translation_capability_cases;
#[path = "body_contract/u64_calls.rs"]
mod u64_call_cases;
#[path = "body_contract/unsigned_division.rs"]
mod unsigned_division_cases;
#[path = "body_contract/unsigned_select.rs"]
mod unsigned_select_cases;
#[path = "body_contract/widthconv.rs"]
mod widthconv_cases;
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fmt::Write as _;

use trust_ir::{
    proof::{
        clause_typing::ClauseTypingError, ClauseBinding, ClausePlace, ClauseSort, SpecObligationRef,
    },
    signature_abi::{
        AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiFrontend, AbiPassMode,
        AbiRegister, AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
    },
    ty::TypeOrigin,
    Block, BlockId, CallingConv, CastLayoutEvidence, CastOp, Constant, Endianness, FatPtrKind,
    FieldDef, FuncId, FuncTy, Function, Inst, InstrNode, Module, NativeAdapterInput,
    NativeAdtLayoutFact, NativeAssertionId, NativeBundleProducer, NativeCastFact,
    NativeCompilerFactId, NativeCompilerFactRef, NativeDiagnosticsPolicy,
    NativeEvidenceArtifactKind, NativeFatPointerFact, NativeMonomorphizationFact,
    NativeMonomorphizationId, NativeObligationCause, NativeObligationSource, NativeReplayAtom,
    NativeReplayAtomId, NativeReplayContext, NativeRequestId, NativeRequestProvenance,
    NativeToolIdentity, NativeVerificationBundle, NativeVerificationRequest, ObligationKind,
    PointerLayoutShape, PointerMetadataShape, ProofDigest, ProofFormula, ProofId, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofObligation, ProofObligationSourceIdentity,
    ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
    PublicObligationIdentity, SourceSpan, StructDef, StructId, StructPassingPolicy, StructRepr,
    TargetInfo, TrustWpNativeRequest, TrustWpRequestOptions, TrustWpVerificationMode, Ty, ValueId,
    NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION,
};
use trust_wp_lib::{
    replay_verify_bundle_result_evidence, trust_ir_native_bundle_to_verify_requests,
    verify_trust_ir_native_bundle, verify_trust_ir_native_bundle_and_record_evidence, BundleClaim,
    BundleClaimFormat, BundleDigest, BundleNativeVerificationMode, BundleObligation,
    BundleObligationKind, BundleObligationStatus, BundleProofAtomRole, BundleResultMetadata,
    BundleTmirCompilerFactKind, BundleTmirObligationCause, BundleTmirSourceSpan,
    EvidenceArtifactKind, TrustIrClauseCarrier, TrustIrNativeBundleError, TrustIrTrustWpMode,
    TrustIrUnsupportedClauseBindingReason, TrustIrUnsupportedModeReason,
    TrustIrUnsupportedObligationKindReason, TrustWpLibError, VerifyBundleStatus,
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
    native_bundle_with_signature(formula, mode, Vec::new(), Vec::new())
}

fn native_bundle_with_signature(
    formula: ProofFormula,
    mode: TrustWpVerificationMode,
    params: Vec<Ty>,
    returns: Vec<Ty>,
) -> NativeVerificationBundle {
    // The legacy signature: it records no source ABI placement, so its slots
    // are the function's own parameters and results.
    native_bundle_with_func_ty(formula, mode, FuncTy::unrecorded(params, returns, false))
}

fn native_bundle_with_func_ty(
    formula: ProofFormula,
    mode: TrustWpVerificationMode,
    signature: FuncTy,
) -> NativeVerificationBundle {
    let semantic_identity = format!("{}\0{}", formula.schema, formula.payload);
    let mut module = Module::new("trust_wp_trust_ir_native_direct");
    let func_ty = module
        .add_func_type(signature)
        .expect("add_func_type: test fixture");
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
    module
        .try_add_function(function)
        .expect("try_add_function: test fixture");
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
        // The fixture is the image of no source definition, so it claims no
        // nominal key and compares structurally.
        origin: None,
    });
    let u8_ty = bundle
        .module
        .add_type(Ty::U8)
        .expect("add_type: test fixture");
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
    let context = (mode == TrustWpVerificationMode::StrongestPostcondition).then(|| {
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
            )
    });
    trust_wp_request_with_replay_context(mode, context)
}

fn trust_wp_request_with_replay_context(
    mode: TrustWpVerificationMode,
    context: Option<NativeReplayContext>,
) -> TrustWpNativeRequest {
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
    if let Some(context) = context {
        provenance = provenance.with_replay_context(context);
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
    assert!(source.compiler_fact_refs.iter().all(|fact_ref| {
        fact_ref
            .digest
            .as_ref()
            .is_some_and(BundleDigest::is_hash_addressed)
    }));
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
fn test_trust_ir_native_producer_identity_binds_replay_without_granting_credit() {
    for (producer, expected_name) in [
        (NativeBundleProducer::TRust, "tRust"),
        (NativeBundleProducer::TSwift, "tSwift"),
        (NativeBundleProducer::TC, "tC"),
        (NativeBundleProducer::TrustIr, "TrustIr"),
        (NativeBundleProducer::Clean, "Clean"),
    ] {
        let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            trust_formula_true(),
        ));
        bundle.producer = producer;
        let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
            .expect("the native request retains its producer identity");
        assert_eq!(requests.len(), 1);
        assert_eq!(requests[0].producer.name, expected_name);
        let results =
            verify_trust_ir_native_bundle(&bundle).expect("the closed true obligation verifies");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].status, VerifyBundleStatus::Verified);
        replay_verify_bundle_result_evidence(&requests[0], &results[0])
            .expect("evidence replays against its own producer");

        // Producer identity is part of the request, so relabeling an otherwise
        // identical request cannot reuse the original verification evidence.
        let mut relabeled = requests[0].clone();
        relabeled.producer.name = if expected_name == "Clean" {
            "tRust"
        } else {
            "Clean"
        }
        .into();
        replay_verify_bundle_result_evidence(&relabeled, &results[0])
            .expect_err("another producer must re-earn the verdict");

        let mut false_bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            r#"{"schema":"trust-wp.trust-formula.v1","variables":[],"body":{"bool":false}}"#,
        ));
        false_bundle.producer = producer;
        let refused = verify_trust_ir_native_bundle(&false_bundle)
            .expect("the false obligation returns a verdict");
        assert_eq!(refused.len(), 1);
        assert_ne!(refused[0].status, VerifyBundleStatus::Verified);
    }
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

/// A definition's nominal key is part of the module identity a verdict rests
/// on: two structurally equal definitions under different keys are different
/// types, so stamping a key the digest was not taken over is a stale module.
fn pair_struct_type_origin() -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: 0x5452_5553_545f_5750,
        def_path_hash: [0x5a; 16],
        args_digest: digest(0x61),
    }
}

fn stamp_pair_struct_origin(bundle: &mut NativeVerificationBundle) {
    let pair = bundle
        .module
        .structs
        .iter_mut()
        .find(|def| def.name == "PairI64")
        .expect("the schema-v2 fixture declares PairI64");
    assert_eq!(pair.origin, None, "the fixture starts unkeyed");
    pair.origin = Some(pair_struct_type_origin());
}

#[test]
fn test_trust_ir_native_bundle_rejects_a_type_origin_the_module_digest_does_not_cover() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    stamp_pair_struct_origin(&mut bundle);

    let err = trust_ir_native_bundle_to_verify_requests(&bundle)
        .expect_err("a nominal key stamped after the digest is a stale module");

    let TrustIrNativeBundleError::InvalidNativeBundle { errors } = err else {
        panic!("expected InvalidNativeBundle for a key the module digest does not cover");
    };
    assert!(errors.iter().any(|error| error.contains("digest")));
}

#[test]
fn test_trust_ir_native_keyed_definition_verifies_once_the_module_digest_covers_it() {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        trust_formula_true(),
    ));
    let unkeyed_digest = bundle.trust_ir_module_digest;
    stamp_pair_struct_origin(&mut bundle);
    refresh_native_bundle_module_identity(&mut bundle);
    assert_ne!(
        bundle.trust_ir_module_digest, unkeyed_digest,
        "the nominal key moves the module identity"
    );

    let results = verify_trust_ir_native_bundle(&bundle).expect("a keyed module verifies");

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
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

fn native_bundle_with_obligation_kind(
    formula: &'static str,
    kind: ObligationKind,
    cause: NativeObligationCause,
) -> NativeVerificationBundle {
    let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        formula,
    ));
    bundle.module.proof_obligations[0].kind = kind;
    bundle.compiler_facts.obligation_sources[0].cause = cause;
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

/// The kinds trust-ir added after the panic-class split each get a named
/// mapping: `Termination` lands on the core kind of the same name, the others
/// keep a faithful label instead of collapsing into one shared placeholder.
/// Naming a kind admits it to core, not to a verdict: native pure replay owns
/// only precondition, postcondition and loop-invariant obligations, so even a
/// `true` formula under these kinds comes back `Unsupported`. Causes are the
/// ones the producer emits for each kind.
#[test]
fn test_trust_ir_native_named_kinds_map_faithfully_and_stay_unsupported() {
    for (kind, cause, expected) in [
        (
            ObligationKind::GiveBackRefinement,
            NativeObligationCause::BorrowCheck,
            BundleObligationKind::Other("give_back_refinement".to_string()),
        ),
        (
            ObligationKind::Termination,
            NativeObligationCause::Panic,
            BundleObligationKind::Termination,
        ),
        (
            ObligationKind::Ownership,
            NativeObligationCause::Panic,
            BundleObligationKind::Other("ownership".to_string()),
        ),
    ] {
        let label = kind.to_string();
        let bundle = native_bundle_with_obligation_kind(trust_formula_true(), kind, cause);

        let requests = trust_ir_native_bundle_to_verify_requests(&bundle)
            .unwrap_or_else(|err| panic!("{label} converts: {err}"));
        assert_eq!(requests[0].obligations[0].kind, expected, "{label}");

        let results = verify_trust_ir_native_bundle(&bundle)
            .unwrap_or_else(|err| panic!("{label} reaches core: {err}"));
        assert_eq!(
            results[0].status,
            VerifyBundleStatus::Unsupported,
            "{label}: a kind native replay does not own must never verify"
        );
        assert_ne!(results[0].exit_code(), 0, "{label}");
    }
}

/// A producer-namespaced kind is refused by name before any solver runs: its
/// namespace is authority-bearing and trust-wp pins no namespace list, so a
/// true formula must not buy it a verdict either.
#[test]
fn test_trust_ir_native_custom_kind_is_refused_before_verification() {
    let bundle = native_bundle_with_obligation_kind(
        trust_formula_true(),
        ObligationKind::Custom {
            namespace: "trust.concurrency".to_string(),
            name: "data_race_free".to_string(),
        },
        NativeObligationCause::Other,
    );

    let expected = TrustIrNativeBundleError::UnsupportedObligationKind {
        request_id: 7,
        obligation_id: 0,
        kind: "custom:trust.concurrency/data_race_free".to_string(),
        reason: TrustIrUnsupportedObligationKindReason::UnpinnedCustomNamespace,
    };
    assert_eq!(
        trust_ir_native_bundle_to_verify_requests(&bundle)
            .expect_err("a custom kind has no admission rule"),
        expected
    );
    assert!(
        verify_trust_ir_native_bundle(&bundle).is_err(),
        "the verify entry point refuses the same bundle"
    );
}

// ---- Clause bindings and spec backrefs --------------------------------------
//
// trust-wp reads every formula name as an unbounded Int or a Bool over the
// request function's own parameters and results. A binding or spec backref
// that says the clause means something else must be refused by name: the
// formula below, `x + 1 > x` over `int`, is valid as trust-wp reads it and
// false at `u64::MAX`.

fn trust_formula_x_plus_one_gt_x() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "gt",
            "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
            "rhs": {"var": "x"}
        }
    }"#
}

fn trust_formula_x_gt_x_false() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {"op": "gt", "lhs": {"var": "x"}, "rhs": {"var": "x"}}
    }"#
}

fn trust_formula_x_declared_bool() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "bool"}],
        "body": {"op": "implies", "lhs": {"var": "x"}, "rhs": {"var": "x"}}
    }"#
}

/// One name per admitted place kind: a parameter, a bool parameter, the value
/// behind a `&mut` at exit, and the result slot.
fn trust_formula_every_admitted_place() -> &'static str {
    r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [
            {"name": "x", "sort": "int"},
            {"name": "b", "sort": "bool"},
            {"name": "m", "sort": "int"}
        ],
        "result": {"name": "r", "sort": "int"},
        "body": {
            "op": "and",
            "lhs": {
                "op": "gt",
                "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                "rhs": {"var": "x"}
            },
            "rhs": {
                "op": "and",
                "lhs": {"op": "implies", "lhs": {"var": "b"}, "rhs": {"var": "b"}},
                "rhs": {
                    "op": "and",
                    "lhs": {"op": "ge", "lhs": {"var": "m"}, "rhs": {"var": "m"}},
                    "rhs": {"op": "ge", "lhs": {"var": "r"}, "rhs": {"var": "r"}}
                }
            }
        }
    }"#
}

fn bound_formula(
    payload: &'static str,
    bindings: &[(&str, ClauseSort, ClausePlace)],
) -> ProofFormula {
    let mut formula = ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, payload);
    formula.bindings = bindings
        .iter()
        .map(|(name, sort, place)| {
            (
                (*name).to_string(),
                ClauseBinding {
                    sort: sort.clone(),
                    place: *place,
                },
            )
        })
        .collect();
    formula
}

/// `fn(x: u64, b: bool, m: &mut i32) -> u64`.
fn native_bundle_with_bound_signature(formula: ProofFormula) -> NativeVerificationBundle {
    native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::U64, Ty::Bool, Ty::RefMut(Box::new(Ty::I32))],
        vec![Ty::U64],
    )
}

fn assert_binding_refused(
    bundle: &NativeVerificationBundle,
    carrier: TrustIrClauseCarrier,
    name: &str,
    reason: TrustIrUnsupportedClauseBindingReason,
) {
    let expected = TrustIrNativeBundleError::UnsupportedClauseBinding {
        request_id: 7,
        obligation_id: 0,
        carrier,
        name: name.to_string(),
        reason,
    };
    assert_eq!(
        trust_ir_native_bundle_to_verify_requests(bundle)
            .expect_err("a binding trust-wp cannot read faithfully is refused before verification"),
        expected
    );
    assert!(
        verify_trust_ir_native_bundle(bundle).is_err(),
        "the verify entry point refuses the same bundle"
    );
}

fn assert_verified(bundle: &NativeVerificationBundle) {
    let results = verify_trust_ir_native_bundle(bundle).expect("admitted bindings convert");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
    assert_eq!(results[0].exit_code(), 0);
}

/// Measured false accept: a name bound to a spec-machine state variable was
/// verified as if it were an unconstrained integer.
#[test]
fn test_trust_ir_native_spec_var_binding_is_refused() {
    let place = ClausePlace::SpecVar { index: 0 };
    let bundle = native_bundle_with_trust_wp_formula(bound_formula(
        trust_formula_x_plus_one_gt_x(),
        &[("x", ClauseSort::Int, place)],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::SpecVariablePlace { place },
    );
}

/// Measured false accept: the primed successor-state spelling of the same.
#[test]
fn test_trust_ir_native_spec_var_next_binding_is_refused() {
    let place = ClausePlace::SpecVarNext { index: 0 };
    let bundle = native_bundle_with_trust_wp_formula(bound_formula(
        trust_formula_x_plus_one_gt_x(),
        &[("x", ClauseSort::Int, place)],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::SpecVariablePlace { place },
    );
}

/// Measured false accept: a Postcondition claiming to discharge a temporal
/// property of a machine the module does not carry. The temporal kinds are
/// refused the same way even though a backref is legal on them: trust-wp has
/// no temporal model, so the refusal does not depend on the reference
/// resolving.
#[test]
fn test_trust_ir_native_spec_backref_is_refused() {
    for (kind, cause) in [
        (
            ObligationKind::Postcondition,
            NativeObligationCause::Postcondition,
        ),
        (ObligationKind::Liveness, NativeObligationCause::Temporal),
        (
            ObligationKind::TemporalSafety,
            NativeObligationCause::Temporal,
        ),
    ] {
        let label = kind.to_string();
        let mut bundle =
            native_bundle_with_obligation_kind(trust_formula_x_plus_one_gt_x(), kind, cause);
        bundle.module.proof_obligations[0].spec = Some(SpecObligationRef::new(
            "no_such_machine",
            "no_such_property",
        ));
        refresh_native_bundle_module_identity(&mut bundle);

        let expected = TrustIrNativeBundleError::UnsupportedSpecObligation {
            request_id: 7,
            obligation_id: 0,
            machine: "no_such_machine".to_string(),
            temporal: "no_such_property".to_string(),
        };
        assert_eq!(
            trust_ir_native_bundle_to_verify_requests(&bundle)
                .expect_err("a spec backref names a property trust-wp cannot state"),
            expected,
            "{label}"
        );
        assert!(verify_trust_ir_native_bundle(&bundle).is_err(), "{label}");
    }
}

/// Measured false accept: `BitVec(64)` at a parameter the zero-parameter
/// function does not have. The place is refused first; the sort is refused on
/// its own in the next test.
#[test]
fn test_trust_ir_native_unresolvable_bitvec_param_binding_is_refused() {
    let place = ClausePlace::Param { index: 0 };
    let bundle = native_bundle_with_trust_wp_formula(bound_formula(
        trust_formula_x_plus_one_gt_x(),
        &[("x", ClauseSort::BitVec(64), place)],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::UnresolvedPlace {
            place,
            error: ClauseTypingError::ParamOutOfRange { index: 0, arity: 0 },
        },
    );
}

/// The width strip itself: `BitVec(64)` at a real `u64` parameter, where
/// trust-ir calls the reading faithful and trust-wp would still prove the
/// clause over unbounded Int. Every other sort trust-wp has no model for is
/// refused the same way.
#[test]
fn test_trust_ir_native_unmodeled_sort_at_resolvable_param_is_refused() {
    for sort in [
        ClauseSort::BitVec(64),
        ClauseSort::Float { eb: 11, sb: 53 },
        ClauseSort::RoundingMode,
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Int)),
        ClauseSort::Datatype {
            name: "Pair".to_string(),
            constructors: Vec::new(),
        },
    ] {
        let bundle = native_bundle_with_bound_signature(bound_formula(
            trust_formula_x_plus_one_gt_x(),
            &[("x", sort.clone(), ClausePlace::Param { index: 0 })],
        ));
        assert_binding_refused(
            &bundle,
            TrustIrClauseCarrier::Obligation,
            "x",
            TrustIrUnsupportedClauseBindingReason::UnmodeledSort { sort },
        );
    }
}

/// Places trust-ir's resolver gives no IR type, a `MutParamExit` of a
/// parameter that is not `&mut` and a `ParamPointeeEntry` of one that is not a
/// reference are refused with the resolver's own reason.
#[test]
fn test_trust_ir_native_unresolvable_places_are_refused() {
    for (place, error) in [
        (
            ClausePlace::World,
            ClauseTypingError::PlaceHasNoIrType(ClausePlace::World),
        ),
        // The v59 world epochs are ambient state, as the un-epoched world is.
        (
            ClausePlace::WorldPre,
            ClauseTypingError::PlaceHasNoIrType(ClausePlace::WorldPre),
        ),
        (
            ClausePlace::WorldPost,
            ClauseTypingError::PlaceHasNoIrType(ClausePlace::WorldPost),
        ),
        (
            ClausePlace::Unwind,
            ClauseTypingError::PlaceHasNoIrType(ClausePlace::Unwind),
        ),
        (
            ClausePlace::Value(ValueId::new(0)),
            ClauseTypingError::ValuePlaceUnsupported(ClausePlace::Value(ValueId::new(0))),
        ),
        (
            ClausePlace::MutParamExit { index: 0 },
            ClauseTypingError::MutParamExitNotMutable {
                index: 0,
                ty: Ty::U64,
            },
        ),
        // v62: the entry pointee of a by-value parameter has no referent.
        (
            ClausePlace::ParamPointeeEntry { index: 0 },
            ClauseTypingError::ParamPointeeNotReference {
                index: 0,
                ty: Ty::U64,
            },
        ),
        (
            ClausePlace::ResultSlot { index: 1 },
            ClauseTypingError::ResultOutOfRange { index: 1, arity: 1 },
        ),
    ] {
        let bundle = native_bundle_with_bound_signature(bound_formula(
            trust_formula_x_plus_one_gt_x(),
            &[("x", ClauseSort::Int, place)],
        ));
        assert_binding_refused(
            &bundle,
            TrustIrClauseCarrier::Obligation,
            "x",
            TrustIrUnsupportedClauseBindingReason::UnresolvedPlace { place, error },
        );
    }
}

/// `fn(x: (u64, u64)) -> u64` as a Rust producer lowers it: the pair travels
/// in two `u64` registers, so lowered parameter 0 carries bytes 0..8 of the
/// source argument and lowered parameter 1 bytes 8..16 (trust-ir v60's
/// `FuncTy::abi`). `abi` is the placement record, or `None` for the same
/// lowered slots with none recorded.
fn split_pair_signature(abi: bool) -> FuncTy {
    let lane = |source_offset: u64| AbiScalar {
        register: AbiRegister {
            class: AbiRegisterClass::Integer,
            bytes: 8,
        },
        source_offset,
        source_bytes: 8,
        value_bits: 64,
        attributes: AbiAttributes::default(),
    };
    let binding = |place: AbiBindingPlace, source_offset: u64| AbiBinding {
        place,
        source_offset,
        source_bytes: 8,
        carrier_offset: 0,
        carrier_bytes: 8,
    };
    let mut signature = FuncTy::unrecorded(vec![Ty::U64, Ty::U64], vec![Ty::U64], false);
    if abi {
        signature.abi = Some(SignatureAbi {
            target: AbiTarget {
                triple: "aarch64-apple-darwin".to_string(),
                data_layout: "e-m:o-p:64:64-i64:64-i128:128-n32:64-S128".to_string(),
                abi: "darwinpcs".to_string(),
                cpu: "apple-m1".to_string(),
                features: vec!["+neon".to_string()],
                target_spec: format!("sha256:{}", "a".repeat(64)),
                pointer_bytes: 8,
                little_endian: true,
            },
            frontend: AbiFrontend {
                name: "trustc".to_string(),
                revision: "trust-wp-test-fixture".to_string(),
            },
            convention: "Rust".to_string(),
            lowered_convention: CallingConv::default(),
            source_abi: "Rust".to_string(),
            can_unwind: false,
            variadic: false,
            fixed_count: 1,
            arguments: vec![AbiArgument {
                size: 16,
                align: 8,
                mode: AbiPassMode::Pair(lane(0), lane(8)),
                bindings: vec![
                    binding(AbiBindingPlace::Parameter(0), 0),
                    binding(AbiBindingPlace::Parameter(1), 8),
                ],
            }],
            result: AbiArgument {
                size: 8,
                align: 8,
                mode: AbiPassMode::Direct(lane(0)),
                bindings: vec![binding(AbiBindingPlace::Result(0), 0)],
            },
        });
    }
    signature
}

fn native_bundle_with_split_pair_signature(
    formula: ProofFormula,
    abi: bool,
) -> NativeVerificationBundle {
    let mut bundle = native_bundle_with_func_ty(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        split_pair_signature(abi),
    );
    bundle.module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("darwinpcs".to_string()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

/// D-191. The unrecorded signature reads `x` as the whole `u64` its slot is,
/// and `x + 1 > x` verifies. With the placement record that slot is half of
/// the source argument, and reading it as the parameter would state the
/// clause about the wrong value: every slot of the placed signature is
/// refused by name, although trust-ir checks the record consistent with the
/// slots, the target and the function.
#[test]
fn test_trust_ir_native_placed_signature_binding_is_refused() {
    for place in [
        ClausePlace::Param { index: 0 },
        ClausePlace::Param { index: 1 },
        ClausePlace::ResultSlot { index: 0 },
    ] {
        let formula = || {
            bound_formula(
                trust_formula_x_plus_one_gt_x(),
                &[("x", ClauseSort::Int, place)],
            )
        };
        assert_verified(&native_bundle_with_split_pair_signature(formula(), false));

        let bundle = native_bundle_with_split_pair_signature(formula(), true);
        let function = &bundle.module.functions[0];
        assert!(
            matches!(function.fn_abi(&bundle.module), Ok(Some(_))),
            "the placement record is consistent, so the refusal is about placement itself"
        );
        assert_binding_refused(
            &bundle,
            TrustIrClauseCarrier::Obligation,
            "x",
            TrustIrUnsupportedClauseBindingReason::PlacedSignature { place },
        );
    }
}

/// A modeled sort that trust-ir does not class as a faithful reading of the
/// place's type.
#[test]
fn test_trust_ir_native_sort_not_admitting_place_type_is_refused() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_x_declared_bool(),
        &[("x", ClauseSort::Bool, ClausePlace::Param { index: 0 })],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::SortDoesNotAdmitPlaceType {
            sort: ClauseSort::Bool,
            ty: Ty::U64,
        },
    );
}

/// The binding and the formula's own declaration give the name two readings.
#[test]
fn test_trust_ir_native_binding_contradicting_formula_declaration_is_refused() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_x_declared_bool(),
        &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::FormulaDeclaresOtherSort {
            sort: ClauseSort::Int,
            declared: "Bool".to_string(),
        },
    );
}

/// Measured false accept: `!true` verified, and the verdict was recorded into
/// the bundle as native tMIR evidence, while a top-level `!` was rewritten into
/// the goal it negates. The claim is its own goal: `!true` fails and records
/// nothing, `!false` verifies and records its evidence.
#[test]
fn test_trust_ir_native_negated_claim_is_its_own_goal() {
    for (payload, verified) in [
        (
            r#"{"schema":"trust-wp.trust-formula.v1","body":{"op":"not","expr":{"bool":true}}}"#,
            false,
        ),
        (
            r#"{"schema":"trust-wp.trust-formula.v1","body":{"op":"not","expr":{"bool":false}}}"#,
            true,
        ),
    ] {
        let mut bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            payload,
        ));
        let output = verify_trust_ir_native_bundle_and_record_evidence(&mut bundle)
            .expect("the request converts");
        assert_eq!(
            output.results[0].status == VerifyBundleStatus::Verified,
            verified,
            "{payload}"
        );
        assert_eq!(output.results[0].exit_code() == 0, verified, "{payload}");
        assert_eq!(bundle.evidence_bundles.is_empty(), !verified, "{payload}");
        assert_eq!(
            output.artifact_attachments.is_empty(),
            !verified,
            "{payload}"
        );
    }
}

/// Measured false accept: a `result` record without a `name` declares
/// `result` — the decoder's default — and the declaration check read only an
/// explicit name, so a binding contradicting the declared sort went through
/// and `result ==> result` verified over a result slot bound as `Int`.
#[test]
fn test_trust_ir_native_binding_contradicting_default_result_declaration_is_refused() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        r#"{
            "schema": "trust-wp.trust-formula.v1",
            "variables": [],
            "result": {"sort": "bool"},
            "body": {"op": "implies", "lhs": {"result": true}, "rhs": {"result": true}}
        }"#,
        &[(
            "result",
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "result",
        TrustIrUnsupportedClauseBindingReason::FormulaDeclaresOtherSort {
            sort: ClauseSort::Int,
            declared: "Bool".to_string(),
        },
    );
}

/// Measured false accept: the binding says `result` is the u8 result slot,
/// but the formula binds `result` itself with a `let`, so the claim is
/// `x + 1 > x` and says nothing about the result slot; it verified at exit 0.
/// A binding is admitted only for a name the formula is stated over.
#[test]
fn test_trust_ir_native_binding_of_let_bound_name_is_refused() {
    let bundle = native_bundle_with_signature(
        bound_formula(
            r#"{
                "schema": "trust-wp.trust-formula.v1",
                "variables": [{"name": "x", "sort": "int"}],
                "body": {
                    "op": "let",
                    "name": "result",
                    "sort": "int",
                    "value": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                    "body": {"op": "gt", "lhs": {"var": "result"}, "rhs": {"var": "x"}}
                }
            }"#,
            &[
                ("x", ClauseSort::Int, ClausePlace::Param { index: 0 }),
                (
                    "result",
                    ClauseSort::Int,
                    ClausePlace::ResultSlot { index: 0 },
                ),
            ],
        ),
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::U64],
        vec![Ty::U8],
    );
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "result",
        TrustIrUnsupportedClauseBindingReason::NotAFormulaName,
    );
}

/// The same rule over a pure-expr payload, whose names are its free names: a
/// binding for a name the predicate never mentions is refused, one for a name
/// it does is admitted.
#[test]
fn test_trust_ir_native_pure_expr_binding_must_name_a_free_name() {
    let pure = |bindings: &[(&str, ClauseSort, ClausePlace)]| {
        let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", "x + 1 > x");
        formula.bindings = bound_formula(trust_formula_true(), bindings).bindings;
        native_bundle_with_bound_signature(formula)
    };
    assert_binding_refused(
        &pure(&[
            ("x", ClauseSort::Int, ClausePlace::Param { index: 0 }),
            ("y", ClauseSort::Int, ClausePlace::Param { index: 0 }),
        ]),
        TrustIrClauseCarrier::Obligation,
        "y",
        TrustIrUnsupportedClauseBindingReason::NotAFormulaName,
    );
    assert_verified(&pure(&[(
        "x",
        ClauseSort::Int,
        ClausePlace::Param { index: 0 },
    )]));
}

/// Measured false accept: a pure-expr predicate declares no sorts, so the
/// declared-sort rule never reached it, and `x` bound as `Bool` to the `bool`
/// parameter was admitted for `x + 1 > x`, `x == x` and `!(x > x)` — each
/// verified at exit 0 over an `x` the claim reads as an integer. A name's
/// sort is now read off its uses, and a binding must agree with it: `x == x`
/// fixes no sort, so `x` is the `Int` an unsorted name is read as.
#[test]
fn test_trust_ir_native_pure_expr_binding_sort_must_agree_with_uses() {
    let pure = |payload: &str, bindings: &[(&str, ClauseSort, ClausePlace)]| {
        let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", payload);
        formula.bindings = bound_formula(trust_formula_true(), bindings).bindings;
        native_bundle_with_bound_signature(formula)
    };
    let x_as_bool = [("x", ClauseSort::Bool, ClausePlace::Param { index: 1 })];
    for (payload, used) in [
        ("x + 1 > x", "Int"),
        ("!(x > x)", "Int"),
        ("x == x", "Int, the reading of a name no use gives a sort"),
    ] {
        assert_binding_refused(
            &pure(payload, &x_as_bool),
            TrustIrClauseCarrier::Obligation,
            "x",
            TrustIrUnsupportedClauseBindingReason::FormulaUsesOtherSort {
                sort: ClauseSort::Bool,
                used: used.to_string(),
            },
        );
    }
    // A name read as a boolean is refused an `Int` binding the same way.
    assert_binding_refused(
        &pure(
            "b ==> b",
            &[("b", ClauseSort::Int, ClausePlace::Param { index: 0 })],
        ),
        TrustIrClauseCarrier::Obligation,
        "b",
        TrustIrUnsupportedClauseBindingReason::FormulaUsesOtherSort {
            sort: ClauseSort::Int,
            used: "Bool".to_string(),
        },
    );
    // Uses that disagree leave no sort any binding could agree with.
    assert_binding_refused(
        &pure(
            "(x > 0) == x",
            &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
        ),
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::FormulaUsesConflictingSorts {
            first: "Int".to_string(),
            second: "Bool".to_string(),
        },
    );
    // A dereferenced name is a reference, which no Int or Bool place is.
    assert_binding_refused(
        &pure(
            "*m >= *m",
            &[("m", ClauseSort::Int, ClausePlace::MutParamExit { index: 2 })],
        ),
        TrustIrClauseCarrier::Obligation,
        "m",
        TrustIrUnsupportedClauseBindingReason::FormulaUsesOtherSort {
            sort: ClauseSort::Int,
            used: "a reference to Int".to_string(),
        },
    );
    // Controls: the bindings that agree with the uses still verify.
    for (payload, bindings) in [
        (
            "x + 1 > x",
            &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })][..],
        ),
        (
            "x == x",
            &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })][..],
        ),
        // A bare unsorted name in a boolean position is no typed predicate to
        // native replay, so the boolean control compares `b` with a literal.
        (
            "(b == true) ==> (b == true)",
            &[("b", ClauseSort::Bool, ClausePlace::Param { index: 1 })][..],
        ),
    ] {
        let results = verify_trust_ir_native_bundle(&pure(payload, bindings))
            .unwrap_or_else(|error| panic!("`{payload}` converts: {error}"));
        assert_eq!(results[0].status, VerifyBundleStatus::Verified, "{payload}");
    }
}

/// Measured false accept: `r` is declared by the trust-formula payload and
/// never read by its body, and a binding of it to the `u8` result slot was
/// admitted — `x + 1 > x` verified at exit 0 with a binding saying the claim
/// is about the result. A declared name the goal never reads is refused like
/// a let-bound one, in both formats.
#[test]
fn test_trust_ir_native_binding_of_declared_unused_name_is_refused() {
    let bundle = native_bundle_with_signature(
        bound_formula(
            r#"{
                "schema": "trust-wp.trust-formula.v1",
                "variables": [{"name": "x", "sort": "int"}, {"name": "r", "sort": "int"}],
                "body": {
                    "op": "gt",
                    "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                    "rhs": {"var": "x"}
                }
            }"#,
            &[
                ("x", ClauseSort::Int, ClausePlace::Param { index: 0 }),
                ("r", ClauseSort::Int, ClausePlace::ResultSlot { index: 0 }),
            ],
        ),
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::U64],
        vec![Ty::U8],
    );
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "r",
        TrustIrUnsupportedClauseBindingReason::NotAFormulaName,
    );
}

#[test]
fn test_trust_ir_native_duplicate_binding_name_is_refused() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_x_plus_one_gt_x(),
        &[
            ("x", ClauseSort::Int, ClausePlace::Param { index: 0 }),
            ("x", ClauseSort::Int, ClausePlace::ResultSlot { index: 0 }),
        ],
    ));
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::DuplicateName,
    );
}

/// Places resolve against the request's function; an obligation scoped to a
/// different one has no single signature for them to mean anything in.
#[test]
fn test_trust_ir_native_binding_on_obligation_of_other_function_is_refused() {
    let mut bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_x_plus_one_gt_x(),
        &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    ));
    bundle.module.proof_obligations[0].function = Some(FuncId::new(1));
    refresh_native_bundle_module_identity(&mut bundle);
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "x",
        TrustIrUnsupportedClauseBindingReason::OwningFunctionMismatch {
            obligation_function: 1,
            request_function: 0,
        },
    );
}

/// A replay atom entering the obligation's proof context is held to the same
/// rule as the obligation's own formula.
#[test]
fn test_trust_ir_native_replay_atom_binding_is_refused() {
    let mut bundle = native_bundle_with_signature(
        ProofFormula::new(
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            trust_formula_linear_variable(),
        ),
        TrustWpVerificationMode::StrongestPostcondition,
        vec![Ty::U64],
        Vec::new(),
    );
    let span = SourceSpan {
        file: 3,
        line: 17,
        col: 11,
    };
    let context = NativeReplayContext::default()
        .with_atom(
            NativeReplayAtom::assumption(
                NativeReplayAtomId::new(3),
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
                NativeReplayAtomId::new(4),
                bound_formula(
                    trust_formula_linear_assertion_atom(),
                    &[("x", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 })],
                ),
            )
            .with_obligation(ProofId::new(0))
            .with_assertion_id(NativeAssertionId::new(0))
            .with_span(span),
        );
    bundle.requests = vec![NativeVerificationRequest::TrustWp(
        trust_wp_request_with_replay_context(
            TrustWpVerificationMode::StrongestPostcondition,
            Some(context),
        ),
    )];
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::ReplayAtom { atom_id: 4 },
        "x",
        TrustIrUnsupportedClauseBindingReason::UnmodeledSort {
            sort: ClauseSort::BitVec(64),
        },
    );
}

/// Positive control for the measured formula: `Int` at a `u64` parameter is
/// the mathematical value of the place, which trust-ir calls faithful, and
/// `x + 1 > x` holds for every such value.
#[test]
fn test_trust_ir_native_int_binding_at_param_verifies() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_x_plus_one_gt_x(),
        &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    ));
    assert_verified(&bundle);
}

/// Positive control over every place kind trust-wp admits, Int and Bool both.
#[test]
fn test_trust_ir_native_bindings_at_every_admitted_place_verify() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_every_admitted_place(),
        &[
            ("x", ClauseSort::Int, ClausePlace::Param { index: 0 }),
            ("b", ClauseSort::Bool, ClausePlace::Param { index: 1 }),
            ("m", ClauseSort::Int, ClausePlace::MutParamExit { index: 2 }),
            ("r", ClauseSort::Int, ClausePlace::ResultSlot { index: 0 }),
        ],
    ));
    assert_verified(&bundle);
}

/// Admitted bindings buy no verdict: a false formula over them still fails.
#[test]
fn test_trust_ir_native_false_formula_with_admitted_binding_does_not_verify() {
    let bundle = native_bundle_with_bound_signature(bound_formula(
        trust_formula_x_gt_x_false(),
        &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    ));
    let results = verify_trust_ir_native_bundle(&bundle).expect("admitted bindings convert");
    assert_ne!(results[0].status, VerifyBundleStatus::Verified);
    assert_ne!(results[0].exit_code(), 0);
}

/// `fn(x: u64, b: bool, m: &mut i32, y: i64) -> u8`, the oracle's signature,
/// in `mode`.
fn native_bundle_with_oracle_signature(
    formula: ProofFormula,
    mode: TrustWpVerificationMode,
) -> NativeVerificationBundle {
    native_bundle_with_signature(
        formula,
        mode,
        vec![Ty::U64, Ty::Bool, Ty::RefMut(Box::new(Ty::I32)), Ty::I64],
        vec![Ty::U8],
    )
}

fn pure_expr_formula(payload: &str, bindings: &[(&str, ClauseSort, ClausePlace)]) -> ProofFormula {
    let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", payload);
    formula.bindings = bindings
        .iter()
        .map(|(name, sort, place)| {
            (
                (*name).to_string(),
                ClauseBinding {
                    sort: sort.clone(),
                    place: *place,
                },
            )
        })
        .collect();
    formula
}

/// Every message a fail-closed result gives: its own diagnostics, each
/// obligation's, and each obligation's refusal reason.
fn refusal_messages(result: &trust_wp_lib::VerifyBundleResult) -> Vec<String> {
    let mut messages = result
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.clone())
        .collect::<Vec<_>>();
    for obligation in &result.obligation_results {
        messages.extend(
            obligation
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.message.clone()),
        );
        if let BundleObligationStatus::Failed { reason }
        | BundleObligationStatus::Unknown { reason }
        | BundleObligationStatus::Unsupported { reason } = &obligation.status
        {
            messages.push(reason.clone());
        }
    }
    messages
}

/// Whether `bundle` is refused before any verdict, and a refusal message
/// names `named`: an `Invalid` or `Unsupported` result carrying it, or (for a
/// bound claim) a binding refusal before verification.
fn refused_naming(bundle: &NativeVerificationBundle, named: &str) -> Result<(), String> {
    match verify_trust_ir_native_bundle(bundle) {
        Err(TrustWpLibError::TrustIrNativeBundle(
            TrustIrNativeBundleError::UnsupportedClauseBinding { .. },
        )) => Ok(()),
        Err(error) => Err(format!("does not convert: {error}")),
        Ok(results) => {
            let result = &results[0];
            let messages = refusal_messages(result);
            let fail_closed = matches!(
                result.status,
                VerifyBundleStatus::Invalid | VerifyBundleStatus::Unsupported
            ) && result.exit_code() != 0;
            if fail_closed && messages.iter().any(|message| message.contains(named)) {
                Ok(())
            } else {
                Err(format!(
                    "is {:?}, not refused naming {named}: {messages:?}",
                    result.status
                ))
            }
        }
    }
}

/// Measured false accept: the pure-expr parser read `e as T` as `e`, so
/// `(x as u8) == x` over the `u64` parameter and `(y as u64) == y` over the
/// `i64` parameter verified at exit 0, bound and unbound, in both modes. The
/// first is false at `x = 256`, the second at `y = -1`. A cast is Rust's `as`
/// between integer types, exactly, or the claim is refused naming it.
#[test]
fn test_trust_ir_native_pure_expr_cast_is_not_its_operand() {
    let x = ("x", ClauseSort::Int, ClausePlace::Param { index: 0 });
    let y = ("y", ClauseSort::Int, ClausePlace::Param { index: 3 });
    let verdict = |payload: &str, bindings: &[(&str, ClauseSort, ClausePlace)], mode| {
        let bundle =
            native_bundle_with_oracle_signature(pure_expr_formula(payload, bindings), mode);
        let results = verify_trust_ir_native_bundle(&bundle)
            .unwrap_or_else(|error| panic!("`{payload}` converts: {error}"));
        assert_eq!(results.len(), 1);
        results.into_iter().next().expect("one result")
    };
    let mut violations = Vec::new();
    for mode in [
        TrustWpVerificationMode::WeakestPrecondition,
        TrustWpVerificationMode::StrongestPostcondition,
    ] {
        for (payload, bound) in [("(x as u8) == x", &x), ("(y as u64) == y", &y)] {
            for bindings in [std::slice::from_ref(bound), &[]] {
                let result = verdict(payload, bindings, mode);
                if result.status == VerifyBundleStatus::Verified || result.exit_code() == 0 {
                    violations.push(format!(
                        "`{payload}` ({mode:?}, {} bindings) is false and VERIFIED",
                        bindings.len()
                    ));
                }
            }
        }
        // A cast the prover cannot model is refused, and the refusal names it.
        for (payload, cast) in [
            ("(x as usize) == x", "cast `as usize`"),
            ("(x as u128) == x", "cast `as u128`"),
            ("(y as i128) == y", "cast `as i128`"),
            ("(x as f64) == x", "cast `as f64`"),
            ("(x as char) == x", "cast `as char`"),
            ("(x as Wd) == x", "cast `as Wd`"),
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            if let Err(why) = refused_naming(&bundle, cast) {
                violations.push(format!("`{payload}` ({mode:?}) {why}"));
            }
        }
        // Controls: Rust's `as`, evaluated, verifies.
        for payload in [
            "(300 as u8) == 44",
            "(-1 as u8) == 255",
            "(200 as i8) == -56",
            "(-129 as i8) == 127",
            "(4294967296 as u32) == 0",
            "(-1 as u32) == 4294967295",
            "(-1 as i64) == -1",
            "(4294967296 as u64) == 4294967296",
            "(-2147483649 as i32) == 2147483647",
            "((x + 1) as u8) == ((x + 1) as u8)",
            "(y as u64) == (y as u64)",
        ] {
            let result = verdict(payload, &[], mode);
            if result.status != VerifyBundleStatus::Verified {
                violations.push(format!(
                    "control `{payload}` ({mode:?}) is {:?}, not verified",
                    result.status
                ));
            }
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// Measured: every construct below was parsed and then dropped, and each claim
/// verified at exit 0 through this path (each is shown bound where it has a
/// free name, and unbound). An ascription never changes a value, but one that
/// contradicts the reading of its operand (`(x : bool) + 1 > x`), or names a
/// type the pure-expr reading cannot check (`: u8`), states a claim trust-wp
/// does not prove; a literal suffix types the operators around it; a `let`
/// annotation is an ascription of the value; a `let` whose pattern is a
/// literal, an expression statement and a binder whose type is not recorded
/// (`forall<v: u8>`, `forall<v>`) each drop a part of the claim. Each is now
/// refused by name.
#[test]
fn test_trust_ir_native_pure_expr_dropped_constructs_are_refused() {
    let x = [("x", ClauseSort::Int, ClausePlace::Param { index: 0 })];
    let mut violations = Vec::new();
    for mode in [
        TrustWpVerificationMode::WeakestPrecondition,
        TrustWpVerificationMode::StrongestPostcondition,
    ] {
        for (payload, bindings, named) in [
            ("(x : bool) + 1 > x", &x[..], "type ascription `: bool`"),
            (
                "(x : bool) + 1 > x",
                &[][..],
                "reads `x` at both Int and Bool",
            ),
            (
                "((x : bool) == (x : bool)) && (x + 1 > x)",
                &[][..],
                "reads `x` at both Int and Bool",
            ),
            (
                "((x > 0) : Int) == ((x > 0) : Int)",
                &x[..],
                "type ascription `: Int`",
            ),
            ("(x : u8) == x", &x[..], "type ascription `: u8`"),
            ("(x : u8) + 1 > x", &[][..], "type ascription `: u8`"),
            ("256u8 == 256", &[][..], "256u8"),
            ("-1u8 < 0", &[][..], "-1u8"),
            ("x + 1u8 > x", &x[..], "literal type suffix `u8`"),
            (
                "{ let t: bool = x + 1; t > x }",
                &x[..],
                "`let` annotation `: bool`",
            ),
            (
                "{ let t: u8 = x; t + 1 > t }",
                &x[..],
                "`let` annotation `: u8`",
            ),
            ("{ let 5 = x; true }", &[][..], "literal pattern"),
            ("{ false; true }", &[][..], "statement"),
            ("{ proof_assert!(false); true }", &[][..], "statement"),
            ("forall<v: u8> v + 1 > v", &[][..], "binder type `u8`"),
            ("forall<v> v == v", &[][..], "binder with no written type"),
            (
                "exists<v: (u8, bool)> true",
                &[][..],
                "binder type `(u8, bool)`",
            ),
        ] {
            let bundle =
                native_bundle_with_oracle_signature(pure_expr_formula(payload, bindings), mode);
            if let Err(why) = refused_naming(&bundle, named) {
                violations.push(format!(
                    "`{payload}` ({mode:?}, {} bindings) {why}",
                    bindings.len()
                ));
            }
        }
        // Controls: annotations the reading records faithfully are checked and
        // kept, so these still verify.
        for payload in [
            "(x : Int) + 1 > x",
            "((b : bool) == true) ==> ((b : bool) == true)",
            "{ let t: Int = x + 1; t > x }",
            "forall<v: Int> v + 1 > v",
            "3int + 1 > 3",
            "(255 as u8) == 255",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if !matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("control `{payload}` ({mode:?}) is {status:?}"));
            }
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// A trust-formula `let` declares its name's sort; the value must have it.
/// Measured: `let t: bool = x + 1 in t == t`, the declaration dropped at the
/// value, verified at exit 0.
#[test]
fn test_trust_ir_native_trust_formula_let_sort_must_match_its_value() {
    let payload = r#"{
        "schema": "trust-wp.trust-formula.v1",
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "let", "name": "t", "sort": "bool",
            "value": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
            "body": {"op": "eq", "lhs": {"var": "t"}, "rhs": {"var": "t"}}
        }
    }"#;
    let bundle = native_bundle_with_trust_wp_formula(ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        payload,
    ));
    refused_naming(
        &bundle,
        "declares `t` at sort `Bool` but binds it to a value of sort `Int`",
    )
    .unwrap_or_else(|why| panic!("the ill-sorted let {why}"));
}

/// Measured false accept: an ascription or a `let` annotation wrote its sort
/// onto a quantifier-bound name, and native sort inference read that
/// annotation in place of the binder's declared sort; the parser checked the
/// annotation against the operand's syntax only, and the two-sort check
/// looked at free names only. Each claim below verified at exit 0 in both
/// modes over a `v` (`x`, `p`) its binder does not range over. An annotation
/// must agree with the sort its name already has in scope — declared by the
/// binder, or the sort of the value a `let` binds — and one that does not is
/// refused naming the name. A free name bound by a clause binding is held
/// to the binding's sort by the binding rules, annotation included.
#[test]
fn test_trust_ir_native_pure_expr_annotation_must_agree_with_its_binder() {
    let x = [("x", ClauseSort::Int, ClausePlace::Param { index: 0 })];
    let b = [("b", ClauseSort::Bool, ClausePlace::Param { index: 1 })];
    let mut violations = Vec::new();
    for mode in ORACLE_MODES {
        for (payload, named) in [
            (
                "forall<v: bool> (v : Int) + 1 > (v : Int)",
                "`v` is annotated at sort Int where it is bound at sort Bool",
            ),
            (
                "forall<v: Int> (v : bool) || true",
                "`v` is annotated at sort Bool where it is bound at sort Int",
            ),
            (
                "forall<v: bool> { let t: Int = v; t + 1 > t }",
                "`v` is annotated at sort Int where it is bound at sort Bool",
            ),
            (
                "forall<v: Int> { let t = (v : bool); t || true }",
                "`v` is annotated at sort Bool where it is bound at sort Int",
            ),
            (
                "forall<x: Int> ((x : bool) == (x : bool)) && (x + 1 > x)",
                "`x` is annotated at sort Bool where it is bound at sort Int",
            ),
            (
                "exists<v: bool> (v : Int) + 1 > (v : Int)",
                "`v` is annotated at sort Int where it is bound at sort Bool",
            ),
            (
                "forall<p: &T> (p : Int) + 1 > (p : Int)",
                "`p` is annotated at sort Int where it is bound at sort &TypeParam(T)",
            ),
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            if let Err(why) = refused_naming(&bundle, named) {
                violations.push(format!("`{payload}` ({mode:?}) {why}"));
            }
        }
        // A free name's annotation against its clause binding.
        for (payload, bindings) in [
            ("(x : bool) || true", &x[..]),
            ("(b : Int) + 1 > (b : Int)", &b[..]),
        ] {
            let bundle =
                native_bundle_with_oracle_signature(pure_expr_formula(payload, bindings), mode);
            match verify_trust_ir_native_bundle(&bundle) {
                Err(TrustWpLibError::TrustIrNativeBundle(
                    TrustIrNativeBundleError::UnsupportedClauseBinding {
                        reason: TrustIrUnsupportedClauseBindingReason::FormulaUsesOtherSort { .. },
                        ..
                    },
                )) => {}
                other => violations.push(format!(
                    "`{payload}` ({mode:?}) bound at the other sort is {other:?}"
                )),
            }
        }
        // Controls: an annotation agreeing with the binder is kept and read.
        for payload in [
            "forall<v: Int> (v : Int) + 1 > v",
            "forall<v: Int> { let t: Int = v; t + 1 > t }",
            "forall<v: bool> (v : bool) == (v : bool)",
            "forall<v: bool> { let t = (v : bool); t == t }",
            "exists<v: Int> (v : Int) == (v : Int)",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if !matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("control `{payload}` ({mode:?}) is {status:?}"));
            }
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// Measured false accept: a pure-expr binder over a type parameter
/// (`forall<v: T>`) or a slice was admitted as a recorded sort, and native
/// replay read the name as an integer, so `forall<v: T> v + 1 > v`,
/// `forall<v: T> v < v + 1`, `forall<v: U> v + 2 > v + 1`,
/// `forall<v: E|Z|I> v + 1 > v` and `forall<s: [Int]> s + 1 > s` verified at
/// exit 0, over types whose values are not integers. And the rules that need
/// a value of the binder's sort fired over any sort: `exists<v: T> true`,
/// `exists<v: T> v == v` and `exists<p: &T> true` verified, false for an
/// uninhabited `T`, and so did `!(forall<p: &T> false)` and the
/// trust-formula `exists v: T. true`, `exists v: &T. true` and
/// `not(forall v: &T. false)`. A binder whose type is not a sort native
/// replay models is refused naming it (a trust-formula `seq` binder too,
/// though `exists v: seq. true` holds: native replay reads no sequence
/// value), and only `Int` and `Bool` are known inhabited.
#[test]
#[allow(clippy::too_many_lines)]
fn test_trust_ir_native_binder_over_an_unmodeled_or_empty_sort_is_refused() {
    let quantified = |op: &str, sort: &str, body: &str| {
        let payload = format!(
            r#"{{"schema": "trust-wp.trust-formula.v1", "variables": [], "body": {{"op": "{op}", "name": "v", "sort": "{sort}", "body": {body}}}}}"#
        );
        ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, payload)
    };
    let not_quantified = |op: &str, sort: &str, body: &str| {
        let payload = format!(
            r#"{{"schema": "trust-wp.trust-formula.v1", "variables": [], "body": {{"op": "not", "expr": {{"op": "{op}", "name": "v", "sort": "{sort}", "body": {body}}}}}}}"#
        );
        ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, payload)
    };
    let successor = r#"{"op": "gt", "lhs": {"op": "add", "lhs": {"var": "v"}, "rhs": {"int": 1}}, "rhs": {"var": "v"}}"#;
    let mut violations = Vec::new();
    for mode in ORACLE_MODES {
        let mut refused = vec![
            (
                pure_expr_formula("forall<v: T> v + 1 > v", &[]),
                "quantifier binder type `T`",
            ),
            (
                pure_expr_formula("forall<v: T> v < v + 1", &[]),
                "quantifier binder type `T`",
            ),
            (
                pure_expr_formula("forall<v: U> v + 2 > v + 1", &[]),
                "quantifier binder type `U`",
            ),
            (
                pure_expr_formula("forall<v: E> v + 1 > v", &[]),
                "quantifier binder type `E`",
            ),
            (
                pure_expr_formula("forall<v: Z> v + 1 > v", &[]),
                "quantifier binder type `Z`",
            ),
            (
                pure_expr_formula("forall<v: I> v + 1 > v", &[]),
                "quantifier binder type `I`",
            ),
            (
                pure_expr_formula("exists<v: T> true", &[]),
                "quantifier binder type `T`",
            ),
            (
                pure_expr_formula("exists<v: T> v == v", &[]),
                "quantifier binder type `T`",
            ),
            (
                pure_expr_formula("forall<s: [Int]> s + 1 > s", &[]),
                "quantifier binder type `[Int]`",
            ),
            (
                pure_expr_formula("exists<p: &T> true", &[]),
                "not known to be inhabited",
            ),
            (
                pure_expr_formula("!(forall<p: &T> false)", &[]),
                "not known to be inhabited",
            ),
            (
                quantified("forall", "T", successor),
                "sort `T` is a quantifier sort native replay does not model",
            ),
            (
                quantified("exists", "T", r#"{"bool": true}"#),
                "sort `T` is a quantifier sort native replay does not model",
            ),
            (
                quantified("exists", "seq", r#"{"bool": true}"#),
                "sort `seq` is a quantifier sort native replay does not model",
            ),
            (
                quantified("exists", "&T", r#"{"bool": true}"#),
                "not known to be inhabited",
            ),
            (
                not_quantified("forall", "&T", r#"{"bool": false}"#),
                "not known to be inhabited",
            ),
        ];
        for (formula, named) in refused.drain(..) {
            let payload = formula.payload.clone();
            let bundle = native_bundle_with_oracle_signature(formula, mode);
            if let Err(why) = refused_naming(&bundle, named) {
                violations.push(format!("`{payload}` ({mode:?}) {why}"));
            }
        }
        // Controls: over `Int` and `Bool` a witness exists, and a reference
        // binder still reaches pointer replay.
        for formula in [
            pure_expr_formula("exists<v: Int> true", &[]),
            pure_expr_formula("exists<v: bool> true", &[]),
            pure_expr_formula("!(forall<v: Int> false)", &[]),
            pure_expr_formula("exists<v: Int> v + 1 > v", &[]),
            pure_expr_formula("forall<p: &T> p == p", &[]),
            quantified("exists", "int", r#"{"bool": true}"#),
            not_quantified("forall", "bool", r#"{"bool": false}"#),
            quantified("forall", "int", successor),
        ] {
            let payload = formula.payload.clone();
            let bundle = native_bundle_with_oracle_signature(formula, mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if !matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("control `{payload}` ({mode:?}) is {status:?}"));
            }
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// Measured false accept, pre-existing on d2fa44af and f5640243: `*e` was
/// read as an integer whatever `e` is. Native sort inference gave every
/// dereference the unsorted (integer) reading, the two-sort check kept only
/// `Int` against `Bool`, the parser dropped an `Int` ascription on a `*`
/// operand (and `*&v` was a dereference of `v`), and native replay proved
/// `e + k > e` by its shape. Each claim below VERIFIED at exit 0 in both
/// modes, over a `*p` that is a `bool`, a `T`, a slice, or no value at all.
/// `*e` now reads the sort `e` references (`*&e` is `e`), a dereference of
/// anything else is refused naming it, every name read at two sorts is
/// refused, an annotation the AST cannot carry refuses the claim, and the
/// integer rules read an operand as an integer only where it is one.
#[test]
#[allow(clippy::too_many_lines)]
fn test_trust_ir_native_pure_expr_dereference_reads_the_referent_sort() {
    let refused = [
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
    let b = [("b", ClauseSort::Bool, ClausePlace::Param { index: 1 })];
    let mut violations = Vec::new();
    for mode in ORACLE_MODES {
        for (payload, named) in refused {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            if let Err(why) = refused_naming(&bundle, named) {
                violations.push(format!("`{payload}` ({mode:?}) {why}"));
            }
        }
        // The free-name form, `b` bound to the `bool` parameter: the claim
        // reads it both as a reference and as a `bool`.
        let payload = "(0 < 1 ==> *b + 1 > *b) && ((b : bool) || true)";
        let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &b), mode);
        match verify_trust_ir_native_bundle(&bundle) {
            Err(TrustWpLibError::TrustIrNativeBundle(
                TrustIrNativeBundleError::UnsupportedClauseBinding {
                    reason:
                        TrustIrUnsupportedClauseBindingReason::FormulaUsesConflictingSorts { .. },
                    ..
                },
            )) => {}
            other => violations.push(format!("`{payload}` ({mode:?}) bound is {other:?}")),
        }
        // Controls: a dereference of a reference to an `Int` is one, and
        // `*&v` is `v`.
        for payload in [
            "forall<p: &Int> (0 < 1 ==> *p + 1 > *p)",
            "forall<p: &mut Int> (0 < 1 ==> *p + 1 > *p)",
            "forall<p: &&Int> (0 < 1 ==> **p + 1 > **p)",
            "forall<p: &Int> { let t = *p; 0 < 1 ==> t + 1 > t }",
            "forall<p: &mut Int> (0 < 1 ==> ^p + 1 > ^p)",
            "forall<v: Int> (0 < 1 ==> *&v + 1 > *&v)",
            "forall<p: &bool> *p == *p",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if !matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("control `{payload}` ({mode:?}) is {status:?}"));
            }
        }
        for payload in [
            "forall<p: &Int> (0 < 1 ==> *p + 1 > *p + 1)",
            "forall<v: Int> (0 < 1 ==> *&v + 1 > *&v + 1)",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("false `{payload}` ({mode:?}) VERIFIED"));
            }
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// Measured false accepts through a borrow, VERIFIED at exit 0 in both
/// modes. The parser keeps `e` for `&e` and `&mut e`, a reference level
/// below the borrow, and cancelled it only in `*&e`: `^&p` read as `^p` (the
/// final value of `p`, not of the shared borrow `&p`, which has none), and
/// once `^p` of a `&mut Int` was an integer the `^&p`, `^(&mut p)` and
/// `final_value(&p)` family verified; `let r = &p; ^r` did the same through
/// a `let`; `*(&v)` stayed a dereference of `v`, so `*(&v) + 1 > *(&v)`
/// verified over a `v: &Int`; `^&mut p == ^&mut q` read as `^p == ^q`; and
/// equality substitution replaced a `&mut Int` name by another reference, so
/// `p == if true {q} else {q}` equated their final values. `*` of a borrow,
/// parenthesized or not, is now the borrowed value, `^` of one is refused,
/// any other borrow refuses the claim, and only an `Int` or `Bool` name is
/// substituted, by a value of its own sort. A name a `let` binds to a borrow
/// is read the same way: `*r` reads the borrowed value, and `^r` is refused.
#[test]
#[allow(clippy::too_many_lines)]
fn test_trust_ir_native_pure_expr_borrow_is_read_at_its_reference_level() {
    let refused = [
        (
            "forall<p: &mut Int> (0 < 1 ==> ^&p + 1 > ^&p)",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> ^(&p) + 1 > ^(&p))",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> ^(&mut p) + 1 > ^(&mut p))",
            "`^` of the borrow `&mut p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> ^& &p + 1 > ^& &p)",
            "`^` of the borrow `& &p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> old(^&p) + 1 > old(^&p))",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> final_value(&p) + 1 > final_value(&p))",
            "`final_value` of the borrow `&p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> final_value(&mut p) + 1 > ^p)",
            "`final_value` of the borrow `&mut p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> ^&mut p + 1 > ^p)",
            "`^` of the borrow `&mut p` has no reading",
        ),
        (
            "forall<p: &mut Int> (^&p == ^p)",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "forall<p: &mut Int> (^&mut p == ^p)",
            "`^` of the borrow `&mut p` has no reading",
        ),
        (
            "forall<p: &mut Int> { let r = &p; 0 < 1 ==> ^r + 1 > ^r }",
            "`^` of `r`, bound to the borrow `&p`, has no reading",
        ),
        (
            "forall<v: &Int> { let r = &v; 0 < 1 ==> *r + 1 > *r }",
            "reads `v` at both Int and a reference",
        ),
        (
            "forall<p: &mut &mut Int> forall<q: &mut &mut Int> ((^p == ^q) ==> (^&mut p == ^&mut q))",
            "`^` of the borrow `&mut p` has no reading",
        ),
        (
            "forall<p: &mut &mut Int> forall<q: &mut &mut Int> ((^p == ^q) ==> (^(&mut p) == ^(&mut q)))",
            "`^` of the borrow `&mut p` has no reading",
        ),
        (
            "forall<p: &mut &mut Int> (0 < 1 ==> ^&*p + 1 > ^&*p)",
            "`^` of the borrow `&*p` has no reading",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> ^&mut *p + 1 > ^p)",
            "`^` of the borrow `&mut *p` has no reading",
        ),
        (
            "forall<v: &Int> (0 < 1 ==> *(&v) + 1 > *(&v))",
            "reads `v` at both Int and a reference",
        ),
        (
            "forall<v: &Int> (*(&v) == *v)",
            "reads `v` at both Int and a reference",
        ),
        (
            "forall<p: &mut Int> (0 < 1 ==> *(&mut p) + 1 > *(&mut p))",
            "reads `p` at both Int and a reference",
        ),
        (
            "forall<p: &mut Int> forall<q: &mut Int> ((p == (if true {q} else {q}) && 0 < 1) ==> ^p + 1 > ^(if true {q} else {q}))",
            "native pure replay cannot prove or refute",
        ),
    ];
    let mut violations = Vec::new();
    for mode in ORACLE_MODES {
        for (payload, named) in refused {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            if let Err(why) = refused_naming(&bundle, named) {
                violations.push(format!("`{payload}` ({mode:?}) {why}"));
            }
        }
        // Controls: `*` of a borrow reads the borrowed value, and `^` of a
        // dereferenced borrow is `^` of the borrowed reference.
        for payload in [
            "forall<v: Int> (0 < 1 ==> *(&v) + 1 > *(&v))",
            "forall<p: &Int> (0 < 1 ==> **(&p) + 1 > **(&p))",
            "forall<p: &mut Int> (0 < 1 ==> ^*&mut p + 1 > ^p)",
            "forall<p: &mut Int> forall<x: Int> ((x == ^p && 0 < 1) ==> x + 1 > ^p)",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if !matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("control `{payload}` ({mode:?}) is {status:?}"));
            }
        }
        let payload = "forall<v: Int> (0 < 1 ==> *(&v) + 1 > *(&v) + 1)";
        let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
        let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
        if matches!(status, Ok(VerifyBundleStatus::Verified)) {
            violations.push(format!("false `{payload}` ({mode:?}) VERIFIED"));
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// Measured false accepts through a reference pattern, a binding by
/// reference and a view, each VERIFIED at exit 0 in both modes. The parser
/// consumed `&`/`&mut`/`ref`/`ref mut` in a pattern and bound `t` to the
/// matched value itself: `let ref t = p; ^t` (Rust's `let t = &p`, refused in
/// that spelling) read `^p`, and `let &t = p; *t` read `*p` of a `t` that is
/// an integer. Every `b@` (`view(b)`) had a sort of its own, and native
/// replay read each as an integer, so a view read as a `bool` in one place and
/// added to in another verified. A `let` pattern now binds at its level, a
/// name bound to a borrow is read through by `*` and refused under `^`, and a
/// view is one `Int` per operand.
#[test]
#[allow(clippy::too_many_lines)]
fn test_trust_ir_native_pure_expr_pattern_and_view_are_read_at_their_level() {
    let refused = [
        (
            "forall<p: &mut Int> { let ref t = p; 0 < 1 ==> ^t + 1 > ^t }",
            "`^` of `t`, bound to the borrow `ref t`, has no reading",
        ),
        (
            "forall<p: &mut Int> { let ref mut t = p; 0 < 1 ==> ^t + 1 > ^t }",
            "`^` of `t`, bound to the borrow `ref mut t`, has no reading",
        ),
        (
            "forall<p: &Int> { let &t = p; 0 < 1 ==> *t + 1 > *t }",
            "`*t` dereferences `t`, which is not a reference: its sort is Int",
        ),
        (
            "forall<p: &mut Int> { let &mut t = p; 0 < 1 ==> *t + 1 > *t }",
            "`*t` dereferences `t`, which is not a reference: its sort is Int",
        ),
        (
            "forall<p: &mut Int> { let &mut t = p; 0 < 1 ==> ^t + 1 > ^t }",
            "`^t` is the final value of `t`, which is not a mutable reference",
        ),
        (
            "forall<v: &Int> (0 < 1 ==> **(& &v) + 1 > **(& &v))",
            "reads `v` at both Int and a reference",
        ),
        (
            "forall<p: &Int> { let ref t = p; 0 < 1 ==> t == t }",
            "the borrow `ref t`, whose reference the AST drops",
        ),
        (
            "forall<p: &Int> match p { Some(&t) => 0 < 1 ==> t + 1 > t, _ => true }",
            "the reference pattern `&t`, whose reference level the AST drops",
        ),
        (
            "(b@ == true && 0 < 1) ==> b@ + 1 > b@",
            "reads `b` at both a value whose view is Bool and a value whose view is Int",
        ),
        (
            "(0 < 1 ==> b@ + 1 > b@) && (b@ == true || true)",
            "reads `b` at both a value whose view is Bool and a value whose view is Int",
        ),
        (
            "(0 < 1 ==> view(b) + 1 > view(b)) && (view(b) == true || true)",
            "reads `b` at both a value whose view is Bool and a value whose view is Int",
        ),
        (
            "(0 < 1 ==> view(b) + 1 > b@) && (b@ == true || true)",
            "reads `b` at both a value whose view is Bool and a value whose view is Int",
        ),
    ];
    let mut violations = Vec::new();
    for mode in ORACLE_MODES {
        for (payload, named) in refused {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            if let Err(why) = refused_naming(&bundle, named) {
                violations.push(format!("`{payload}` ({mode:?}) {why}"));
            }
        }
        // Controls: each level read where the text puts it.
        for payload in [
            "forall<p: &Int> { let &t = p; 0 < 1 ==> t + 1 > t }",
            "forall<p: &&Int> { let &t = p; 0 < 1 ==> *t + 1 > *t }",
            "forall<p: &mut Int> { let &mut t = p; 0 < 1 ==> t + 1 > t }",
            "forall<p: &mut Int> { let ref t = p; 0 < 1 ==> ^*t + 1 > ^*t }",
            "forall<p: &mut Int> { let ref mut t = p; 0 < 1 ==> **t + 1 > **t }",
            "forall<v: Int> { let r = &v; 0 < 1 ==> *r + 1 > *r }",
            "forall<v: Int> (0 < 1 ==> **(& &v) + 1 > **(& &v))",
            "0 < 1 ==> b@ + 1 > view(b)",
            "forall<p: &Int> match p { &t => 0 < 1 ==> t + 1 > t }",
            "forall<p: &Int> if let &t = p { 0 < 1 ==> t + 1 > t } else { false }",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if !matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("control `{payload}` ({mode:?}) is {status:?}"));
            }
        }
        for payload in [
            "forall<p: &Int> { let &t = p; 0 < 1 ==> t + 1 > t + 1 }",
            "forall<p: &mut Int> { let ref t = p; 0 < 1 ==> ^*t + 1 > ^*t + 1 }",
            "0 < 1 ==> b@ + 1 > view(b) + 1",
            "forall<p: &Int> match p { &t => 0 < 1 ==> t + 1 > t + 1 }",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            if matches!(status, Ok(VerifyBundleStatus::Verified)) {
                violations.push(format!("false `{payload}` ({mode:?}) VERIFIED"));
            }
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

/// The examples contract-syntax.md gives for `as`, `/`, `%`, annotations
/// and dereferences, each read the way the page says. The page once gave
/// `-1 as u64 == 18446744073709551615`, whose literal does not parse, and
/// called `%` Euclidean, which the parser's `%` is not.
#[test]
fn test_trust_ir_native_contract_syntax_examples_hold() {
    for mode in ORACLE_MODES {
        for payload in [
            "256 as u8 == 0",
            "-1 as u32 == 4294967295",
            "200 as i8 == -56",
            "-7 / 2 == -3",
            "-7 % 3 == -1",
            "7 % -3 == 1",
            "forall<v: Int> *&v == v",
            "forall<v: Int> *(&v) == v",
            "forall<p: &&Int> (0 < 1 ==> **p + 1 > **p)",
            "forall<v: Int> **(& &v) == v",
            "forall<v: Int> { let r = &v; *r == v }",
            "forall<p: &Int> { let &t = p; t == *p }",
            "forall<p: &mut Int> { let ref t = p; ^*t == ^p }",
            "0 < 1 ==> b@ + 1 > view(b)",
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            let status = verify_trust_ir_native_bundle(&bundle).map(|results| results[0].status);
            assert!(
                matches!(status, Ok(VerifyBundleStatus::Verified)),
                "`{payload}` ({mode:?}) is {status:?}"
            );
        }
        for (payload, named) in [
            (
                "-1 as u64 == 18446744073709551615",
                "integer literal '18446744073709551615' overflows i64",
            ),
            (
                "forall<v: bool> (v : Int) > 0",
                "`v` is annotated at sort Int where it is bound at sort Bool",
            ),
            (
                "forall<p: &bool> { let t = *p; (t : Int) > 0 }",
                "`t` is annotated at sort Int where it is bound at sort Bool",
            ),
            (
                "forall<p: &Int> (*p : Int) > 0",
                "type ascription `: Int` on `*p`",
            ),
            (
                "forall<p: &Int> { let t: Int = *p; t > 0 }",
                "`let` annotation `: Int` on `*p`",
            ),
            (
                "forall<v: bool> *v",
                "`*v` dereferences `v`, which is not a reference",
            ),
            (
                "*b",
                "`*b` dereferences `b`, which nothing in the claim makes a reference",
            ),
            (
                "forall<p: &T> *p == *p",
                "reads the referent of `p` at sort TypeParam(T)",
            ),
            (
                "forall<p: &[Int]> *p == *p",
                "reads the referent of `p` at sort Seq",
            ),
            (
                "forall<p: &Int> ^p == ^p",
                "`^p` is the final value of `p`, which is not a mutable reference",
            ),
            (
                "forall<p: &mut Int> ^&p == ^p",
                "`^` of the borrow `&p` has no reading",
            ),
            (
                "forall<p: &mut Int> { let r = &p; ^r == ^p }",
                "`^` of `r`, bound to the borrow `&p`, has no reading",
            ),
            (
                "forall<p: &mut Int> { let ref t = p; ^t == ^p }",
                "`^` of `t`, bound to the borrow `ref t`, has no reading",
            ),
            (
                "forall<v: Int> v@ == v@",
                "reads `v` at both Int and a value with a view",
            ),
            (
                "forall<p: &mut Int> { let r = &p; r == p }",
                "the borrow `&p`, whose reference the AST drops",
            ),
            (
                "forall<p: &Int> match p { Some(&t) => t == *p, None => true }",
                "the reference pattern `&t`, whose reference level the AST drops",
            ),
            (
                "(b@ == true) || true",
                "reads `b` at both a value whose view is Bool and a value whose view is Int",
            ),
        ] {
            let bundle = native_bundle_with_oracle_signature(pure_expr_formula(payload, &[]), mode);
            refused_naming(&bundle, named)
                .unwrap_or_else(|why| panic!("`{payload}` ({mode:?}) {why}"));
        }
    }
}

// ---- Soundness oracle over the native bundle path ---------------------------
//
// Every verdict below is checked against an evaluator that shares no code with
// trust-wp. A claim is evaluated at a grid of concrete values of the places
// its names are bound to, read as the mathematical values trust-wp proves
// over (`old(v)` is a value of its own). Two properties hold for every claim
// in the corpus, whatever its shape:
//
// 1. a claim and its negation never both verify;
// 2. a claim that some grid point falsifies never verifies.
//
// A claim whose bindings are ill-formed is refused before verification, by
// name and by the rule it breaks: a binding at the sort the formula does not
// read the name at (by declaration or by use), for a name the goal never reads
// (declared and unused, or absent), for a name only a `let` binds, or at a
// place that does not resolve. The generated corpus derives each of these from
// its own claims, so the binding rules are exercised mechanically, and every
// well-formed claim it emits must decode and have its bindings admitted.
//
// A quantifier ranges over `Int` or `bool` and is evaluated over a grid of
// its name's values (`oracle_bound_domain`). A claim quantifying over a sort
// that says nothing of its values (a type parameter, a sequence) or reading a
// bound name at a sort its binder does not give it must not decode; one whose
// truth turns on whether a reference's referent type is inhabited must never
// verify, nor may its negation.
//
// A dereference is read at the sort its operand references. One of a value
// that is no reference to a sort native replay models decodes and must be
// refused naming it, an annotation on one must not decode, and a well-sorted
// one `X` of known truth is stated as `(C && X) || (!C && !X)`, which the
// evaluator reads as `C` or `!C`.

/// How a division by a literal rounds. Each claim format spells one: a
/// trust-formula `div`/`mod` is Euclidean, a pure-expr `/`/`%` truncates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OracleDivision {
    Euclidean,
    Truncating,
}

/// An integer term over the oracle signature's places.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OracleTerm {
    /// `x`, `y`, `m` or `result`.
    Place(&'static str),
    /// `old(x)`, `old(y)` or `old(m)`.
    Old(&'static str),
    /// A name bound by an enclosing `let` or `Int` quantifier.
    LetBound(String),
    /// `(t : Int)`: an ascription agreeing with the term's sort. Only
    /// pure-expr spells it; trust-formula spells the term.
    AscribedInt(Box<OracleTerm>),
    Lit(i64),
    Add(Box<OracleTerm>, Box<OracleTerm>),
    Sub(Box<OracleTerm>, Box<OracleTerm>),
    /// `t * k` for a literal `k`, so no product of places leaves `i128`.
    Mul(Box<OracleTerm>, i64),
    Neg(Box<OracleTerm>),
    /// `t / k` for a nonzero literal `k`, a divisor both decoders accept
    /// without a guard.
    Div(Box<OracleTerm>, i64, OracleDivision),
    /// `t % k`, likewise.
    Rem(Box<OracleTerm>, i64, OracleDivision),
    /// `if c { t } else { e }`; only pure-expr spells it.
    Ite(Box<OracleClaim>, Box<OracleTerm>, Box<OracleTerm>),
    /// `t as T` for a fixed-width integer type; only pure-expr spells it.
    Cast(Box<OracleTerm>, OracleIntTy),
}

/// The integer types a cast in the corpus targets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OracleIntTy {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

impl OracleIntTy {
    const ALL: [Self; 8] = [
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
        Self::I8,
        Self::I16,
        Self::I32,
        Self::I64,
    ];

    const fn name(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
        }
    }

    /// Rust's `as`, applied by the compiler that builds this test: the
    /// operand is the mathematical value, held in an `i128`, whose low bits
    /// are the bits of that value in any integer type that holds it.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    fn cast(self, value: i128) -> i128 {
        match self {
            Self::U8 => i128::from(value as u8),
            Self::U16 => i128::from(value as u16),
            Self::U32 => i128::from(value as u32),
            Self::U64 => i128::from(value as u64),
            Self::I8 => i128::from(value as i8),
            Self::I16 => i128::from(value as i16),
            Self::I32 => i128::from(value as i32),
            Self::I64 => i128::from(value as i64),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OracleCmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl OracleCmp {
    const ALL: [Self; 6] = [Self::Eq, Self::Ne, Self::Lt, Self::Le, Self::Gt, Self::Ge];

    const fn trust_formula_op(self) -> &'static str {
        match self {
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Lt => "lt",
            Self::Le => "le",
            Self::Gt => "gt",
            Self::Ge => "ge",
        }
    }

    const fn pure_expr_op(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }

    fn holds(self, left: i128, right: i128) -> bool {
        match self {
            Self::Eq => left == right,
            Self::Ne => left != right,
            Self::Lt => left < right,
            Self::Le => left <= right,
            Self::Gt => left > right,
            Self::Ge => left >= right,
        }
    }
}

/// A boolean claim over the oracle signature's places.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OracleClaim {
    Lit(bool),
    /// The bool parameter `b`.
    B,
    /// `b == lit` (`true`) or `b != lit` (`false`): `b` read as a boolean by
    /// the side it is compared with, the position a pure-expr `Bool` name
    /// reaches a verdict in.
    BCmp(bool, bool),
    Cmp(OracleCmp, OracleTerm, OracleTerm),
    Not(Box<OracleClaim>),
    And(Box<OracleClaim>, Box<OracleClaim>),
    Or(Box<OracleClaim>, Box<OracleClaim>),
    Implies(Box<OracleClaim>, Box<OracleClaim>),
    /// `let name: int = value in body`; the flag writes the `: Int`
    /// annotation in pure-expr (trust-formula always declares the sort).
    Let(String, OracleTerm, Box<OracleClaim>, bool),
    /// `forall`/`exists` (the flag says `exists`) over a name of the given
    /// sort, read in the body through `LetBound` (`Int`) or `BoundBool`.
    Quant(bool, String, OracleSort, Box<OracleClaim>),
    /// A name a `bool` quantifier binds, read as a boolean.
    BoundBool(String, OracleBoolRead),
}

/// A sort a generated quantifier ranges over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OracleSort {
    Int,
    Bool,
}

/// How a claim reads a `bool`-bound name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OracleBoolRead {
    /// `p`.
    Bare,
    /// `(p : bool)`, the binder's own sort (pure-expr; trust-formula `p`).
    Ascribed,
    /// `p == lit` (`true`) or `p != lit` (`false`).
    Cmp(bool, bool),
}

/// The grid an `Int` quantifier ranges over in the evaluator: the place
/// grids' boundary and interior points. A quantifier is decided on this
/// finite grid, which agrees with native replay's quantifier rules: they
/// decide `forall`/`exists` only from a body that holds (or fails) for every
/// value of the name, and such a body does so on the grid too.
fn oracle_bound_domain() -> Vec<i128> {
    vec![
        i128::from(i64::MIN),
        -129,
        -2,
        -1,
        0,
        1,
        2,
        3,
        7,
        100,
        128,
        256,
        i128::from(u64::MAX),
    ]
}

fn oracle_not(claim: OracleClaim) -> OracleClaim {
    OracleClaim::Not(Box::new(claim))
}

fn oracle_and(left: OracleClaim, right: OracleClaim) -> OracleClaim {
    OracleClaim::And(Box::new(left), Box::new(right))
}

fn oracle_cmp(op: OracleCmp, left: OracleTerm, right: OracleTerm) -> OracleClaim {
    OracleClaim::Cmp(op, left, right)
}

fn oracle_add(left: OracleTerm, right: OracleTerm) -> OracleTerm {
    OracleTerm::Add(Box::new(left), Box::new(right))
}

/// The grid each evaluator key ranges over: the boundary values of the place's
/// IR type, the small values the literals in the corpus meet, interior points
/// on both sides of them, and values a narrowing cast wraps (`256`, `128`,
/// `-129`).
fn oracle_domain(key: &str) -> Vec<i128> {
    match key {
        "x" | "old(x)" => vec![0, 1, 2, 3, 7, 100, 256, i128::from(u64::MAX)],
        "y" | "old(y)" => vec![
            i128::from(i64::MIN),
            -129,
            -2,
            -1,
            0,
            1,
            3,
            7,
            100,
            128,
            i128::from(i64::MAX),
        ],
        "m" | "old(m)" => vec![
            i128::from(i32::MIN),
            -2,
            -1,
            0,
            1,
            3,
            7,
            100,
            i128::from(i32::MAX),
        ],
        "result" => vec![0, 1, 3, 7, 100, i128::from(u8::MAX)],
        other => panic!("oracle key `{other}` has no domain"),
    }
}

#[derive(Debug, Clone, Default)]
struct OracleEnv {
    ints: std::collections::BTreeMap<String, i128>,
    b: bool,
    /// The names `bool` quantifiers bind.
    bools: std::collections::BTreeMap<String, bool>,
}

/// What a claim reads.
#[derive(Debug, Default)]
struct OracleReads {
    /// Evaluator keys: a place name, or `old(name)`.
    keys: std::collections::BTreeSet<String>,
    /// Whether the bool parameter `b` is read.
    b: bool,
    /// Every name a `let` or a quantifier in the claim binds.
    let_names: std::collections::BTreeSet<String>,
}

fn oracle_checked(value: Option<i128>) -> i128 {
    value.expect("oracle arithmetic stays inside i128")
}

fn oracle_literal(value: i64) -> String {
    if value < 0 {
        format!("({value})")
    } else {
        value.to_string()
    }
}

impl OracleTerm {
    fn eval(&self, env: &OracleEnv) -> i128 {
        match self {
            Self::Place(name) => env.ints[*name],
            Self::Old(name) => env.ints[&format!("old({name})")],
            Self::LetBound(name) => env.ints[name],
            Self::AscribedInt(term) => term.eval(env),
            Self::Lit(value) => i128::from(*value),
            Self::Add(left, right) => oracle_checked(left.eval(env).checked_add(right.eval(env))),
            Self::Sub(left, right) => oracle_checked(left.eval(env).checked_sub(right.eval(env))),
            Self::Mul(term, factor) => {
                oracle_checked(term.eval(env).checked_mul(i128::from(*factor)))
            }
            Self::Neg(term) => oracle_checked(term.eval(env).checked_neg()),
            Self::Div(term, divisor, division) => {
                let (dividend, divisor) = (term.eval(env), i128::from(*divisor));
                oracle_checked(match division {
                    OracleDivision::Euclidean => dividend.checked_div_euclid(divisor),
                    OracleDivision::Truncating => dividend.checked_div(divisor),
                })
            }
            Self::Rem(term, divisor, division) => {
                let (dividend, divisor) = (term.eval(env), i128::from(*divisor));
                oracle_checked(match division {
                    OracleDivision::Euclidean => dividend.checked_rem_euclid(divisor),
                    OracleDivision::Truncating => dividend.checked_rem(divisor),
                })
            }
            Self::Ite(cond, then_term, else_term) => {
                if cond.eval(env) {
                    then_term.eval(env)
                } else {
                    else_term.eval(env)
                }
            }
            Self::Cast(term, ty) => ty.cast(term.eval(env)),
        }
    }

    fn collect_reads(&self, bound: &mut Vec<String>, reads: &mut OracleReads) {
        match self {
            Self::Place(name) => {
                assert!(
                    !bound.iter().any(|bound| bound == name),
                    "place `{name}` is never generated under a let of its own name"
                );
                reads.keys.insert((*name).to_string());
            }
            Self::Old(name) => {
                reads.keys.insert(format!("old({name})"));
            }
            Self::LetBound(name) => assert!(bound.contains(name), "let name `{name}` is bound"),
            Self::AscribedInt(term) => term.collect_reads(bound, reads),
            Self::Lit(_) => {}
            Self::Add(left, right) | Self::Sub(left, right) => {
                left.collect_reads(bound, reads);
                right.collect_reads(bound, reads);
            }
            Self::Mul(term, _)
            | Self::Neg(term)
            | Self::Div(term, ..)
            | Self::Rem(term, ..)
            | Self::Cast(term, _) => {
                term.collect_reads(bound, reads);
            }
            Self::Ite(cond, then_term, else_term) => {
                cond.collect_reads(bound, reads);
                then_term.collect_reads(bound, reads);
                else_term.collect_reads(bound, reads);
            }
        }
    }

    fn is_extended(&self) -> bool {
        match self {
            Self::Place(_) | Self::Old(_) | Self::LetBound(_) | Self::Lit(_) => false,
            Self::AscribedInt(term) => term.is_extended(),
            Self::Add(left, right) | Self::Sub(left, right) => {
                left.is_extended() || right.is_extended()
            }
            Self::Mul(..)
            | Self::Neg(_)
            | Self::Div(..)
            | Self::Rem(..)
            | Self::Ite(..)
            | Self::Cast(..) => true,
        }
    }

    fn has_cast(&self) -> bool {
        match self {
            Self::Place(_) | Self::Old(_) | Self::LetBound(_) | Self::Lit(_) => false,
            Self::AscribedInt(term) => term.has_cast(),
            Self::Add(left, right) | Self::Sub(left, right) => left.has_cast() || right.has_cast(),
            Self::Mul(term, _) | Self::Neg(term) | Self::Div(term, ..) | Self::Rem(term, ..) => {
                term.has_cast()
            }
            Self::Ite(cond, then_term, else_term) => {
                cond.has_cast() || then_term.has_cast() || else_term.has_cast()
            }
            Self::Cast(..) => true,
        }
    }

    /// The trust-formula spelling; `None` for what that format cannot spell.
    fn trust_formula(&self) -> Option<serde_json::Value> {
        use serde_json::json;
        let binary = |op: &str, left: &Self, right: &Self| {
            Some(json!({"op": op, "lhs": left.trust_formula()?, "rhs": right.trust_formula()?}))
        };
        let by_literal = |op: &str, term: &Self, literal: i64| {
            Some(json!({"op": op, "lhs": term.trust_formula()?, "rhs": {"int": literal}}))
        };
        match self {
            Self::Place("result") => Some(json!({"result": true})),
            Self::Place(name) => Some(json!({"var": name})),
            Self::Old(name) => Some(json!({"old": {"var": name}})),
            Self::LetBound(name) => Some(json!({"var": name})),
            Self::AscribedInt(term) => term.trust_formula(),
            Self::Lit(value) => Some(json!({"int": value})),
            Self::Add(left, right) => binary("add", left, right),
            Self::Sub(left, right) => binary("sub", left, right),
            Self::Mul(term, factor) => by_literal("mul", term, *factor),
            Self::Neg(term) => Some(json!({"op": "neg", "expr": term.trust_formula()?})),
            Self::Div(term, divisor, OracleDivision::Euclidean) => {
                by_literal("div", term, *divisor)
            }
            Self::Rem(term, divisor, OracleDivision::Euclidean) => {
                by_literal("mod", term, *divisor)
            }
            Self::Div(_, _, OracleDivision::Truncating)
            | Self::Rem(_, _, OracleDivision::Truncating)
            | Self::Ite(..)
            | Self::Cast(..) => None,
        }
    }

    /// The pure-expr spelling; `None` for what that format cannot spell.
    fn pure_expr(&self) -> Option<String> {
        Some(match self {
            Self::Place(name) => (*name).to_string(),
            Self::LetBound(name) => name.clone(),
            Self::AscribedInt(term) => format!("({} : Int)", term.pure_expr()?),
            Self::Old(name) => format!("old({name})"),
            Self::Lit(value) => oracle_literal(*value),
            Self::Add(left, right) => format!("({} + {})", left.pure_expr()?, right.pure_expr()?),
            Self::Sub(left, right) => format!("({} - {})", left.pure_expr()?, right.pure_expr()?),
            Self::Mul(term, factor) => {
                format!("({} * {})", term.pure_expr()?, oracle_literal(*factor))
            }
            Self::Neg(term) => format!("(-{})", term.pure_expr()?),
            Self::Div(term, divisor, OracleDivision::Truncating) => {
                format!("({} / {})", term.pure_expr()?, oracle_literal(*divisor))
            }
            Self::Rem(term, divisor, OracleDivision::Truncating) => {
                format!("({} % {})", term.pure_expr()?, oracle_literal(*divisor))
            }
            Self::Div(_, _, OracleDivision::Euclidean)
            | Self::Rem(_, _, OracleDivision::Euclidean) => return None,
            Self::Ite(cond, then_term, else_term) => format!(
                "(if {} {{ {} }} else {{ {} }})",
                cond.pure_expr()?,
                then_term.pure_expr()?,
                else_term.pure_expr()?
            ),
            Self::Cast(term, ty) => format!("({} as {})", term.pure_expr()?, ty.name()),
        })
    }
}

impl OracleClaim {
    fn eval(&self, env: &OracleEnv) -> bool {
        match self {
            Self::Lit(value) => *value,
            Self::B => env.b,
            Self::BCmp(equal, literal) => (env.b == *literal) == *equal,
            Self::Cmp(op, left, right) => op.holds(left.eval(env), right.eval(env)),
            Self::Not(inner) => !inner.eval(env),
            Self::And(left, right) => left.eval(env) && right.eval(env),
            Self::Or(left, right) => left.eval(env) || right.eval(env),
            Self::Implies(left, right) => !left.eval(env) || right.eval(env),
            Self::Let(name, value, body, _) => {
                let mut scoped = env.clone();
                scoped.ints.insert(name.clone(), value.eval(env));
                body.eval(&scoped)
            }
            Self::Quant(exists, name, sort, body) => {
                let holds_at = |bind: &dyn Fn(&mut OracleEnv)| {
                    let mut scoped = env.clone();
                    bind(&mut scoped);
                    body.eval(&scoped)
                };
                let results = match sort {
                    OracleSort::Int => oracle_bound_domain()
                        .into_iter()
                        .map(|value| {
                            holds_at(&|scoped: &mut OracleEnv| {
                                scoped.ints.insert(name.clone(), value);
                            })
                        })
                        .collect::<Vec<_>>(),
                    OracleSort::Bool => [false, true]
                        .into_iter()
                        .map(|value| {
                            holds_at(&|scoped: &mut OracleEnv| {
                                scoped.bools.insert(name.clone(), value);
                            })
                        })
                        .collect(),
                };
                if *exists {
                    results.contains(&true)
                } else {
                    !results.contains(&false)
                }
            }
            Self::BoundBool(name, read) => {
                let value = env.bools[name];
                match read {
                    OracleBoolRead::Bare | OracleBoolRead::Ascribed => value,
                    OracleBoolRead::Cmp(equal, literal) => (value == *literal) == *equal,
                }
            }
        }
    }

    fn collect_reads(&self, bound: &mut Vec<String>, reads: &mut OracleReads) {
        match self {
            Self::Lit(_) => {}
            Self::B | Self::BCmp(..) => reads.b = true,
            Self::Cmp(_, left, right) => {
                left.collect_reads(bound, reads);
                right.collect_reads(bound, reads);
            }
            Self::Not(inner) => inner.collect_reads(bound, reads),
            Self::And(left, right) | Self::Or(left, right) | Self::Implies(left, right) => {
                left.collect_reads(bound, reads);
                right.collect_reads(bound, reads);
            }
            Self::Let(name, value, body, _) => {
                value.collect_reads(bound, reads);
                reads.let_names.insert(name.clone());
                bound.push(name.clone());
                body.collect_reads(bound, reads);
                bound.pop();
            }
            Self::Quant(_, name, _, body) => {
                reads.let_names.insert(name.clone());
                bound.push(name.clone());
                body.collect_reads(bound, reads);
                bound.pop();
            }
            Self::BoundBool(name, _) => {
                assert!(bound.contains(name), "bool name `{name}` is bound");
            }
        }
    }

    fn reads(&self) -> OracleReads {
        let mut reads = OracleReads::default();
        self.collect_reads(&mut Vec::new(), &mut reads);
        reads
    }

    fn is_extended(&self) -> bool {
        match self {
            Self::Lit(_) | Self::B | Self::BCmp(..) => false,
            Self::Cmp(_, left, right) => left.is_extended() || right.is_extended(),
            Self::Not(inner) => inner.is_extended(),
            Self::And(left, right) | Self::Or(left, right) | Self::Implies(left, right) => {
                left.is_extended() || right.is_extended()
            }
            Self::Let(_, value, body, _) => value.is_extended() || body.is_extended(),
            Self::Quant(.., body) => body.is_extended(),
            Self::BoundBool(..) => false,
        }
    }

    fn has_cast(&self) -> bool {
        match self {
            Self::Lit(_) | Self::B | Self::BCmp(..) => false,
            Self::Cmp(_, left, right) => left.has_cast() || right.has_cast(),
            Self::Not(inner) => inner.has_cast(),
            Self::And(left, right) | Self::Or(left, right) | Self::Implies(left, right) => {
                left.has_cast() || right.has_cast()
            }
            Self::Let(_, value, body, _) => value.has_cast() || body.has_cast(),
            Self::Quant(.., body) => body.has_cast(),
            Self::BoundBool(..) => false,
        }
    }

    /// Whether the claim holds a quantifier, and whether an `exists`.
    fn quantifiers(&self) -> (bool, bool) {
        match self {
            Self::Lit(_) | Self::B | Self::BCmp(..) | Self::Cmp(..) | Self::BoundBool(..) => {
                (false, false)
            }
            Self::Not(inner) | Self::Let(_, _, inner, _) => inner.quantifiers(),
            Self::And(left, right) | Self::Or(left, right) | Self::Implies(left, right) => {
                let (left, right) = (left.quantifiers(), right.quantifiers());
                (left.0 || right.0, left.1 || right.1)
            }
            Self::Quant(exists, .., body) => (true, *exists || body.quantifiers().1),
        }
    }

    /// Whether some grid point falsifies the claim, and which.
    fn falsifying_point(&self) -> Option<OracleEnv> {
        let reads = self.reads();
        let keys = reads.keys.into_iter().collect::<Vec<_>>();
        let domains = keys
            .iter()
            .map(|key| oracle_domain(key))
            .collect::<Vec<_>>();
        let bool_values: &[bool] = if reads.b { &[false, true] } else { &[false] };
        let mut index = vec![0_usize; keys.len()];
        loop {
            for &b in bool_values {
                let env = OracleEnv {
                    ints: keys
                        .iter()
                        .zip(&index)
                        .zip(&domains)
                        .map(|((key, &at), domain)| (key.clone(), domain[at]))
                        .collect(),
                    b,
                    bools: std::collections::BTreeMap::new(),
                };
                if !self.eval(&env) {
                    return Some(env);
                }
            }
            // Advance the mixed-radix counter; the grid is done when it wraps.
            let mut position = 0;
            loop {
                if position == index.len() {
                    return None;
                }
                index[position] += 1;
                if index[position] < domains[position].len() {
                    break;
                }
                index[position] = 0;
                position += 1;
            }
        }
    }

    fn trust_formula_body(&self) -> Option<serde_json::Value> {
        use serde_json::json;
        let binary = |op: &str, left: &Self, right: &Self| {
            Some(
                json!({"op": op, "lhs": left.trust_formula_body()?, "rhs": right.trust_formula_body()?}),
            )
        };
        match self {
            Self::Lit(value) => Some(json!({"bool": value})),
            Self::B => Some(json!({"var": "b"})),
            Self::BCmp(equal, literal) => Some(json!({
                "op": if *equal { "eq" } else { "ne" },
                "lhs": {"var": "b"},
                "rhs": {"bool": literal},
            })),
            Self::Cmp(op, left, right) => Some(json!({
                "op": op.trust_formula_op(),
                "lhs": left.trust_formula()?,
                "rhs": right.trust_formula()?,
            })),
            Self::Not(inner) => Some(json!({"op": "not", "expr": inner.trust_formula_body()?})),
            Self::And(left, right) => binary("and", left, right),
            Self::Or(left, right) => binary("or", left, right),
            Self::Implies(left, right) => binary("implies", left, right),
            Self::Let(name, value, body, _) => Some(json!({
                "op": "let",
                "name": name,
                "sort": "int",
                "value": value.trust_formula()?,
                "body": body.trust_formula_body()?,
            })),
            Self::Quant(exists, name, sort, body) => Some(json!({
                "op": if *exists { "exists" } else { "forall" },
                "name": name,
                "sort": match sort {
                    OracleSort::Int => "int",
                    OracleSort::Bool => "bool",
                },
                "body": body.trust_formula_body()?,
            })),
            Self::BoundBool(name, OracleBoolRead::Bare | OracleBoolRead::Ascribed) => {
                Some(json!({"var": name}))
            }
            Self::BoundBool(name, OracleBoolRead::Cmp(equal, literal)) => Some(json!({
                "op": if *equal { "eq" } else { "ne" },
                "lhs": {"var": name},
                "rhs": {"bool": literal},
            })),
        }
    }

    /// A trust-formula v1 payload declaring every oracle place no `let` of
    /// the claim binds, `result` through the decoder's default name, whether
    /// the body reads it or not. `None` when the format cannot spell the body,
    /// or when a `let` rebinds a name the claim also reads free (the decoder
    /// refuses a let that shadows a declaration).
    fn trust_formula_payload(&self) -> Option<String> {
        let reads = self.reads();
        if self
            .read_names()
            .iter()
            .any(|name| reads.let_names.contains(*name))
        {
            return None;
        }
        let declared = ORACLE_PLACES
            .into_iter()
            .filter(|name| !reads.let_names.contains(*name))
            .collect::<Vec<_>>();
        let variables = declared
            .iter()
            .filter(|name| **name != "result")
            .map(|name| {
                serde_json::json!({"name": name, "sort": if *name == "b" { "bool" } else { "int" }})
            })
            .collect::<Vec<_>>();
        let mut payload = serde_json::json!({
            "schema": TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            "variables": variables,
            "body": self.trust_formula_body()?,
        });
        if declared.contains(&"result") {
            payload["result"] = serde_json::json!({"sort": "int"});
        }
        Some(payload.to_string())
    }

    /// Pure-expr text, fully parenthesized, a `let` as a block. `None` for
    /// what the format cannot spell.
    fn pure_expr(&self) -> Option<String> {
        Some(match self {
            Self::Lit(value) => value.to_string(),
            Self::B => "b".to_string(),
            Self::BCmp(equal, literal) => {
                format!("(b {} {literal})", if *equal { "==" } else { "!=" })
            }
            Self::Cmp(op, left, right) => format!(
                "({} {} {})",
                left.pure_expr()?,
                op.pure_expr_op(),
                right.pure_expr()?
            ),
            Self::Not(inner) => format!("!{}", inner.pure_expr()?),
            Self::And(left, right) => format!("({} && {})", left.pure_expr()?, right.pure_expr()?),
            Self::Or(left, right) => format!("({} || {})", left.pure_expr()?, right.pure_expr()?),
            Self::Implies(left, right) => {
                format!("({} ==> {})", left.pure_expr()?, right.pure_expr()?)
            }
            Self::Let(name, value, body, typed) => {
                format!(
                    "{{ let {name}{} = {}; {} }}",
                    if *typed { ": Int" } else { "" },
                    value.pure_expr()?,
                    body.pure_expr()?
                )
            }
            Self::Quant(exists, name, sort, body) => format!(
                "({}<{name}: {}> {})",
                if *exists { "exists" } else { "forall" },
                match sort {
                    OracleSort::Int => "Int",
                    OracleSort::Bool => "bool",
                },
                body.pure_expr()?
            ),
            Self::BoundBool(name, OracleBoolRead::Bare) => name.clone(),
            Self::BoundBool(name, OracleBoolRead::Ascribed) => format!("({name} : bool)"),
            Self::BoundBool(name, OracleBoolRead::Cmp(equal, literal)) => {
                format!("({name} {} {literal})", if *equal { "==" } else { "!=" })
            }
        })
    }

    fn formula(&self, format: OracleFormat) -> Option<ProofFormula> {
        Some(match format {
            OracleFormat::TrustFormula => ProofFormula::new(
                TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
                self.trust_formula_payload()?,
            ),
            OracleFormat::PureExpr => ProofFormula::new(PURE_EXPR_SCHEMA, self.pure_expr()?),
        })
    }

    /// The places the claim reads free, as the binding names that denote them.
    fn read_names(&self) -> Vec<&'static str> {
        let reads = self.reads();
        let mut names = reads
            .keys
            .iter()
            .map(|key| {
                let place = key
                    .strip_prefix("old(")
                    .and_then(|rest| rest.strip_suffix(')'))
                    .unwrap_or(key);
                ORACLE_PLACES
                    .into_iter()
                    .find(|name| *name == place)
                    .expect("every key is an oracle place")
            })
            .collect::<std::collections::BTreeSet<_>>();
        if reads.b {
            names.insert("b");
        }
        names.into_iter().collect()
    }

    /// The claim with its subformula at each position negated in turn, the
    /// whole claim first.
    fn negation_mutants(&self) -> Vec<Self> {
        let mut mutants = vec![oracle_not(self.clone())];
        let rebuild =
            |children: Vec<Vec<Self>>, make: &dyn Fn(Vec<Self>) -> Self, originals: &[Self]| {
                let mut out = Vec::new();
                for (position, variants) in children.into_iter().enumerate() {
                    for variant in variants {
                        let mut parts = originals.to_vec();
                        parts[position] = variant;
                        out.push(make(parts));
                    }
                }
                out
            };
        match self {
            Self::Lit(_) | Self::B | Self::BCmp(..) | Self::Cmp(..) | Self::BoundBool(..) => {}
            Self::Not(inner) => mutants.extend(rebuild(
                vec![inner.negation_mutants()],
                &|parts| oracle_not(parts.into_iter().next().expect("one part")),
                &[(**inner).clone()],
            )),
            Self::And(left, right) | Self::Or(left, right) | Self::Implies(left, right) => {
                let make = |parts: Vec<Self>| {
                    let mut parts = parts.into_iter();
                    let left = Box::new(parts.next().expect("left part"));
                    let right = Box::new(parts.next().expect("right part"));
                    match self {
                        Self::And(..) => Self::And(left, right),
                        Self::Or(..) => Self::Or(left, right),
                        _ => Self::Implies(left, right),
                    }
                };
                mutants.extend(rebuild(
                    vec![left.negation_mutants(), right.negation_mutants()],
                    &make,
                    &[(**left).clone(), (**right).clone()],
                ));
            }
            Self::Let(name, value, body, typed) => {
                for variant in body.negation_mutants() {
                    mutants.push(Self::Let(
                        name.clone(),
                        value.clone(),
                        Box::new(variant),
                        *typed,
                    ));
                }
            }
            Self::Quant(exists, name, sort, body) => {
                for variant in body.negation_mutants() {
                    mutants.push(Self::Quant(*exists, name.clone(), *sort, Box::new(variant)));
                }
            }
        }
        mutants
    }
}

const PURE_EXPR_SCHEMA: &str = "trust-wp.pure-expr.v1";

/// The places of `fn(x: u64, b: bool, m: &mut i32, y: i64) -> u8`, by the
/// name the oracle's claims give each.
const ORACLE_PLACES: [&str; 5] = ["x", "b", "m", "y", "result"];

fn oracle_place_binding(name: &str) -> ClauseBinding {
    let (sort, place) = match name {
        "x" => (ClauseSort::Int, ClausePlace::Param { index: 0 }),
        "b" => (ClauseSort::Bool, ClausePlace::Param { index: 1 }),
        "m" => (ClauseSort::Int, ClausePlace::MutParamExit { index: 2 }),
        "y" => (ClauseSort::Int, ClausePlace::Param { index: 3 }),
        "result" => (ClauseSort::Int, ClausePlace::ResultSlot { index: 0 }),
        other => panic!("`{other}` is not an oracle place"),
    };
    ClauseBinding { sort, place }
}

fn oracle_bindings(names: &[&str]) -> Vec<(String, ClauseBinding)> {
    names
        .iter()
        .map(|name| ((*name).to_string(), oracle_place_binding(name)))
        .collect()
}

/// Places of the oracle signature that do not resolve, and the spec
/// variables, which trust-wp has no model for.
fn oracle_unresolvable_places() -> [ClausePlace; 10] {
    [
        ClausePlace::Param { index: 4 },
        ClausePlace::ResultSlot { index: 1 },
        ClausePlace::MutParamExit { index: 0 },
        ClausePlace::World,
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(0)),
        ClausePlace::SpecVar { index: 0 },
        ClausePlace::SpecVarNext { index: 0 },
    ]
}

/// The binding rule an ill-formed binding breaks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum OracleIllFormed {
    /// The other modeled sort than the formula reads the name at, at a place
    /// whose type admits it, so the formula's own reading is what refuses it.
    WrongSort,
    /// A name the goal never reads free: declared and unused in a
    /// trust-formula payload, absent from a pure-expr one.
    UnusedName,
    /// A name only a `let` or a quantifier inside the formula binds.
    LetBoundName,
    /// A place that does not resolve on the function, or a spec variable.
    UnresolvablePlace,
    /// A name the goal reads both as an integer and as a boolean (an operand
    /// of arithmetic and of a connective). Pure-expr only: a trust-formula
    /// payload declares one sort per name.
    ConflictingUses,
    /// A name compared by `==` with a value of the other sort than its other
    /// uses read it at: the two sides of an equality are one sort.
    /// Pure-expr only.
    EqualitySides,
    /// A name read through `*` or `^`, which reads it as a reference, not an
    /// `Int` or a `Bool`. Pure-expr only.
    ReferenceRead,
    /// An integer place's name as an `if` condition, which reads it as a
    /// boolean. Pure-expr only.
    IfCondition,
    /// A modeled sort at a place whose IR type that sort does not admit.
    SortNotAdmitted,
    /// A name bound twice.
    DuplicateName,
    /// A sort trust-wp has no model for (a bit-vector), at a place whose type
    /// that sort admits, so only the missing model refuses it.
    UnmodeledSort,
}

impl OracleIllFormed {
    const ALL: [Self; 11] = [
        Self::WrongSort,
        Self::UnusedName,
        Self::LetBoundName,
        Self::UnresolvablePlace,
        Self::ConflictingUses,
        Self::EqualitySides,
        Self::ReferenceRead,
        Self::IfCondition,
        Self::SortNotAdmitted,
        Self::DuplicateName,
        Self::UnmodeledSort,
    ];

    /// Whether only a pure-expr payload can spell the claim that breaks the
    /// rule.
    const fn pure_expr_only(self) -> bool {
        matches!(
            self,
            Self::ConflictingUses | Self::EqualitySides | Self::ReferenceRead | Self::IfCondition
        )
    }

    /// Whether `reason` is the refusal this rule gives in `format`.
    fn refuses_with(
        self,
        reason: &TrustIrUnsupportedClauseBindingReason,
        format: OracleFormat,
    ) -> bool {
        use TrustIrUnsupportedClauseBindingReason as Reason;
        match (self, format) {
            (Self::WrongSort, OracleFormat::TrustFormula) => {
                matches!(reason, Reason::FormulaDeclaresOtherSort { .. })
            }
            (Self::WrongSort, OracleFormat::PureExpr) => {
                matches!(reason, Reason::FormulaUsesOtherSort { .. })
            }
            (Self::UnusedName | Self::LetBoundName, _) => matches!(reason, Reason::NotAFormulaName),
            (Self::UnresolvablePlace, _) => matches!(
                reason,
                Reason::UnresolvedPlace { .. } | Reason::SpecVariablePlace { .. }
            ),
            (Self::ConflictingUses | Self::EqualitySides, _) => {
                matches!(reason, Reason::FormulaUsesConflictingSorts { .. })
            }
            // Read only there, the name has that one other reading; read as
            // an integer elsewhere too, its readings conflict.
            (Self::ReferenceRead | Self::IfCondition, _) => matches!(
                reason,
                Reason::FormulaUsesOtherSort { .. } | Reason::FormulaUsesConflictingSorts { .. }
            ),
            (Self::SortNotAdmitted, _) => {
                matches!(reason, Reason::SortDoesNotAdmitPlaceType { .. })
            }
            (Self::DuplicateName, _) => matches!(reason, Reason::DuplicateName),
            (Self::UnmodeledSort, _) => matches!(reason, Reason::UnmodeledSort { .. }),
        }
    }
}

/// The bit width of each oracle place's IR type.
fn oracle_place_bits(name: &str) -> u32 {
    match name {
        "x" | "y" => 64,
        "m" => 32,
        "result" => 8,
        "b" => 1,
        other => panic!("`{other}` is not an oracle place"),
    }
}

/// What the trust-formula decoder names when a `let` declares a sort its
/// value does not have.
const ORACLE_ILL_SORTED_LET: &str =
    "declares `tq` at sort `Bool` but binds it to a value of sort `Int`";

/// What native proof input names when a claim reads a name at two sorts.
const ORACLE_ILL_SORTED: &str = "at both Int and Bool";

/// A construct the pure-expr reading does not model, conjoined to a
/// well-formed claim: the claim must not decode and must be refused naming
/// the construct, bound or not. Each entry is `(conjunct, what the refusal
/// names)`.
const ORACLE_UNMODELED: [(&str, &str); 12] = [
    ("(x as usize) == (x as usize)", "cast `as usize`"),
    ("(y as i128) > 0", "cast `as i128`"),
    ("(x as f64) == (x as f64)", "cast `as f64`"),
    ("(x as bool) == true", "cast `as bool`"),
    ("(1u8 + x) > x", "literal type suffix `u8`"),
    ("(x : u8) == (x : u8)", "type ascription `: u8`"),
    ("forall<v: u8> v == v", "quantifier binder type `u8`"),
    ("forall<v> v == v", "a binder with no written type"),
    ("{ let t: u16 = x; t == t }", "`let` annotation `: u16`"),
    ("{ lemma(x); true }", "the statement `lemma(x);`"),
    ("256u8 == 256", "`256u8`"),
    ("{ let 5 = x; true }", "literal pattern"),
];

/// A disjunct reading a name bound inside it at a sort its binder does not
/// give it, through an ascription or an annotated `let` (pure-expr only).
/// Each verified at exit 0 while an annotation was checked against its
/// operand's syntax alone; the claim must not decode, and the refusal must
/// name the name and both sorts. Each entry is `(disjunct, what the refusal
/// names)`. One binder shadows the place `x`.
const ORACLE_BOUND_ILL_SORTED: [(&str, &str); 8] = [
    (
        "forall<wa: bool> (wa : Int) + 1 > (wa : Int)",
        "`wa` is annotated at sort Int where it is bound at sort Bool",
    ),
    (
        "forall<wb: Int> (wb : bool) || true",
        "`wb` is annotated at sort Bool where it is bound at sort Int",
    ),
    (
        "forall<wc: bool> { let tc: Int = wc; tc + 1 > tc }",
        "`wc` is annotated at sort Int where it is bound at sort Bool",
    ),
    (
        "forall<wd: Int> { let td = (wd : bool); td || true }",
        "`wd` is annotated at sort Bool where it is bound at sort Int",
    ),
    (
        "forall<x: Int> ((x : bool) == (x : bool)) && (x + 1 > x)",
        "`x` is annotated at sort Bool where it is bound at sort Int",
    ),
    (
        "exists<we: bool> (we : Int) + 1 > (we : Int)",
        "`we` is annotated at sort Int where it is bound at sort Bool",
    ),
    (
        "forall<wf: &T> (wf : Int) + 1 > (wf : Int)",
        "`wf` is annotated at sort Int where it is bound at sort &TypeParam(T)",
    ),
    (
        "exists<wg: bool> { let tg = wg; (tg : Int) + 1 > (tg : Int) }",
        "`tg` is annotated at sort Int where it is bound at sort Bool",
    ),
];

/// A disjunct quantifying over a sort native replay does not model, which it
/// read as an integer or as inhabited: the claim must not decode, and the
/// refusal must name the binder's type. Pure-expr entries, then
/// trust-formula ones (`name`, `sort`, body), each with what the refusal
/// names.
const ORACLE_UNMODELED_BINDERS: [(&str, &str); 6] = [
    ("forall<wt: T> wt + 1 > wt", "quantifier binder type `T`"),
    ("forall<wu: U> wu < wu + 1", "quantifier binder type `U`"),
    (
        "forall<wv: E> wv + 2 > wv + 1",
        "quantifier binder type `E`",
    ),
    ("exists<ww: Z> true", "quantifier binder type `Z`"),
    ("exists<wx: I> wx == wx", "quantifier binder type `I`"),
    (
        "forall<ws: [Int]> ws + 1 > ws",
        "quantifier binder type `[Int]`",
    ),
];

const ORACLE_TF_UNMODELED_BINDERS: [(&str, &str, &str); 3] = [
    (
        "forall",
        "T",
        "sort `T` is a quantifier sort native replay does not model",
    ),
    (
        "exists",
        "U",
        "sort `U` is a quantifier sort native replay does not model",
    ),
    (
        "forall",
        "seq",
        "sort `seq` is a quantifier sort native replay does not model",
    ),
];

/// What native replay names when a rule would need a value of a sort not
/// known to be inhabited.
const ORACLE_WITNESS_NEEDED: &str = "not known to be inhabited";

/// A claim over a reference binder whose truth turns on whether the
/// referent type is inhabited (`exists<wp: &T> true` is false for an empty
/// `T`), spelled in each format. Each verified at exit 0 while the witness
/// rules fired over any sort.
const ORACLE_EMPTY_DOMAIN: [&str; 3] = [
    "exists<wp: &T> true",
    "!(forall<wp: &T> false)",
    "exists<wp: &mut T> wp == wp",
];

/// A disjunct dereferencing a value at a sort it has no reading at: a
/// reference to `bool`, to a type parameter, to a slice (directly, nested,
/// through a `let`), a name that is no reference, a borrow of a `bool`
/// (`*&wv` is `wv`), the final value of a shared reference, a free name, and
/// a parenthesized borrow of a reference (`*(&wv)` is the reference `wv`),
/// a `let` reference pattern (`let &wt = wp` binds `*wp`, so `*wt` reads
/// through one level more), a nested borrow (`**(& &wv)` is the reference
/// `wv`), a view read at two sorts, and the subpattern of a binding by
/// reference (`let ref wa @ wt = wp` binds `wt` to `wp` itself, where it was
/// read as a borrow of `wp`). Each was read as an integer and VERIFIED at
/// exit 0 by native replay's `e + k > e` shape rule; the claim decodes, and
/// must be refused naming what the refusal says. Pure-expr only: no other
/// format spells `*`.
const ORACLE_DEREF_ILL_SORTED: [(&str, &str); 26] = [
    (
        "forall<wp: &bool> (0 < 1 ==> *wp + 1 > *wp)",
        "reads `wp` at both a reference to Bool and a reference to Int",
    ),
    (
        "forall<wp: &mut bool> (0 < 1 ==> *wp + 1 > *wp)",
        "reads `wp` at both a reference to Bool and a reference to Int",
    ),
    (
        "forall<wp: &T> (0 < 1 ==> *wp + 1 > *wp)",
        "reads the referent of `wp` at sort TypeParam(T)",
    ),
    (
        "forall<wp: &[Int]> (0 < 1 ==> *wp + 1 > *wp)",
        "reads the referent of `wp` at sort Seq",
    ),
    (
        "forall<wp: &&bool> (0 < 1 ==> **wp + 1 > **wp)",
        "reads `wp` at both a reference to a reference to Bool and a reference to a reference to Int",
    ),
    (
        "forall<wp: &&T> (0 < 1 ==> **wp + 1 > **wp)",
        "reads the referent of `*wp` at sort TypeParam(T)",
    ),
    (
        "forall<wp: &bool> { let wt = *wp; 0 < 1 ==> wt + 1 > wt }",
        "reads `wp` at both a reference to Bool and a reference to Int",
    ),
    (
        "forall<wp: &T> { let wt = *wp; 0 < 1 ==> wt + 1 > wt }",
        "reads the referent of `wp` at sort TypeParam(T)",
    ),
    (
        "forall<wp: &T> exists<wq: Int> (0 < 1 ==> *wp + 1 > *wp)",
        "reads the referent of `wp` at sort TypeParam(T)",
    ),
    (
        "forall<wv: bool> (0 < 1 ==> *wv + 1 > *wv)",
        "`*wv` dereferences `wv`, which is not a reference: its sort is Bool",
    ),
    (
        "exists<wv: bool> (0 < 1 ==> *wv + 1 > *wv)",
        "`*wv` dereferences `wv`, which is not a reference: its sort is Bool",
    ),
    (
        "forall<wv: Int> (0 < 1 ==> *wv + 1 > *wv)",
        "`*wv` dereferences `wv`, which is not a reference: its sort is Int",
    ),
    (
        "forall<wv: bool> (0 < 1 ==> *&wv + 1 > *&wv)",
        "reads `wv` at both Int and Bool",
    ),
    (
        "forall<wp: &Int> (0 < 1 ==> ^wp + 1 > ^wp)",
        "`^wp` is the final value of `wp`, which is not a mutable reference: its sort is &Int",
    ),
    (
        "(0 < 1 ==> *wb + 1 > *wb) && ((wb : bool) || true)",
        "`*wb` dereferences `wb`, which is not a reference: its sort is Bool",
    ),
    (
        "forall<wv: &Int> (0 < 1 ==> *(&wv) + 1 > *(&wv))",
        "reads `wv` at both Int and a reference",
    ),
    (
        "forall<wp: &mut Int> (0 < 1 ==> *(&mut wp) + 1 > *(&mut wp))",
        "reads `wp` at both Int and a reference",
    ),
    (
        "forall<wp: &Int> { let &wt = wp; 0 < 1 ==> *wt + 1 > *wt }",
        "`*wt` dereferences `wt`, which is not a reference: its sort is Int",
    ),
    (
        "forall<wp: &mut Int> { let &mut wt = wp; 0 < 1 ==> ^wt + 1 > ^wt }",
        "`^wt` is the final value of `wt`, which is not a mutable reference: its sort is Int",
    ),
    (
        "forall<wv: &Int> (0 < 1 ==> **(& &wv) + 1 > **(& &wv))",
        "reads `wv` at both Int and a reference",
    ),
    (
        "(wb@ == true && 0 < 1) ==> wb@ + 1 > wb@",
        "reads `wb` at both a value whose view is Bool and a value whose view is Int",
    ),
    (
        "(0 < 1 ==> wb@ + 1 > wb@) && (wb@ == true || true)",
        "reads `wb` at both a value whose view is Bool and a value whose view is Int",
    ),
    (
        "(0 < 1 ==> view(wb) + 1 > view(wb)) && (view(wb) == true || true)",
        "reads `wb` at both a value whose view is Bool and a value whose view is Int",
    ),
    (
        "forall<wp: &Int> { let ref wa @ wt = wp; 0 < 1 ==> **wt + 1 > **wt }",
        "`**wp` dereferences `*wp`, which is not a reference: its sort is Int",
    ),
    (
        "forall<wp: &mut Int> { let ref wa @ wt = wp; 0 < 1 ==> ^*wt + 1 > ^*wt }",
        "`^*wp` is the final value of `*wp`, which is not a mutable reference: its sort is Int",
    ),
    (
        "forall<wp: &mut Int> { let ref mut wa @ wt = wp; 0 < 1 ==> ^*wt + 1 > ^*wt }",
        "`^*wp` is the final value of `*wp`, which is not a mutable reference: its sort is Int",
    ),
];

/// A disjunct writing an `Int` annotation on a dereference, which the AST
/// cannot carry: the annotation was dropped and the claim VERIFIED at exit 0
/// over a `*wp` that is no integer. The claim must not decode, and must be
/// refused naming the annotation; one on a `*wp` that is an integer is
/// refused too, since nothing checks it. One entry annotates a `let` name at
/// a sort the dereference it binds does not have. The rest take `^` of a
/// borrow or of a name bound to one (`let wr = &wp`, `let ref wt = wp`), or
/// read a borrow the AST has no node for, each of
/// which the AST read a reference level off: `^&wp` read as `^wp`, and
/// `let ref wt = wp; ^wt` too, and each VERIFIED at exit 0. Then `*` or `^`
/// of an `if` or `match` whose branches are at different levels (the level
/// was dropped: `^(if c { &wp } else { wq })` read `^wp`), `^` of an operand
/// that drops a borrow, `ref` before anything but a name, a name bound
/// twice in one pattern, and a const generic argument that takes `^` of a
/// borrow (it was read as a type): each is a parse error naming it.
const ORACLE_DEREF_UNMODELED: [(&str, &str); 23] = [
    (
        "forall<wp: &bool> (0 < 1 ==> (*wp : Int) + 1 > (*wp : Int))",
        "type ascription `: Int` on `*wp`",
    ),
    (
        "forall<wv: bool> (0 < 1 ==> (*wv : Int) + 1 > (*wv : Int))",
        "type ascription `: Int` on `*wv`",
    ),
    (
        "forall<wp: &T> (0 < 1 ==> (*wp : Int) + 1 > (*wp : Int))",
        "type ascription `: Int` on `*wp`",
    ),
    (
        "forall<wp: &Int> (0 < 1 ==> (*wp : Int) + 1 > (*wp : Int))",
        "type ascription `: Int` on `*wp`",
    ),
    (
        "forall<wp: &bool> { let wt: Int = *wp; 0 < 1 ==> wt + 1 > wt }",
        "`let` annotation `: Int` on `*wp`",
    ),
    (
        "forall<wv: bool> { let wt: Int = *wv; 0 < 1 ==> wt + 1 > wt }",
        "`let` annotation `: Int` on `*wv`",
    ),
    (
        "forall<wp: &bool> { let wt: Int = (*wp : Int); 0 < 1 ==> wt + 1 > wt }",
        "type ascription `: Int` on `*wp`",
    ),
    (
        "forall<wp: &bool> { let wt = *wp; 0 < 1 ==> (wt : Int) + 1 > (wt : Int) }",
        "`wt` is annotated at sort Int where it is bound at sort Bool",
    ),
    (
        "forall<wp: &mut Int> (0 < 1 ==> ^&wp + 1 > ^&wp)",
        "`^` of the borrow `&wp` has no reading",
    ),
    (
        "forall<wp: &mut Int> (0 < 1 ==> final_value(&mut wp) + 1 > ^wp)",
        "`final_value` of the borrow `&mut wp` has no reading",
    ),
    (
        "forall<wp: &mut &mut Int> (0 < 1 ==> ^&*wp + 1 > ^&*wp)",
        "`^` of the borrow `&*wp` has no reading",
    ),
    (
        "forall<wp: &mut Int> { let wr = &wp; 0 < 1 ==> ^wr + 1 > ^wr }",
        "`^` of `wr`, bound to the borrow `&wp`, has no reading",
    ),
    (
        "forall<wp: &mut Int> { let ref wt = wp; 0 < 1 ==> ^wt + 1 > ^wt }",
        "`^` of `wt`, bound to the borrow `ref wt`, has no reading",
    ),
    (
        "forall<wp: &mut Int> { let ref mut wt = wp; 0 < 1 ==> ^wt + 1 > ^wt }",
        "`^` of `wt`, bound to the borrow `ref mut wt`, has no reading",
    ),
    (
        "forall<wp: &mut Int> { let wr = &mut wp; 0 < 1 ==> ^wr + 1 > ^wr }",
        "`^` of `wr`, bound to the borrow `&mut wp`, has no reading",
    ),
    (
        "forall<wp: &Int> { let wr = &wp; wr == wr }",
        "the borrow `&wp`, whose reference the AST drops",
    ),
    (
        "forall<wp: &mut Int> forall<wq: &mut Int> (0 < 1 ==> ^(if 0 < 1 { &wp } else { wq }) + 1 \
         > ^(if 0 < 1 { &wp } else { wq }))",
        "`^` of a value that is the borrow `&wp` in one branch and not in another has no reading",
    ),
    (
        "forall<wp: &mut Int> (0 < 1 ==> ^(match 0 { _ => &wp }) + 1 > ^(match 0 { _ => &wp }))",
        "`^` of the borrow `&wp` has no reading",
    ),
    (
        "forall<wv: &Int> forall<ww: Int> (0 < 1 ==> *(if 0 < 1 { &ww } else { wv }) + 1 \
         > *(if 0 < 1 { &ww } else { wv }))",
        "`*` of a value that is the borrow `&ww` in one branch and not in another has no reading",
    ),
    (
        "forall<wp: &mut Int> (0 < 1 ==> ^wf(&wp) + 1 > ^wf(&wp))",
        "`^` of an operand that holds the borrow `&wp` has no reading",
    ),
    (
        "forall<wp: &Int> { let ref (wt) = wp; 0 < 1 ==> *wt + 1 > *wt }",
        "expected an identifier after `ref`",
    ),
    (
        "forall<wx: Int> { let (wt, wt) = (wx, 0); 0 < 1 ==> wt + 1 > wt }",
        "identifier `wt` is bound more than once in the same pattern",
    ),
    (
        "0 < 1 ==> wf::<{ ^&wp }>(wp) + 1 > wf::<{ ^&wp }>(wp)",
        "`^` of the borrow `&wp` has no reading",
    ),
];

/// A well-sorted claim reading a dereference, with its truth: a reference to
/// an `Int` (shared, mutable, nested, through a `let`, its final value), a
/// borrow of an `Int` or of a reference (parenthesized or not, nested, under
/// `^`, bound by a `let`), a `let` reference pattern and binding by
/// reference, a reference to a `bool` read as one, the view of a free
/// integer, however it is spelled, the subpattern of a binding by reference
/// (the value itself), and an `@` binding read once (`let wx @ wy = wx + 1`
/// binds both to the old `wx` plus one; `wy` was read as the new `wx` plus
/// one, and the false twin VERIFIED), a reference pattern in a `match` arm
/// that cannot fail (`&wt` binds `*wp`), and a parenthesized pattern (`(wt)`
/// is `wt`, not a one-element tuple). The corpus
/// states `(C && X) || (!C && !X)`, which is `C` for a valid `X` and `!C`
/// for a false one, so the evaluator decides it and native replay must prove
/// the dereference to reach a verdict.
const ORACLE_DEREF_MODELED: [(&str, bool); 25] = [
    ("forall<wp: &Int> (0 < 1 ==> *wp + 1 > *wp)", true),
    ("forall<wp: &mut Int> (0 < 1 ==> *wp + 2 > *wp)", true),
    ("forall<wp: &&Int> (0 < 1 ==> **wp + 1 > **wp)", true),
    (
        "forall<wp: &Int> { let wt = *wp; 0 < 1 ==> wt + 1 > wt }",
        true,
    ),
    ("forall<wv: Int> (0 < 1 ==> *&wv + 1 > *&wv)", true),
    ("forall<wp: &mut Int> (0 < 1 ==> ^wp + 1 > ^wp)", true),
    ("forall<wp: &bool> *wp == *wp", true),
    ("forall<wv: Int> (0 < 1 ==> *&wv + 1 > *&wv + 1)", false),
    ("forall<wv: Int> (0 < 1 ==> *(&wv) + 1 > *(&wv))", true),
    ("forall<wp: &mut Int> (0 < 1 ==> ^*&mut wp + 1 > ^wp)", true),
    (
        "forall<wp: &Int> (0 < 1 ==> **(&wp) + 1 > **(&wp) + 1)",
        false,
    ),
    (
        "forall<wp: &Int> { let &wt = wp; 0 < 1 ==> wt + 1 > wt }",
        true,
    ),
    (
        "forall<wp: &&Int> { let &wt = wp; 0 < 1 ==> *wt + 1 > *wt + 1 }",
        false,
    ),
    (
        "forall<wp: &mut Int> { let ref wt = wp; 0 < 1 ==> ^*wt + 1 > ^*wt }",
        true,
    ),
    (
        "forall<wv: Int> { let wr = &wv; 0 < 1 ==> *wr + 1 > *wr + 1 }",
        false,
    ),
    (
        "forall<wv: Int> (0 < 1 ==> **(& &wv) + 1 > **(& &wv))",
        true,
    ),
    ("0 < 1 ==> wb@ + 1 > view(wb)", true),
    (
        "forall<wp: &Int> { let ref wa @ wt = wp; 0 < 1 ==> *wt + 1 > *wt }",
        true,
    ),
    (
        "forall<wp: &Int> { let ref wa @ wt = wp; 0 < 1 ==> **wa + 1 > **wa + 1 }",
        false,
    ),
    (
        "forall<wx: Int> { let wx @ wy = wx + 1; 0 < 1 ==> wy + 1 > wx + 1 }",
        false,
    ),
    ("forall<wx: Int> { let wx @ wy = wx + 1; wy == wx }", true),
    ("forall<wp: &Int> match wp { &wt => wt + 1 > wt }", true),
    (
        "forall<wp: &Int> match wp { &wt => wt + 1 > wt + 1 }",
        false,
    ),
    (
        "forall<wx: Int> { let (wt) = wx; 0 < 1 ==> wt + 1 > wt }",
        true,
    ),
    (
        "forall<wx: Int> { let (wt) = wx; 0 < 1 ==> wt + 1 > wx + 1 }",
        false,
    ),
];

#[derive(Debug, Clone)]
struct OracleIllFormedBinding {
    rule: OracleIllFormed,
    /// The binding the refusal must name.
    name: String,
}

#[derive(Debug, Clone)]
struct OracleCase {
    label: String,
    /// What the evaluator reads the claim as.
    claim: OracleClaim,
    formula: ProofFormula,
    kind: ObligationKind,
    mode: TrustWpVerificationMode,
    /// Set when a binding is ill-formed: the case must be refused by this
    /// rule, naming this binding, whatever the evaluator says.
    ill_formed: Option<OracleIllFormedBinding>,
    /// Set when the claim writes a construct the pure-expr reading does not
    /// model: the claim must not decode, and the refusal must name this.
    unmodeled: Option<&'static str>,
    /// Set when the claim reads a name at two sorts, or dereferences a value
    /// that is no reference to a sort native replay models: it decodes, but
    /// must be refused before any verdict, naming this.
    ill_sorted: Option<&'static str>,
    /// Set when the claim's truth turns on whether a sort is inhabited,
    /// which nothing in it says: it decodes and is admitted, and neither it
    /// nor its negation may verify.
    witness_needed: bool,
    /// Whether `formula` spells `claim` and nothing else. A derived case that
    /// adds a use the evaluator has no reading for (an ill-formed or
    /// ill-sorted conjunct, an unmodeled construct) must never verify, and
    /// the evaluator is not asked about it.
    spells_claim: bool,
    /// Whether the formula reads a well-sorted dereference whose truth the
    /// evaluator knows, so a verdict on it counts toward the dereferences
    /// the corpus proves.
    dereferences: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum OracleFormat {
    TrustFormula,
    PureExpr,
}

impl OracleCase {
    /// `claim` in `format`, bound at every place it reads (`bound`), or at
    /// none.
    fn new(
        label: String,
        claim: OracleClaim,
        format: OracleFormat,
        bound: bool,
        kind: ObligationKind,
        mode: TrustWpVerificationMode,
    ) -> Option<Self> {
        let mut formula = claim.formula(format)?;
        if bound {
            formula.bindings = oracle_bindings(&claim.read_names());
        }
        Some(Self {
            label,
            claim,
            formula,
            kind,
            mode,
            ill_formed: None,
            unmodeled: None,
            ill_sorted: None,
            witness_needed: false,
            spells_claim: true,
            dereferences: false,
        })
    }

    fn hand_written(
        label: &str,
        claim: OracleClaim,
        schema: &str,
        payload: &str,
        bindings: &[&str],
        kind: ObligationKind,
        mode: TrustWpVerificationMode,
    ) -> Self {
        let mut formula = ProofFormula::new(schema, payload);
        formula.bindings = oracle_bindings(bindings);
        Self {
            label: label.to_string(),
            claim,
            formula,
            kind,
            mode,
            ill_formed: None,
            unmodeled: None,
            ill_sorted: None,
            witness_needed: false,
            spells_claim: true,
            dereferences: false,
        }
    }

    fn ill_formed(mut self, rule: OracleIllFormed, name: &str) -> Self {
        self.ill_formed = Some(OracleIllFormedBinding {
            rule,
            name: name.to_string(),
        });
        self
    }

    fn format(&self) -> OracleFormat {
        if self.formula.schema == TRUST_FORMULA_CLAIM_SCHEMA_VERSION {
            OracleFormat::TrustFormula
        } else {
            OracleFormat::PureExpr
        }
    }

    /// The case bound at every place its claim reads, with `binding` for
    /// `name` added last (replacing that name's own binding, if it has one):
    /// every binding but the offending one is well-formed, so the refusal
    /// must name it.
    fn with_ill_formed_binding(
        &self,
        rule: OracleIllFormed,
        name: &str,
        binding: ClauseBinding,
    ) -> Self {
        let mut case = self.clone();
        let mut bindings = oracle_bindings(&self.claim.read_names());
        bindings.retain(|(bound, _)| bound != name);
        bindings.push((name.to_string(), binding));
        case.formula.bindings = bindings;
        case.label = format!("{} [ill-formed {rule:?} `{name}`]", self.label);
        case.ill_formed(rule, name)
    }

    /// Every ill-formed binding the claim admits, one per rule, the name and
    /// place picked by `rotation` so the corpus walks through them.
    #[allow(clippy::too_many_lines)]
    fn ill_formed_variants(&self, rotation: usize) -> Vec<Self> {
        let reads = self.claim.reads();
        let read = self.claim.read_names();
        let unused = ORACLE_PLACES
            .into_iter()
            .filter(|name| !read.contains(name) && !reads.let_names.contains(*name))
            .collect::<Vec<_>>();
        let mut variants = Vec::new();
        if !read.is_empty() {
            let pick = |offset: usize| read[(rotation + offset) % read.len()];
            let name = pick(0);
            let binding = if name == "b" {
                ClauseBinding {
                    sort: ClauseSort::Int,
                    place: ClausePlace::Param { index: 0 },
                }
            } else {
                ClauseBinding {
                    sort: ClauseSort::Bool,
                    place: ClausePlace::Param { index: 1 },
                }
            };
            variants.push(self.with_ill_formed_binding(OracleIllFormed::WrongSort, name, binding));

            let name = pick(1);
            let places = oracle_unresolvable_places();
            let binding = ClauseBinding {
                sort: oracle_place_binding(name).sort,
                place: places[rotation % places.len()],
            };
            variants.push(self.with_ill_formed_binding(
                OracleIllFormed::UnresolvablePlace,
                name,
                binding,
            ));

            // The sort the formula reads the name at, at a place of the other
            // type: only the place's type refuses it.
            let name = pick(2);
            let binding = if name == "b" {
                ClauseBinding {
                    sort: ClauseSort::Bool,
                    place: ClausePlace::Param { index: 0 },
                }
            } else {
                ClauseBinding {
                    sort: ClauseSort::Int,
                    place: ClausePlace::Param { index: 1 },
                }
            };
            variants.push(self.with_ill_formed_binding(
                OracleIllFormed::SortNotAdmitted,
                name,
                binding,
            ));

            // Two well-formed bindings of one name.
            let name = pick(3);
            let mut twice = self.with_ill_formed_binding(
                OracleIllFormed::DuplicateName,
                name,
                oracle_place_binding(name),
            );
            twice
                .formula
                .bindings
                .insert(0, (name.to_string(), oracle_place_binding(name)));
            variants.push(twice);

            // A bit-vector of the place's own width: the place's type admits
            // it, so only the missing model refuses it.
            let name = pick(4);
            let binding = ClauseBinding {
                sort: ClauseSort::BitVec(oracle_place_bits(name)),
                place: oracle_place_binding(name).place,
            };
            variants.push(self.with_ill_formed_binding(
                OracleIllFormed::UnmodeledSort,
                name,
                binding,
            ));
        }
        if !unused.is_empty() {
            let name = unused[rotation % unused.len()];
            variants.push(self.with_ill_formed_binding(
                OracleIllFormed::UnusedName,
                name,
                oracle_place_binding(name),
            ));
        }
        let let_bound = reads
            .let_names
            .iter()
            .filter(|name| !read.contains(&name.as_str()))
            .collect::<Vec<_>>();
        if !let_bound.is_empty() {
            let name = let_bound[rotation % let_bound.len()];
            let binding = if ORACLE_PLACES.contains(&name.as_str()) {
                oracle_place_binding(name)
            } else {
                oracle_place_binding("x")
            };
            variants.push(self.with_ill_formed_binding(
                OracleIllFormed::LetBoundName,
                name,
                binding,
            ));
        }
        if self.format() == OracleFormat::PureExpr {
            variants.extend(self.pure_expr_ill_formed_variants(rotation, &read, &unused));
        }
        variants
    }

    /// The claim with `conjunct` conjoined, bound at `name` alone (its own
    /// binding, which the conjunct makes ill-formed). Only that name is
    /// bound: a use that fixes one name's sort fixes it for every name an
    /// equality or an `if` unifies with it, so another binding could be
    /// refused first, and rightly.
    fn with_ill_formed_conjunct(&self, rule: OracleIllFormed, name: &str, conjunct: &str) -> Self {
        let mut case = self.clone();
        case.formula = ProofFormula::new(
            PURE_EXPR_SCHEMA,
            format!("({}) && ({conjunct})", self.formula.payload),
        );
        case.formula.bindings = oracle_bindings(&[name]);
        case.spells_claim = false;
        case.label = format!(
            "{} && {conjunct} [ill-formed {rule:?} `{name}`]",
            self.label
        );
        case.ill_formed(rule, name)
    }

    /// The ill-formed readings only a pure-expr payload spells: each conjoins
    /// a use that reads a name at a sort no binding of it can agree with.
    fn pure_expr_ill_formed_variants(
        &self,
        rotation: usize,
        read: &[&'static str],
        unused: &[&'static str],
    ) -> Vec<Self> {
        let mut variants = Vec::new();
        if !read.is_empty() {
            // Read as an integer by arithmetic and as a boolean by a
            // connective. The conjunct fixes both itself: the claim's own
            // uses may fix neither (`old(y) != old(y)`).
            let name = read[rotation % read.len()];
            let conjunct = if name == "b" {
                "(b || !b) && ((b + 1) > b)".to_string()
            } else {
                format!("({name} + 0 >= 0) && ({name} || !{name})")
            };
            variants.push(self.with_ill_formed_conjunct(
                OracleIllFormed::ConflictingUses,
                name,
                &conjunct,
            ));
            // Compared by `==` with a value of the other sort than an
            // arithmetic or connective use reads it at: only the equality
            // carries the second sort.
            let name = read[(rotation + 1) % read.len()];
            let conjunct = if name == "b" {
                "(b || !b) && (b == 0)".to_string()
            } else {
                format!("({name} + 0 >= 0) && ({name} == true)")
            };
            variants.push(self.with_ill_formed_conjunct(
                OracleIllFormed::EqualitySides,
                name,
                &conjunct,
            ));
        }
        // Read through a reference operator: a name the claim does not read
        // otherwise, so the reference reading is its only one, else one it
        // reads, so the readings conflict.
        let pool = if unused.is_empty() { read } else { unused };
        if !pool.is_empty() {
            let name = pool[rotation % pool.len()];
            let op = if rotation % 2 == 0 { "*" } else { "^" };
            variants.push(self.with_ill_formed_conjunct(
                OracleIllFormed::ReferenceRead,
                name,
                &format!("{op}{name} == {op}{name}"),
            ));
        }
        // An integer place's name as an `if` condition.
        let integers = |names: &[&'static str]| {
            names
                .iter()
                .copied()
                .filter(|name| *name != "b")
                .collect::<Vec<_>>()
        };
        let pool = if integers(unused).is_empty() {
            integers(read)
        } else {
            integers(unused)
        };
        if !pool.is_empty() {
            let name = pool[rotation % pool.len()];
            variants.push(self.with_ill_formed_conjunct(
                OracleIllFormed::IfCondition,
                name,
                &format!("(if {name} {{ 1 }} else {{ 0 }}) >= 0"),
            ));
        }
        variants
    }

    /// Well-formed claims that read `b` only where a boolean reading comes
    /// from an equality with a literal or from an `if` condition, and bind
    /// it: the reading must admit the `Bool` binding. `None` when the claim
    /// already reads `b`, which would fix its sort by another use.
    fn bool_name_variants(&self, rotation: usize) -> Vec<Self> {
        if self.claim.read_names().contains(&"b") {
            return Vec::new();
        }
        let literal = rotation % 2 == 0;
        let equality = OracleClaim::BCmp(rotation % 3 != 0, literal);
        let condition = oracle_cmp(
            OracleCmp::Ge,
            OracleTerm::Ite(
                Box::new(OracleClaim::B),
                Box::new(OracleTerm::Lit(1)),
                Box::new(OracleTerm::Lit(0)),
            ),
            OracleTerm::Lit(0),
        );
        [("==", equality), ("if", condition)]
            .into_iter()
            .filter_map(|(how, extra)| {
                let claim = oracle_and(self.claim.clone(), extra);
                OracleCase::new(
                    format!("{} [b read by {how}]", self.label),
                    claim,
                    self.format(),
                    true,
                    self.kind.clone(),
                    self.mode,
                )
            })
            .collect()
    }

    /// The pure-expr claim with a construct the reading does not model
    /// conjoined, bound as the claim is.
    fn unmodeled_variant(&self, rotation: usize) -> Option<Self> {
        if self.format() != OracleFormat::PureExpr {
            return None;
        }
        let (conjunct, named) = ORACLE_UNMODELED[rotation % ORACLE_UNMODELED.len()];
        let mut case = self.clone();
        let bindings = std::mem::take(&mut case.formula.bindings);
        case.formula = ProofFormula::new(
            PURE_EXPR_SCHEMA,
            format!("({}) && ({conjunct})", self.formula.payload),
        );
        case.formula.bindings = bindings;
        case.spells_claim = false;
        case.label = format!("{} && {conjunct} [unmodeled]", self.label);
        case.unmodeled = Some(named);
        Some(case)
    }

    /// The pure-expr claim, unbound, with a disjunct that reads one of its
    /// names as both an `Int` and a `Bool` through ascriptions, each half of
    /// which native replay types and decides: no binding is there to refuse
    /// it, so only the claim's own reading can.
    fn ill_sorted_variant(&self, rotation: usize) -> Option<Self> {
        if self.format() != OracleFormat::PureExpr {
            return None;
        }
        let read = self.claim.read_names();
        let name = *read.get(rotation % read.len().max(1))?;
        let disjunct = if name == "b" {
            "((b : Int) == (b : Int)) || ((b : bool) == (b : bool))".to_string()
        } else {
            format!("(({name} : bool) == ({name} : bool)) || ({name} + 0 >= {name})")
        };
        let mut case = self.clone();
        case.formula = ProofFormula::new(
            PURE_EXPR_SCHEMA,
            format!("({}) || ({disjunct})", self.formula.payload),
        );
        case.spells_claim = false;
        case.label = format!("{} || {disjunct} [ill-sorted]", self.label);
        case.ill_sorted = Some(ORACLE_ILL_SORTED);
        Some(case)
    }

    /// The trust-formula claim under a `let` whose declared sort is not its
    /// value's: the decoder must refuse it naming the declaration.
    fn ill_sorted_let_variant(&self) -> Option<Self> {
        if self.format() != OracleFormat::TrustFormula {
            return None;
        }
        let mut envelope =
            serde_json::from_str::<serde_json::Value>(&self.formula.payload).expect("json");
        let body = envelope["body"].take();
        envelope["body"] = serde_json::json!({
            "op": "let",
            "name": "tq",
            "sort": "bool",
            "value": {"int": 1},
            "body": body,
        });
        let mut case = self.clone();
        let bindings = std::mem::take(&mut case.formula.bindings);
        case.formula = ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, envelope.to_string());
        case.formula.bindings = bindings;
        case.spells_claim = false;
        case.label = format!("let tq: bool = 1 in {} [ill-sorted let]", self.label);
        case.unmodeled = Some(ORACLE_ILL_SORTED_LET);
        Some(case)
    }

    /// The claim with `disjunct` (a pure-expr spelling, or a trust-formula
    /// body) or-ed on, bound as the claim is.
    fn with_disjunct(&self, pure_expr: &str, trust_formula: serde_json::Value) -> Self {
        let mut case = self.clone();
        let bindings = std::mem::take(&mut case.formula.bindings);
        case.formula = match self.format() {
            OracleFormat::PureExpr => ProofFormula::new(
                PURE_EXPR_SCHEMA,
                format!("({}) || ({pure_expr})", self.formula.payload),
            ),
            OracleFormat::TrustFormula => {
                let mut envelope =
                    serde_json::from_str::<serde_json::Value>(&self.formula.payload).expect("json");
                let body = envelope["body"].take();
                envelope["body"] =
                    serde_json::json!({"op": "or", "lhs": body, "rhs": trust_formula});
                ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, envelope.to_string())
            }
        };
        case.formula.bindings = bindings;
        case.spells_claim = false;
        case
    }

    /// The pure-expr claim or a disjunct reading a bound name at a sort its
    /// binder does not give it: it must not decode, and must be refused
    /// naming the name.
    fn bound_ill_sorted_variant(&self, rotation: usize) -> Option<Self> {
        if self.format() != OracleFormat::PureExpr {
            return None;
        }
        let (disjunct, named) = ORACLE_BOUND_ILL_SORTED[rotation % ORACLE_BOUND_ILL_SORTED.len()];
        let mut case = self.with_disjunct(disjunct, serde_json::Value::Null);
        case.label = format!("{} || {disjunct} [bound ill-sorted]", self.label);
        case.unmodeled = Some(named);
        Some(case)
    }

    /// The claim or a disjunct quantifying over a sort native replay does
    /// not model, in the claim's format: it must not decode, and must be
    /// refused naming the binder's type.
    fn unmodeled_binder_variant(&self, rotation: usize) -> Self {
        let (label, named, case) = match self.format() {
            OracleFormat::PureExpr => {
                let (disjunct, named) =
                    ORACLE_UNMODELED_BINDERS[rotation % ORACLE_UNMODELED_BINDERS.len()];
                (
                    disjunct.to_string(),
                    named,
                    self.with_disjunct(disjunct, serde_json::Value::Null),
                )
            }
            OracleFormat::TrustFormula => {
                let (op, sort, named) =
                    ORACLE_TF_UNMODELED_BINDERS[rotation % ORACLE_TF_UNMODELED_BINDERS.len()];
                let successor = serde_json::json!({
                    "op": "gt",
                    "lhs": {"op": "add", "lhs": {"var": "wt"}, "rhs": {"int": 1}},
                    "rhs": {"var": "wt"},
                });
                (
                    format!("{op} wt: {sort}. wt + 1 > wt"),
                    named,
                    self.with_disjunct(
                        "",
                        serde_json::json!({"op": op, "name": "wt", "sort": sort, "body": successor}),
                    ),
                )
            }
        };
        let mut case = case;
        case.label = format!("{} || {label} [unmodeled binder]", self.label);
        case.unmodeled = Some(named);
        case
    }

    /// `(claim && X) || (!claim && !X)` for an `X` whose truth turns on
    /// whether a reference's referent type is inhabited: whatever the claim,
    /// the whole is as undecided as `X`, and so is its negation. Pre-fix,
    /// `X` verified and the whole verified wherever the claim did.
    fn empty_domain_variant(&self, rotation: usize) -> Self {
        let which = rotation % ORACLE_EMPTY_DOMAIN.len();
        let mut case = self.clone();
        let bindings = std::mem::take(&mut case.formula.bindings);
        case.formula = match self.format() {
            OracleFormat::PureExpr => {
                let (claim, witness) = (&self.formula.payload, ORACLE_EMPTY_DOMAIN[which]);
                ProofFormula::new(
                    PURE_EXPR_SCHEMA,
                    format!("(({claim}) && ({witness})) || (!({claim}) && !({witness}))"),
                )
            }
            OracleFormat::TrustFormula => {
                use serde_json::json;
                let witness = match which {
                    0 => {
                        json!({"op": "exists", "name": "wp", "sort": "&T", "body": {"bool": true}})
                    }
                    1 => json!({"op": "not", "expr": {
                        "op": "forall", "name": "wp", "sort": "&T", "body": {"bool": false}
                    }}),
                    _ => json!({"op": "exists", "name": "wp", "sort": "&mut T", "body": {
                        "op": "eq", "lhs": {"var": "wp"}, "rhs": {"var": "wp"}
                    }}),
                };
                let mut envelope =
                    serde_json::from_str::<serde_json::Value>(&self.formula.payload).expect("json");
                let claim = envelope["body"].take();
                envelope["body"] = json!({
                    "op": "or",
                    "lhs": {"op": "and", "lhs": claim.clone(), "rhs": witness.clone()},
                    "rhs": {"op": "and",
                        "lhs": {"op": "not", "expr": claim},
                        "rhs": {"op": "not", "expr": witness}},
                });
                ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, envelope.to_string())
            }
        };
        case.formula.bindings = bindings;
        case.spells_claim = false;
        case.witness_needed = true;
        case.label = format!(
            "({0}) iff {1} [empty domain]",
            self.label, ORACLE_EMPTY_DOMAIN[which]
        );
        case
    }

    /// The pure-expr claim or a disjunct dereferencing a value at a sort it
    /// has no reading at: it decodes, and must be refused naming why.
    fn deref_ill_sorted_variant(&self, rotation: usize) -> Option<Self> {
        if self.format() != OracleFormat::PureExpr {
            return None;
        }
        let (disjunct, named) = ORACLE_DEREF_ILL_SORTED[rotation % ORACLE_DEREF_ILL_SORTED.len()];
        let mut case = self.with_disjunct(disjunct, serde_json::Value::Null);
        case.label = format!("{} || {disjunct} [dereference ill-sorted]", self.label);
        case.ill_sorted = Some(named);
        Some(case)
    }

    /// The pure-expr claim or a disjunct annotating a dereference: it must
    /// not decode, and must be refused naming the annotation.
    fn deref_unmodeled_variant(&self, rotation: usize) -> Option<Self> {
        if self.format() != OracleFormat::PureExpr {
            return None;
        }
        let (disjunct, named) = ORACLE_DEREF_UNMODELED[rotation % ORACLE_DEREF_UNMODELED.len()];
        let mut case = self.with_disjunct(disjunct, serde_json::Value::Null);
        case.label = format!("{} || {disjunct} [dereference annotated]", self.label);
        case.unmodeled = Some(named);
        Some(case)
    }

    /// `(C && X) || (!C && !X)` for a well-sorted dereference claim `X` of
    /// known truth, read by the evaluator as `C` (valid `X`) or `!C` (false
    /// `X`): a verdict must agree with it, and one needs `X` proved.
    fn deref_modeled_variant(&self, rotation: usize) -> Option<Self> {
        if self.format() != OracleFormat::PureExpr {
            return None;
        }
        let (witness, valid) = ORACLE_DEREF_MODELED[rotation % ORACLE_DEREF_MODELED.len()];
        let mut case = self.clone();
        let bindings = std::mem::take(&mut case.formula.bindings);
        let claim = &self.formula.payload;
        case.formula = ProofFormula::new(
            PURE_EXPR_SCHEMA,
            format!("(({claim}) && ({witness})) || (!({claim}) && !({witness}))"),
        );
        case.formula.bindings = bindings;
        if !valid {
            case.claim = oracle_not(self.claim.clone());
        }
        case.dereferences = true;
        case.label = format!("({0}) iff {witness} [dereference]", self.label);
        Some(case)
    }

    fn negated(&self) -> Self {
        let mut negated = self.clone();
        negated.label = format!("not({})", self.label);
        negated.claim = oracle_not(self.claim.clone());
        let bindings = std::mem::take(&mut negated.formula.bindings);
        negated.formula = if self.formula.schema == TRUST_FORMULA_CLAIM_SCHEMA_VERSION {
            let mut envelope =
                serde_json::from_str::<serde_json::Value>(&self.formula.payload).expect("json");
            let body = envelope["body"].take();
            envelope["body"] = serde_json::json!({"op": "not", "expr": body});
            ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, envelope.to_string())
        } else {
            ProofFormula::new(
                self.formula.schema.clone(),
                format!("!({})", self.formula.payload),
            )
        };
        negated.formula.bindings = bindings;
        negated
    }

    fn bundle(&self) -> NativeVerificationBundle {
        let cause = match self.kind {
            ObligationKind::Precondition => NativeObligationCause::Precondition,
            _ => NativeObligationCause::Postcondition,
        };
        let mut bundle = native_bundle_with_signature(
            self.formula.clone(),
            self.mode,
            vec![Ty::U64, Ty::Bool, Ty::RefMut(Box::new(Ty::I32)), Ty::I64],
            vec![Ty::U8],
        );
        bundle.module.proof_obligations[0].kind = self.kind.clone();
        bundle.compiler_facts.obligation_sources[0].cause = cause;
        refresh_native_bundle_module_identity(&mut bundle);
        bundle
    }

    /// Whether the native bundle path reports the claim verified, by status or
    /// by exit code. A refusal before verification is not a verdict.
    fn verified(&self) -> bool {
        verify_trust_ir_native_bundle(&self.bundle()).is_ok_and(|results| {
            results.iter().any(|result| {
                result.status == VerifyBundleStatus::Verified || result.exit_code() == 0
            })
        })
    }
}

#[derive(Debug, Default)]
struct OracleReport {
    claims: usize,
    verified: usize,
    /// Of `verified`, the pure-expr claims.
    verified_pure_expr: usize,
    /// Of `verified`, the strongest-postcondition requests.
    verified_strongest_postcondition: usize,
    /// Of `verified`, the claims using mul, div, mod, neg, ite or a cast.
    verified_extended: usize,
    /// Of `verified`, the claims using a cast.
    verified_cast: usize,
    /// Of `verified`, the pure-expr claims that bind `b` as a `Bool`.
    verified_bound_bool_name: usize,
    /// Of `claims`, those writing a construct the reading does not model,
    /// which must never verify.
    unmodeled_claims: usize,
    /// Refusals of an unmodeled construct or of a claim with no one
    /// reading, by what the refusal names.
    refused_unmodeled: std::collections::BTreeMap<&'static str, usize>,
    /// Of `verified`, the claims holding a quantifier, and an `exists`.
    verified_quantified: usize,
    verified_exists: usize,
    /// Of `claims`, those whose truth turns on whether a sort is inhabited,
    /// which must never verify, and of those the ones refused naming it.
    witness_claims: usize,
    refused_witness: usize,
    /// Of `claims`, those that decode but have no one reading: a name read
    /// at two sorts, or a dereference of what is no reference to a modeled
    /// sort.
    ill_sorted_claims: usize,
    /// Of those, the ones refused naming why.
    refused_ill_sorted: usize,
    /// Of `verified`, the claims reading a well-sorted dereference.
    verified_dereference: usize,
    /// Of `claims`, those with an ill-formed binding, which must never verify.
    ill_formed_claims: usize,
    /// Ill-formed bindings refused by the rule they break, by rule and format.
    refused: std::collections::BTreeMap<(OracleIllFormed, OracleFormat), usize>,
    violations: Vec<String>,
}

impl OracleReport {
    /// An ill-formed case must be refused before verification, naming the
    /// offending binding, by the rule it breaks; a well-formed one must decode
    /// and have its bindings admitted, or the oracle would be checking a
    /// refusal instead of a verdict.
    fn check_admission(&mut self, case: &OracleCase) {
        let format = case.format();
        let claim_format = match format {
            OracleFormat::TrustFormula => BundleClaimFormat::TrustFormulaV1,
            OracleFormat::PureExpr => BundleClaimFormat::TrustWpPureExprV1,
        };
        let decodes = trust_wp_core::verify_bundle::native_claim_names(&BundleClaim::new(
            claim_format,
            case.formula.payload.clone(),
        ))
        .is_some();
        if let Some(named) = case.unmodeled {
            self.check_unmodeled(case, named, decodes);
            return;
        }
        if let Some(named) = case.ill_sorted {
            self.check_ill_sorted(case, named, decodes);
            return;
        }
        if !decodes {
            self.violations.push(format!(
                "{} does not decode, so it checks nothing: {}",
                case.label, case.formula.payload
            ));
        }
        if case.witness_needed {
            if let Ok(results) = verify_trust_ir_native_bundle(&case.bundle()) {
                if results[0].status == VerifyBundleStatus::Unsupported
                    && refusal_messages(&results[0])
                        .iter()
                        .any(|message| message.contains(ORACLE_WITNESS_NEEDED))
                {
                    self.refused_witness += 1;
                }
            }
        }
        let converted = trust_ir_native_bundle_to_verify_requests(&case.bundle());
        match (&case.ill_formed, converted) {
            (None, Ok(_)) => {}
            (None, Err(error)) => self.violations.push(format!(
                "{} has well-formed bindings and was refused: {error}",
                case.label
            )),
            (Some(ill), Ok(_)) => self.violations.push(format!(
                "{} was admitted although it breaks {:?}",
                case.label, ill.rule
            )),
            (
                Some(ill),
                Err(TrustIrNativeBundleError::UnsupportedClauseBinding {
                    carrier: TrustIrClauseCarrier::Obligation,
                    name,
                    reason,
                    ..
                }),
            ) if name == ill.name && ill.rule.refuses_with(&reason, format) => {
                *self.refused.entry((ill.rule, format)).or_default() += 1;
            }
            (Some(ill), Err(error)) => self.violations.push(format!(
                "{} breaks {:?} at `{}` but was refused otherwise: {error}",
                case.label, ill.rule, ill.name
            )),
        }
    }

    /// A claim writing a construct the reading does not model must not
    /// decode, and must be refused naming the construct.
    fn check_unmodeled(&mut self, case: &OracleCase, named: &'static str, decodes: bool) {
        if decodes {
            self.violations.push(format!(
                "{} decodes although it writes {named}: {}",
                case.label, case.formula.payload
            ));
        }
        match verify_trust_ir_native_bundle(&case.bundle()) {
            Ok(results) => {
                let messages = refusal_messages(&results[0]);
                if matches!(
                    results[0].status,
                    VerifyBundleStatus::Invalid | VerifyBundleStatus::Unsupported
                ) && messages.iter().any(|message| message.contains(named))
                {
                    *self.refused_unmodeled.entry(named).or_default() += 1;
                } else {
                    self.violations.push(format!(
                        "{} is {:?}, not refused naming {named}: {messages:?}",
                        case.label, results[0].status
                    ));
                }
            }
            Err(error) => self.violations.push(format!(
                "{} was refused before it could name {named}: {error}",
                case.label
            )),
        }
    }

    /// A claim reading a name at two sorts (or dereferencing what is no
    /// reference to a modeled sort) decodes, and must be refused before any
    /// verdict, naming `named`.
    fn check_ill_sorted(&mut self, case: &OracleCase, named: &'static str, decodes: bool) {
        if !decodes {
            self.violations.push(format!(
                "{} does not decode, so it checks nothing: {}",
                case.label, case.formula.payload
            ));
        }
        match verify_trust_ir_native_bundle(&case.bundle()) {
            Ok(results) => {
                let messages = refusal_messages(&results[0]);
                if results[0].status == VerifyBundleStatus::Invalid
                    && messages.iter().any(|message| message.contains(named))
                {
                    self.refused_ill_sorted += 1;
                    *self.refused_unmodeled.entry(named).or_default() += 1;
                } else {
                    self.violations.push(format!(
                        "{} has no one reading and is {:?}, not refused naming {named}: {messages:?}",
                        case.label, results[0].status
                    ));
                }
            }
            Err(error) => self.violations.push(format!(
                "{} is unbound and was refused at conversion: {error}",
                case.label
            )),
        }
    }

    /// Check `case` and its negation against both properties.
    fn check_pair(&mut self, case: &OracleCase) {
        let negated = case.negated();
        self.check_admission(case);
        self.check_admission(&negated);
        let verdicts = [(case, case.verified()), (&negated, negated.verified())];
        for (checked, verified) in verdicts {
            self.claims += 1;
            if checked.ill_formed.is_some() {
                self.ill_formed_claims += 1;
            }
            if checked.unmodeled.is_some() {
                self.unmodeled_claims += 1;
            }
            if checked.ill_sorted.is_some() {
                self.ill_sorted_claims += 1;
            }
            if checked.witness_needed {
                self.witness_claims += 1;
            }
            if !verified {
                continue;
            }
            self.verified += 1;
            if checked.witness_needed {
                self.violations.push(format!(
                    "{} VERIFIED although its truth turns on whether a sort is inhabited: {}",
                    checked.label, checked.formula.payload
                ));
            }
            if let Some(named) = checked.unmodeled {
                self.violations.push(format!(
                    "{} VERIFIED although it writes {named}: {}",
                    checked.label, checked.formula.payload
                ));
            }
            if let Some(named) = checked.ill_sorted {
                self.violations.push(format!(
                    "{} VERIFIED although it has no one reading ({named}): {}",
                    checked.label, checked.formula.payload
                ));
            }
            if checked.dereferences {
                self.verified_dereference += 1;
            }
            if checked.claim.has_cast() {
                self.verified_cast += 1;
            }
            if checked.spells_claim {
                let (quantified, exists) = checked.claim.quantifiers();
                self.verified_quantified += usize::from(quantified);
                self.verified_exists += usize::from(exists);
            }
            if checked.format() == OracleFormat::PureExpr
                && checked.formula.bindings.iter().any(|(name, _)| name == "b")
            {
                self.verified_bound_bool_name += 1;
            }
            if checked.format() == OracleFormat::PureExpr {
                self.verified_pure_expr += 1;
            }
            if checked.mode == TrustWpVerificationMode::StrongestPostcondition {
                self.verified_strongest_postcondition += 1;
            }
            if checked.claim.is_extended() {
                self.verified_extended += 1;
            }
            let kind = checked.kind.to_string();
            if let Some(ill) = &checked.ill_formed {
                self.violations.push(format!(
                    "{} [{kind}] VERIFIED although it breaks {:?}: {}",
                    checked.label, ill.rule, checked.formula.payload
                ));
            }
            if !checked.spells_claim {
                continue;
            }
            if let Some(point) = checked.claim.falsifying_point() {
                self.violations.push(format!(
                    "{} [{kind}] VERIFIED but is false at {:?} (b = {}): {}",
                    checked.label, point.ints, point.b, checked.formula.payload
                ));
            }
        }
        if verdicts[0].1 && verdicts[1].1 {
            self.violations.push(format!(
                "{} [{}] VERIFIED together with its negation: {}",
                case.label, case.kind, case.formula.payload
            ));
        }
    }

    /// Not vacuous: the path proves a real share of the well-formed corpus,
    /// in both formats and both modes, with the extended operators and casts
    /// among what it proves; every binding rule refuses its ill-formed
    /// bindings in every format that can spell them; and every unmodeled
    /// construct is refused naming it.
    fn assert_not_vacuous(&self) {
        let well_formed = self.claims
            - self.ill_formed_claims
            - self.unmodeled_claims
            - self.ill_sorted_claims
            - self.witness_claims;
        assert!(
            self.verified * 10 >= well_formed
                && self.verified_pure_expr * 50 >= well_formed
                && self.verified_strongest_postcondition * 50 >= well_formed
                && self.verified_extended * 100 >= well_formed
                && self.verified_cast * 400 >= well_formed
                && self.verified_bound_bool_name * 400 >= well_formed,
            "only {} of {well_formed} well-formed claims verified ({} pure-expr, {} strongest-postcondition, {} extended, {} with a cast, {} pure-expr binding `b`); the oracle checks too little",
            self.verified,
            self.verified_pure_expr,
            self.verified_strongest_postcondition,
            self.verified_extended,
            self.verified_cast,
            self.verified_bound_bool_name
        );
        for rule in OracleIllFormed::ALL {
            for format in [OracleFormat::TrustFormula, OracleFormat::PureExpr] {
                if rule.pure_expr_only() && format == OracleFormat::TrustFormula {
                    continue;
                }
                assert!(
                    self.refused.get(&(rule, format)).copied().unwrap_or(0) >= 4,
                    "the corpus refuses too few {rule:?} bindings in {format:?}: {:?}",
                    self.refused
                );
            }
        }
        assert!(
            self.refused_ill_sorted >= 8 && self.refused_ill_sorted == self.ill_sorted_claims,
            "{} of {} claims reading a name at two sorts refused naming them",
            self.refused_ill_sorted,
            self.ill_sorted_claims
        );
        assert!(
            self.verified_quantified >= 40 && self.verified_exists >= 10,
            "only {} verified claims hold a quantifier ({} an `exists`); the oracle checks too little",
            self.verified_quantified,
            self.verified_exists
        );
        assert!(
            self.refused_witness >= 20,
            "{} of {} claims whose truth turns on an inhabited sort refused naming it",
            self.refused_witness,
            self.witness_claims
        );
        assert!(
            self.verified_dereference >= 40,
            "only {} verified claims read a well-sorted dereference; the oracle checks too little",
            self.verified_dereference
        );
        for named in ORACLE_UNMODELED
            .into_iter()
            .map(|(_, named)| named)
            .chain([ORACLE_ILL_SORTED_LET])
            .chain(ORACLE_DEREF_ILL_SORTED.into_iter().map(|(_, named)| named))
            .chain(ORACLE_DEREF_UNMODELED.into_iter().map(|(_, named)| named))
            .chain(ORACLE_BOUND_ILL_SORTED.into_iter().map(|(_, named)| named))
            .chain(ORACLE_UNMODELED_BINDERS.into_iter().map(|(_, named)| named))
            .chain(
                ORACLE_TF_UNMODELED_BINDERS
                    .into_iter()
                    .map(|(_, _, named)| named),
            )
        {
            assert!(
                self.refused_unmodeled.get(named).copied().unwrap_or(0) >= 2,
                "the corpus refuses too few claims writing {named}: {:?}",
                self.refused_unmodeled
            );
        }
    }

    fn assert_sound(&self) {
        assert!(
            self.violations.is_empty(),
            "{} of {} claims break the oracle ({} verified):\n{}",
            self.violations.len(),
            self.claims,
            self.verified,
            self.violations.join("\n")
        );
    }
}

fn oracle_x() -> OracleTerm {
    OracleTerm::Place("x")
}

const ORACLE_MODES: [TrustWpVerificationMode; 2] = [
    TrustWpVerificationMode::WeakestPrecondition,
    TrustWpVerificationMode::StrongestPostcondition,
];

/// Every false claim measured VERIFIED through this path, plus the ill-formed
/// bindings that bought a verdict, each in every obligation kind trust-wp
/// owns and every mode the bundle path supports.
fn oracle_seed_cases() -> Vec<OracleCase> {
    let x_plus_one_gt_x = oracle_cmp(
        OracleCmp::Gt,
        oracle_add(oracle_x(), OracleTerm::Lit(1)),
        oracle_x(),
    );
    let x_ge_zero = oracle_cmp(OracleCmp::Ge, oracle_x(), OracleTerm::Lit(0));
    let old_m = OracleTerm::Old("m");
    let claims = [
        ("not(true)", oracle_not(OracleClaim::Lit(true)), vec![]),
        ("not(x+1>x)", oracle_not(x_plus_one_gt_x.clone()), vec!["x"]),
        (
            "(x>=0) and not(x+1>x)",
            oracle_and(x_ge_zero.clone(), oracle_not(x_plus_one_gt_x.clone())),
            vec!["x"],
        ),
        (
            "(x>=0) and not(x>=0)",
            oracle_and(x_ge_zero.clone(), oracle_not(x_ge_zero)),
            vec!["x"],
        ),
        (
            "not(old(m)==old(m))",
            oracle_not(oracle_cmp(OracleCmp::Eq, old_m.clone(), old_m)),
            vec!["m"],
        ),
    ];
    let kinds = [
        ObligationKind::Postcondition,
        ObligationKind::Precondition,
        ObligationKind::LoopInvariant,
    ];

    let mut cases = Vec::new();
    for mode in ORACLE_MODES {
        for kind in &kinds {
            for (label, claim, bound) in &claims {
                let payload = claim
                    .trust_formula_payload()
                    .expect("a seed claim is spellable");
                cases.push(OracleCase::hand_written(
                    label,
                    claim.clone(),
                    TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
                    &payload,
                    bound,
                    kind.clone(),
                    mode,
                ));
                cases.push(OracleCase::hand_written(
                    &format!("{label} unbound"),
                    claim.clone(),
                    TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
                    &payload,
                    &[],
                    kind.clone(),
                    mode,
                ));
            }
            for bindings in [&["x"][..], &[]] {
                cases.push(OracleCase::hand_written(
                    "pure-expr !(x + 1 > x)",
                    oracle_not(x_plus_one_gt_x.clone()),
                    PURE_EXPR_SCHEMA,
                    "!(x + 1 > x)",
                    bindings,
                    kind.clone(),
                    mode,
                ));
            }
            // A cast read as its operand: false at x = 256 and at y = -1.
            for (place, ty, payload) in [
                ("x", OracleIntTy::U8, "(x as u8) == x"),
                ("y", OracleIntTy::U64, "(y as u64) == y"),
            ] {
                let claim = oracle_cmp(
                    OracleCmp::Eq,
                    OracleTerm::Cast(Box::new(OracleTerm::Place(place)), ty),
                    OracleTerm::Place(place),
                );
                for bindings in [&[place][..], &[]] {
                    cases.push(OracleCase::hand_written(
                        &format!("pure-expr {payload}"),
                        claim.clone(),
                        PURE_EXPR_SCHEMA,
                        payload,
                        bindings,
                        kind.clone(),
                        mode,
                    ));
                }
            }
            cases.extend(oracle_ill_formed_seed_cases(kind, mode));
        }
    }
    cases
}

/// Claims whose bindings bought a verdict for a claim they do not describe.
fn oracle_ill_formed_seed_cases(
    kind: &ObligationKind,
    mode: TrustWpVerificationMode,
) -> [OracleCase; 5] {
    let x_plus_one_gt_x = oracle_cmp(
        OracleCmp::Gt,
        oracle_add(oracle_x(), OracleTerm::Lit(1)),
        oracle_x(),
    );
    let pure_x_as_bool = |label: &str, claim: OracleClaim, payload: &str| {
        let mut case = OracleCase::hand_written(
            label,
            claim,
            PURE_EXPR_SCHEMA,
            payload,
            &[],
            kind.clone(),
            mode,
        );
        case.formula.bindings = vec![(
            "x".to_string(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 1 },
            },
        )];
        case.ill_formed(OracleIllFormed::WrongSort, "x")
    };
    [
        // The binding names `result`, which the formula binds itself: the
        // claim is `x + 1 > x`, and nothing in it is the u8 result slot.
        OracleCase::hand_written(
            "let result = x+1 in result > x, result bound to the result slot",
            OracleClaim::Let(
                "result".to_string(),
                oracle_add(oracle_x(), OracleTerm::Lit(1)),
                Box::new(oracle_cmp(
                    OracleCmp::Gt,
                    OracleTerm::LetBound("result".to_string()),
                    oracle_x(),
                )),
                false,
            ),
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            r#"{
                "schema": "trust-wp.trust-formula.v1",
                "variables": [{"name": "x", "sort": "int"}],
                "body": {
                    "op": "let",
                    "name": "result",
                    "sort": "int",
                    "value": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                    "body": {"op": "gt", "lhs": {"var": "result"}, "rhs": {"var": "x"}}
                }
            }"#,
            &["x", "result"],
            kind.clone(),
            mode,
        )
        .ill_formed(OracleIllFormed::LetBoundName, "result"),
        // The formula declares `result` as bool through the decoder's default
        // name; the binding says Int. The evaluator has no reading for a claim
        // whose name has two sorts, so only the ill-formed rule applies.
        OracleCase::hand_written(
            "result: bool by default name, bound as Int",
            OracleClaim::Lit(true),
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            r#"{
                "schema": "trust-wp.trust-formula.v1",
                "variables": [],
                "result": {"sort": "bool"},
                "body": {"op": "implies", "lhs": {"result": true}, "rhs": {"result": true}}
            }"#,
            &["result"],
            kind.clone(),
            mode,
        )
        .ill_formed(OracleIllFormed::WrongSort, "result"),
        // A pure-expr name read as an integer, bound as the bool parameter.
        pure_x_as_bool(
            "pure-expr x + 1 > x, x: Bool",
            x_plus_one_gt_x.clone(),
            "x + 1 > x",
        ),
        pure_x_as_bool(
            "pure-expr x == x, x: Bool",
            oracle_cmp(OracleCmp::Eq, oracle_x(), oracle_x()),
            "x == x",
        ),
        // `r` is declared and never read; the binding says the claim is about
        // the u8 result slot.
        OracleCase::hand_written(
            "x+1>x with declared-unused r bound to the result slot",
            x_plus_one_gt_x,
            TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            r#"{
                "schema": "trust-wp.trust-formula.v1",
                "variables": [{"name": "x", "sort": "int"}, {"name": "r", "sort": "int"}],
                "body": {
                    "op": "gt",
                    "lhs": {"op": "add", "lhs": {"var": "x"}, "rhs": {"int": 1}},
                    "rhs": {"var": "x"}
                }
            }"#,
            &["x"],
            kind.clone(),
            mode,
        )
        .with_extra_binding("r", oracle_place_binding("result"))
        .ill_formed(OracleIllFormed::UnusedName, "r"),
    ]
}

impl OracleCase {
    fn with_extra_binding(mut self, name: &str, binding: ClauseBinding) -> Self {
        self.formula.bindings.push((name.to_string(), binding));
        self
    }
}

/// The seeds break the oracle only if one of them verifies; each is checked
/// with its negation, and the valid negations are the controls that show the
/// path still proves what it should.
#[test]
fn test_trust_ir_native_soundness_oracle_seeds() {
    let mut report = OracleReport::default();
    for case in oracle_seed_cases() {
        report.check_pair(&case);
    }
    report.assert_sound();

    for mode in ORACLE_MODES {
        for (label, claim, bindings) in [
            ("not(false)", oracle_not(OracleClaim::Lit(false)), vec![]),
            (
                "x+1>x",
                oracle_cmp(
                    OracleCmp::Gt,
                    oracle_add(oracle_x(), OracleTerm::Lit(1)),
                    oracle_x(),
                ),
                vec!["x"],
            ),
            (
                "not(x>x)",
                oracle_not(oracle_cmp(OracleCmp::Gt, oracle_x(), oracle_x())),
                vec!["x"],
            ),
        ] {
            let case = OracleCase::hand_written(
                label,
                claim.clone(),
                TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
                &claim
                    .trust_formula_payload()
                    .expect("a control claim is spellable"),
                &bindings,
                ObligationKind::Postcondition,
                mode,
            );
            assert!(case.verified(), "control `{label}` must verify in {mode:?}");
        }
    }
}

/// xorshift64*: the corpus is identical on every run.
struct OracleRng(u64);

impl OracleRng {
    fn next(&mut self) -> u64 {
        let mut state = self.0;
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        self.0 = state;
        state.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).expect("bound fits")).expect("fits")
    }

    fn pick<T: Clone>(&mut self, items: &[T]) -> T {
        items[self.below(items.len())].clone()
    }
}

/// The names a generated claim may read at a point, besides the places.
#[derive(Debug, Clone, Default)]
struct OracleScope {
    /// Integer names a `let` or an `Int` quantifier binds, innermost last.
    ints: Vec<String>,
    /// Boolean names a `bool` quantifier binds.
    bools: Vec<String>,
    /// Whether quantifiers, typed `let`s and ascriptions are generated. Off,
    /// the generator draws exactly what it drew before they existed, so the
    /// base corpus is unchanged.
    quantifiers: bool,
}

impl OracleScope {
    fn with_quantifiers() -> Self {
        Self {
            quantifiers: true,
            ..Self::default()
        }
    }

    /// A fresh name for the next binder, distinct from every name in scope.
    fn fresh(&self, prefix: char) -> String {
        format!("{prefix}{}", self.ints.len() + self.bools.len())
    }
}

/// A term of at most `depth` operators. A place a `let` in scope rebinds is
/// never generated: its spelling names the let.
fn oracle_term(rng: &mut OracleRng, depth: usize, scope: &OracleScope) -> OracleTerm {
    if depth > 0 && rng.below(3) == 0 {
        let division = if rng.below(2) == 0 {
            OracleDivision::Euclidean
        } else {
            OracleDivision::Truncating
        };
        return match rng.below(8) {
            0 => {
                let left = oracle_term(rng, depth - 1, scope);
                OracleTerm::Add(Box::new(left), Box::new(oracle_term(rng, depth - 1, scope)))
            }
            1 => {
                let left = oracle_term(rng, depth - 1, scope);
                OracleTerm::Sub(Box::new(left), Box::new(oracle_term(rng, depth - 1, scope)))
            }
            2 => OracleTerm::Mul(
                Box::new(oracle_term(rng, depth - 1, scope)),
                rng.pick(&[-1, 2, 3]),
            ),
            3 => OracleTerm::Neg(Box::new(oracle_term(rng, depth - 1, scope))),
            4 => OracleTerm::Div(
                Box::new(oracle_term(rng, depth - 1, scope)),
                rng.pick(&[2, 3, -2]),
                division,
            ),
            5 => OracleTerm::Rem(
                Box::new(oracle_term(rng, depth - 1, scope)),
                rng.pick(&[2, 3, -2]),
                division,
            ),
            6 => {
                let cond = oracle_condition(rng, depth - 1, scope);
                let then_term = oracle_term(rng, depth - 1, scope);
                OracleTerm::Ite(
                    Box::new(cond),
                    Box::new(then_term),
                    Box::new(oracle_term(rng, depth - 1, scope)),
                )
            }
            _ => OracleTerm::Cast(
                Box::new(oracle_term(rng, depth - 1, scope)),
                rng.pick(&OracleIntTy::ALL),
            ),
        };
    }
    let lets = &scope.ints;
    let places = ["x", "y", "m", "result"]
        .into_iter()
        .filter(|place| !lets.iter().any(|name| name.as_str() == *place))
        .collect::<Vec<_>>();
    match rng.below(if lets.is_empty() { 3 } else { 4 }) {
        0 => OracleTerm::Place(rng.pick(&places)),
        1 => OracleTerm::Old(rng.pick(&["x", "y", "m"])),
        2 => OracleTerm::Lit(rng.pick(&[-2, -1, 0, 1, 2, 3, 7, 100])),
        _ => {
            let bound = OracleTerm::LetBound(rng.pick(lets));
            // A bound name read through an ascription of its own sort.
            if scope.quantifiers && rng.below(3) == 0 {
                OracleTerm::AscribedInt(Box::new(bound))
            } else {
                bound
            }
        }
    }
}

/// The bool parameter, bare or compared with a literal.
fn oracle_b(rng: &mut OracleRng) -> OracleClaim {
    if rng.below(2) == 0 {
        OracleClaim::B
    } else {
        OracleClaim::BCmp(rng.below(2) == 0, rng.below(2) == 0)
    }
}

/// A leaf claim over terms of at most `term_depth` operators.
fn oracle_condition(rng: &mut OracleRng, term_depth: usize, scope: &OracleScope) -> OracleClaim {
    match rng.below(4) {
        0 => OracleClaim::Lit(rng.below(2) == 0),
        1 => oracle_b(rng),
        _ => oracle_atom(rng, term_depth, scope),
    }
}

/// A comparison. Half relate a term to itself shifted by a small constant, so
/// the corpus holds claims native replay can decide as well as ones it cannot.
fn oracle_atom(rng: &mut OracleRng, term_depth: usize, scope: &OracleScope) -> OracleClaim {
    let op = rng.pick(&OracleCmp::ALL);
    let mut left = oracle_term(rng, term_depth, scope);
    // A quarter cast the related term, so casts reach verdicts too.
    if rng.below(4) == 0 {
        left = OracleTerm::Cast(Box::new(left), rng.pick(&OracleIntTy::ALL));
    }
    let right = if rng.below(2) == 0 {
        match rng.below(3) {
            0 => left.clone(),
            1 => oracle_add(left.clone(), OracleTerm::Lit(rng.pick(&[-1, 1, 2]))),
            _ => OracleTerm::Sub(
                Box::new(left.clone()),
                Box::new(OracleTerm::Lit(rng.pick(&[-1, 1]))),
            ),
        }
    } else {
        oracle_term(rng, term_depth, scope)
    };
    if rng.below(2) == 0 {
        oracle_cmp(op, left, right)
    } else {
        oracle_cmp(op, right, left)
    }
}

/// A name a `bool` quantifier in scope binds, read as a boolean.
fn oracle_bound_bool(rng: &mut OracleRng, scope: &OracleScope) -> OracleClaim {
    let name = rng.pick(&scope.bools);
    let read = match rng.below(3) {
        0 => OracleBoolRead::Bare,
        1 => OracleBoolRead::Ascribed,
        _ => OracleBoolRead::Cmp(rng.below(2) == 0, rng.below(2) == 0),
    };
    OracleClaim::BoundBool(name, read)
}

/// `forall`/`exists` over an `Int` or `bool` name, over a body of at most
/// `depth` connectives that may read it.
fn oracle_quantifier(rng: &mut OracleRng, depth: usize, scope: &mut OracleScope) -> OracleClaim {
    let exists = rng.below(2) == 0;
    let sort = if rng.below(3) == 0 {
        OracleSort::Bool
    } else {
        OracleSort::Int
    };
    let name = scope.fresh(match sort {
        OracleSort::Int => 'q',
        OracleSort::Bool => 'p',
    });
    match sort {
        OracleSort::Int => scope.ints.push(name.clone()),
        OracleSort::Bool => scope.bools.push(name.clone()),
    }
    let body = oracle_claim(rng, depth, scope);
    match sort {
        OracleSort::Int => scope.ints.pop(),
        OracleSort::Bool => scope.bools.pop(),
    };
    OracleClaim::Quant(exists, name, sort, Box::new(body))
}

fn oracle_claim(rng: &mut OracleRng, depth: usize, scope: &mut OracleScope) -> OracleClaim {
    let choice = match (depth, scope.quantifiers) {
        (0, _) => rng.below(4),
        (_, false) => rng.below(10),
        (_, true) => rng.below(12),
    };
    match choice {
        0 => OracleClaim::Lit(rng.below(2) == 0),
        1 if !scope.bools.is_empty() && rng.below(2) == 0 => oracle_bound_bool(rng, scope),
        1 => oracle_b(rng),
        2 | 3 => oracle_atom(rng, 1, scope),
        4 | 5 => oracle_not(oracle_claim(rng, depth - 1, scope)),
        6 => oracle_and(
            oracle_claim(rng, depth - 1, scope),
            oracle_claim(rng, depth - 1, scope),
        ),
        7 => OracleClaim::Or(
            Box::new(oracle_claim(rng, depth - 1, scope)),
            Box::new(oracle_claim(rng, depth - 1, scope)),
        ),
        8 => OracleClaim::Implies(
            Box::new(oracle_claim(rng, depth - 1, scope)),
            Box::new(oracle_claim(rng, depth - 1, scope)),
        ),
        9 => {
            // A quarter of the lets rebind `result`, the spelling of a place.
            let name = if rng.below(4) == 0 && !scope.ints.iter().any(|name| name == "result") {
                "result".to_string()
            } else {
                scope.fresh('t')
            };
            // Half the lets over a quantifier corpus write `: Int`.
            let typed = scope.quantifiers && rng.below(2) == 0;
            let value = oracle_term(rng, 1, scope);
            scope.ints.push(name.clone());
            let body = oracle_claim(rng, depth - 1, scope);
            scope.ints.pop();
            OracleClaim::Let(name, value, Box::new(body), typed)
        }
        _ => oracle_quantifier(rng, depth - 1, scope),
    }
}

/// A generated corpus: every claim, and every claim with one subformula
/// negated, in both claim formats where the format spells it, bound and
/// unbound, rotating through the kinds trust-wp owns and the modes the bundle
/// path supports; plus, from each root claim, one ill-formed binding per
/// binding rule it can break. A second set of roots is quantified: `forall`
/// and `exists` over `Int` and `bool` names, read bare, through an
/// ascription of their own sort and through `let`s written `: Int`. From
/// every root the corpus also derives a disjunct reading a bound name at a
/// sort its binder does not give it, one quantifying over a type parameter
/// or a sequence, and a claim whose truth turns on whether a reference's
/// referent type is inhabited. From every pure-expr root it derives three
/// dereference shapes: a disjunct dereferencing a value at a sort it has no
/// reading at, one annotating a dereference, and `(C && X) || (!C && !X)`
/// for a well-sorted dereference claim `X` of known truth.
#[test]
fn test_trust_ir_native_soundness_oracle_generated_corpus() {
    const CLAIMS: usize = 120;
    const QUANTIFIED_CLAIMS: usize = 60;
    let kinds = [
        ObligationKind::Postcondition,
        ObligationKind::Precondition,
        ObligationKind::LoopInvariant,
    ];
    let mut rng = OracleRng(0x7472_7573_742d_7770);
    let mut quantified_rng = OracleRng(0x7175_616e_7469_6669);
    let roots = (0..CLAIMS)
        .map(|_| oracle_claim(&mut rng, 3, &mut OracleScope::default()))
        .chain((0..QUANTIFIED_CLAIMS).map(|_| {
            oracle_quantifier(&mut quantified_rng, 2, &mut OracleScope::with_quantifiers())
        }))
        .collect::<Vec<_>>();
    let mut report = OracleReport::default();
    for (index, root) in roots.into_iter().enumerate() {
        let mut claims = vec![root.clone()];
        claims.extend(root.negation_mutants().into_iter().skip(1));
        for (variant, claim) in claims.into_iter().enumerate() {
            for format in [OracleFormat::TrustFormula, OracleFormat::PureExpr] {
                let rotation = index + variant;
                let bound = rotation % 4 != 3;
                let kind = kinds[rotation % kinds.len()].clone();
                let mode = ORACLE_MODES[(rotation / kinds.len()) % ORACLE_MODES.len()];
                let label = format!("#{index}.{variant} {format:?} {mode:?} {claim:?}");
                let Some(case) = OracleCase::new(label, claim.clone(), format, bound, kind, mode)
                else {
                    continue;
                };
                report.check_pair(&case);
                if variant == 0 {
                    for ill_formed in case.ill_formed_variants(index) {
                        report.check_pair(&ill_formed);
                    }
                    for bool_read in case.bool_name_variants(index) {
                        report.check_pair(&bool_read);
                    }
                    if let Some(unmodeled) = case.unmodeled_variant(index) {
                        report.check_pair(&unmodeled);
                    }
                    if let Some(ill_sorted) = case.ill_sorted_variant(index) {
                        report.check_pair(&ill_sorted);
                    }
                    if let Some(ill_sorted) = case.ill_sorted_let_variant() {
                        report.check_pair(&ill_sorted);
                    }
                    if let Some(ill_sorted) = case.bound_ill_sorted_variant(index) {
                        report.check_pair(&ill_sorted);
                    }
                    report.check_pair(&case.unmodeled_binder_variant(index));
                    report.check_pair(&case.empty_domain_variant(index));
                    for dereference in [
                        case.deref_ill_sorted_variant(index),
                        case.deref_unmodeled_variant(index),
                        case.deref_modeled_variant(index),
                    ]
                    .into_iter()
                    .flatten()
                    {
                        report.check_pair(&dereference);
                    }
                }
            }
        }
    }
    report.assert_sound();
    report.assert_not_vacuous();
    eprintln!(
        "soundness oracle: {} claims ({} with an ill-formed binding, {} writing an unmodeled construct, {} with no one reading, {} turning on an inhabited sort ({} refused naming it)), {} verified ({} quantified, {} with an exists, {} reading a dereference, {} pure-expr, {} strongest-postcondition, {} with mul/div/mod/neg/ite/cast, {} with a cast, {} pure-expr binding `b`); ill-formed bindings refused by rule: {:?}; refusals by what they name: {:?}",
        report.claims,
        report.ill_formed_claims,
        report.unmodeled_claims,
        report.ill_sorted_claims,
        report.witness_claims,
        report.refused_witness,
        report.verified,
        report.verified_quantified,
        report.verified_exists,
        report.verified_dereference,
        report.verified_pure_expr,
        report.verified_strongest_postcondition,
        report.verified_extended,
        report.verified_cast,
        report.verified_bound_bool_name,
        report.refused,
        report.refused_unmodeled
    );
}
