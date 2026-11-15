//! The compiler capture is immutable. Only a separate test contract is appended.
//! Its derived binary image is retained separately from the original JSON.
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts, trust_ir_native_bundle_to_body_verify_requests,
    verify_trust_ir_body_contracts,
};

use super::*;

const ORIGINAL: &str = include_str!("fixtures/compiler_memory/original-native.json");
const DERIVED: &[u8] = include_bytes!("fixtures/compiler_memory/derived-original.tirb");
const POST: &str =
    "((c : bool) && ((r : bool) == (l : bool))) || (!(c : bool) && ((r : bool) == (q : bool)))";

#[derive(Clone, Copy)]
enum Change {
    Original,
    WrongStore,
    WrongCondition,
    Uninitialized,
}

fn captured(change: Change) -> Module {
    let capture: NativeVerificationBundle = serde_json::from_str(ORIGINAL).unwrap();
    assert_eq!(
        capture.module.stable_digest(),
        capture.trust_ir_module_digest
    );
    assert_eq!(
        trust_ir::binary::serialize_module(&capture.module).unwrap(),
        DERIVED
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(DERIVED).unwrap(),
        capture.module
    );
    let mut module = capture.module;
    match change {
        Change::Original => {}
        Change::WrongStore => match &mut module.functions[0].blocks[1].body[1].inst {
            Inst::Store { value, .. } => *value = ValueId::new(2),
            _ => panic!("original store shape"),
        },
        Change::WrongCondition => match &mut module.functions[0].blocks[0].body[2].inst {
            Inst::ICmp { op, .. } => *op = trust_ir::ICmpOp::Ne,
            _ => panic!("original equality shape"),
        },
        Change::Uninitialized => {
            module.functions[0].blocks[1].body[1] = InstrNode::new(Inst::Copy {
                ty: Ty::Bool,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(10));
        }
    }
    module
}

fn attached(change: Change, contract: &str) -> NativeVerificationBundle {
    let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", contract);
    formula.bindings = [
        ("c", ClausePlace::Param { index: 0 }),
        ("l", ClausePlace::Param { index: 1 }),
        ("q", ClausePlace::Param { index: 2 }),
        ("r", ClausePlace::ResultSlot { index: 0 }),
    ]
    .into_iter()
    .map(|(name, place)| {
        (
            name.into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place,
            },
        )
    })
    .collect();
    let mut bundle = native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::Bool; 3],
        vec![Ty::Bool],
    );
    let mut post = bundle.module.proof_obligations.pop().unwrap();
    post.id = ProofId::new(1);
    post.description = "separately attached compiler-memory test postcondition".into();
    let formula = post.formula.as_ref().unwrap();
    post.source = Some(
        ProofObligationSourceIdentity::new("test:compiler-memory-post", "test:assertion:1")
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:trust-wp:postcondition:1".into(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-wp.native-test.public-obligation.v1",
                    format!("{}\0{}", formula.schema, formula.payload).as_bytes(),
                ),
            }),
    );
    let original: NativeVerificationBundle = serde_json::from_str(ORIGINAL).unwrap();
    bundle.module = captured(change);
    let original_bytes = trust_ir::binary::serialize_module(&bundle.module).unwrap();
    let original_digest = bundle.module.stable_digest();
    bundle.module.proof_obligations.push(post);
    bundle.producer = original.producer;
    bundle.input = original.input;
    bundle.provenance = original.provenance;
    bundle.compiler_facts = original.compiler_facts;
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(1),
            public_obligation_id: "vc:trust-wp:postcondition:1".into(),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan {
                file: 0,
                line: 1,
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(1)),
            cause: NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: vec![],
        });
    bundle.lineage = original.lineage;
    let mut attached = ProofLineageNode::new(
        ProofLineageId::new(1),
        ProofTransform::new(
            ProofTransformStage::SolverAdapter,
            "attach-test-postcondition",
            "captured-compiler-memory",
            "1",
        ),
        original.trust_ir_module_digest,
        bundle.module.stable_digest(),
    );
    attached.obligations = vec![ProofId::new(1)];
    attached.depends_on.clone_from(&bundle.lineage.roots);
    bundle.lineage.nodes.push(attached);
    bundle.lineage.roots = vec![ProofLineageId::new(1)];
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] else {
        panic!("WP request")
    };
    request.obligations = vec![ProofId::new(1)];
    request.lineage_roots = vec![ProofLineageId::new(1)];
    request.provenance.replay = Some(
        ProofReplayIdentity::new("trust-wp", "compiler-memory test contract")
            .with_transcript_digest(original_digest),
    );
    refresh_native_bundle_module_identity(&mut bundle);
    let mut stripped = bundle.module.clone();
    assert_eq!(
        stripped.proof_obligations.pop().unwrap().id,
        ProofId::new(1)
    );
    assert_eq!(
        trust_ir::binary::serialize_module(&stripped).unwrap(),
        original_bytes
    );
    bundle
}

fn verify(bundle: &NativeVerificationBundle, valid: bool) -> Vec<trust_wp_lib::VerifyBundleResult> {
    let requests = trust_ir_native_bundle_to_body_verify_requests(bundle).unwrap();
    let direct: Vec<_> = requests
        .iter()
        .cloned()
        .map(trust_wp_lib::verify_bundle)
        .collect();
    let results = verify_trust_ir_body_contracts(bundle).unwrap();
    assert_eq!(
        serde_json::to_value(&results).unwrap(),
        serde_json::to_value(direct).unwrap()
    );
    assert_eq!(
        results[0].status,
        if valid {
            VerifyBundleStatus::Verified
        } else {
            VerifyBundleStatus::Failed
        },
        "{results:#?}"
    );
    assert_eq!(
        replay_trust_ir_body_contracts(bundle, &results).is_ok(),
        valid
    );
    if valid {
        let value = serde_json::to_value(&results).unwrap();
        assert_eq!(
            value[0]["obligation_results"][0]["status"]["verified"]["evidence"]["strength"],
            "sound"
        );
    }
    assert!(bundle
        .module
        .proof_obligations
        .iter()
        .all(|obligation| obligation.status == ProofStatus::Pending));
    if let Some(dir) = std::env::var_os("TRUST_WP_MEMORY_EVIDENCE_DIR") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        let value = serde_json::json!({"original_capture": ORIGINAL, "derived_original_bytes": DERIVED,
            "bundle": bundle, "requests": requests, "results": results});
        std::fs::write(
            dir.join(format!(
                "{}.json",
                hex_digest(&bundle.module.stable_digest().bytes)
            )),
            serde_json::to_vec_pretty(&value).unwrap(),
        )
        .unwrap();
    }
    results
}

#[test]
fn compiler_memory_contract_verifies_without_upgrading_proof_grade() {
    verify(&attached(Change::Original, POST), true);
    verify(&attached(Change::Original, &format!("!({POST})")), false);
    verify(&attached(Change::WrongStore, POST), false);
    // Boolean inequality is interpreted now, so the changed branch is a
    // well-formed body whose original postcondition must explicitly fail.
    verify(&attached(Change::WrongCondition, POST), false);
    assert!(verify_trust_ir_body_contracts(&attached(Change::Uninitialized, POST)).is_err());
}

#[test]
fn compiler_memory_agrees_with_all_boolean_inputs() {
    for c in [false, true] {
        for l in [false, true] {
            for q in [false, true] {
                let want = if c { l } else { q };
                let output =
                    trust_ir::interpret::Interpreter::with_module(&captured(Change::Original))
                        .execute_func(
                            FuncId::new(0),
                            [c, l, q].map(trust_ir::interpret::InterpretValue::bool),
                        )
                        .unwrap();
                assert_eq!(
                    output.returns,
                    vec![trust_ir::interpret::InterpretValue::bool(want)]
                );
                let antecedent =
                    format!("((c : bool) == {c}) && ((l : bool) == {l}) && ((q : bool) == {q})");
                verify(
                    &attached(
                        Change::Original,
                        &format!("!({antecedent}) || ((r : bool) == {want})"),
                    ),
                    true,
                );
                verify(
                    &attached(
                        Change::Original,
                        &format!("!({antecedent}) || ((r : bool) != {want})"),
                    ),
                    false,
                );
            }
        }
    }
}

#[test]
fn unused_uninitialized_load_is_not_erased_by_a_true_postcondition() {
    let mut bundle = attached(Change::Original, "true");
    bundle.module.proof_obligations[1]
        .formula
        .as_mut()
        .unwrap()
        .bindings
        .clear();
    bundle.module.functions[0].blocks[1].body.insert(
        0,
        InstrNode::new(Inst::Load {
            ty: Ty::Bool,
            ptr: ValueId::new(4),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(99)),
    );
    refresh_native_bundle_module_identity(&mut bundle);
    let error = trust_ir_native_bundle_to_body_verify_requests(&bundle)
        .unwrap_err()
        .to_string();
    assert!(error.contains("uninitialized"), "{error}");
}

#[test]
fn aliases_escapes_layouts_and_non_dominating_uses_are_refused() {
    for mutation in 0..7 {
        let mut bundle = attached(Change::Original, POST);
        let function = &mut bundle.module.functions[0];
        match mutation {
            0 => function.blocks[0].body.insert(
                1,
                InstrNode::new(Inst::Copy {
                    ty: Ty::Ptr,
                    operand: ValueId::new(4),
                })
                .with_result(ValueId::new(20)),
            ),
            1 => {
                function.blocks[3].body[1].inst = Inst::Return {
                    values: vec![ValueId::new(4)],
                }
            }
            2 => {
                if let Inst::Store { volatile, .. } = &mut function.blocks[1].body[1].inst {
                    *volatile = true;
                }
            }
            3 => {
                if let Inst::Load { ty, .. } = &mut function.blocks[3].body[0].inst {
                    *ty = Ty::I32;
                }
            }
            4 => {
                if let Inst::Copy { operand, .. } = &mut function.blocks[1].body[0].inst {
                    *operand = ValueId::new(8);
                }
            }
            5 => bundle.module.target_info.as_mut().unwrap().endianness = Endianness::Big,
            6 => bundle.module.target_info.as_mut().unwrap().pointer_size = 4,
            _ => unreachable!(),
        }
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(
            verify_trust_ir_body_contracts(&bundle).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn fresh_cells_remain_distinct_across_stores() {
    let mut bundle = attached(Change::Original, POST);
    let function = &mut bundle.module.functions[0];
    function.blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Alloca {
            ty: Ty::Bool,
            count: None,
            align: None,
        })
        .with_result(ValueId::new(16)),
    );
    function.blocks[3].body.insert(
        0,
        InstrNode::new(Inst::Store {
            ty: Ty::Bool,
            ptr: ValueId::new(16),
            value: ValueId::new(5),
            volatile: false,
            align: None,
        }),
    );
    function.blocks[3].body.insert(
        1,
        InstrNode::new(Inst::Load {
            ty: Ty::Bool,
            ptr: ValueId::new(16),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(17)),
    );
    refresh_native_bundle_module_identity(&mut bundle);
    verify(&bundle, true);
    for c in [false, true] {
        for l in [false, true] {
            for q in [false, true] {
                let output = trust_ir::interpret::Interpreter::with_module(&bundle.module)
                    .execute_func(
                        FuncId::new(0),
                        [c, l, q].map(trust_ir::interpret::InterpretValue::bool),
                    )
                    .unwrap();
                assert_eq!(
                    output.returns,
                    vec![trust_ir::interpret::InterpretValue::bool(if c {
                        l
                    } else {
                        q
                    })]
                );
            }
        }
    }
    if let Inst::Store { ptr, .. } = &mut bundle.module.functions[0].blocks[3].body[0].inst {
        *ptr = ValueId::new(4);
    }
    refresh_native_bundle_module_identity(&mut bundle);
    assert!(trust_ir_native_bundle_to_body_verify_requests(&bundle).is_err());
}

#[test]
fn global_memory_state_is_outside_the_fresh_local_fragment() {
    let mut bundle = attached(Change::Original, POST);
    bundle.module.globals.push(trust_ir::Global {
        name: "outside".into(),
        ty: Ty::Bool,
        mutable: false,
        initializer: Some(Constant::Bool(false)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    refresh_native_bundle_module_identity(&mut bundle);
    assert_eq!(trust_ir_build::validate_module(&bundle.module), []);
    let error = trust_ir_native_bundle_to_body_verify_requests(&bundle)
        .unwrap_err()
        .to_string();
    assert!(error.contains("global or imported"), "{error}");
}

#[test]
fn memory_certificate_cannot_transfer_to_a_different_body_or_request() {
    let bundle = attached(Change::Original, POST);
    let proof = verify(&bundle, true);
    for change in [
        Change::WrongStore,
        Change::WrongCondition,
        Change::Uninitialized,
    ] {
        assert!(replay_trust_ir_body_contracts(&attached(change, POST), &proof).is_err());
    }
    assert!(replay_trust_ir_body_contracts(
        &attached(Change::Original, &format!("!({POST})")),
        &proof
    )
    .is_err());
    let mut changed = bundle.clone();
    changed.module.proof_obligations[0]
        .description
        .push_str(" changed");
    refresh_native_bundle_module_identity(&mut changed);
    assert!(replay_trust_ir_body_contracts(&changed, &proof).is_err());
    let mut requests = trust_ir_native_bundle_to_body_verify_requests(&bundle).unwrap();
    requests[0].obligations[0].claim.payload.push(' ');
    assert!(replay_verify_bundle_result_evidence(&requests[0], &proof[0]).is_err());
    let mut changed = proof.clone();
    if let BundleObligationStatus::Verified { evidence } =
        &mut changed[0].obligation_results[0].status
    {
        evidence.artifacts[0] = evidence.artifacts[0].clone().with_utf8_bytes("forged");
    }
    assert!(replay_trust_ir_body_contracts(&bundle, &changed).is_err());
}
