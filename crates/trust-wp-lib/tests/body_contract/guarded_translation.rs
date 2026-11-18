//! A real shared question supplies the bytes used by the guarded Lean packet.
//! This synthetic canonical-IR fixture carries no compiler/source authority.

use trust_ir_contract::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION;
use trust_wp_lib::trust_ir_body::NativeBodyWpTranslationCoverage;

use super::*;

fn select_question() -> (api::TrustContractBundle, NativeVerificationBundle) {
    let mut post = ProofFormula::new(
        TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [{"name":"r", "sort":"int"}, {"name":"x", "sort":"int"}],
            "body": {"op":"eq", "lhs":{"var":"r"}, "rhs":{"var":"x"}}
        })
        .to_string(),
    );
    post.bindings = vec![
        binding("r", 0, true, ClauseSort::BitVec(64)),
        binding("x", 1, false, ClauseSort::BitVec(64)),
    ];
    // Construct a complete scalar module. The separate legacy fixture's
    // physical-layout metadata remains intact and outside this theorem.
    let mut module = Module::new("guarded-select-return");
    let file = module.intern_file("guarded-select-return.ir").unwrap();
    let signature = module
        .add_func_type(FuncTy::unrecorded(
            vec![Ty::Bool, Ty::U64, Ty::U64],
            vec![Ty::U64],
            false,
        ))
        .unwrap();
    let mut block = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), Ty::Bool)
        .with_param(ValueId::new(1), Ty::U64)
        .with_param(ValueId::new(2), Ty::U64);
    block.body = vec![
        InstrNode::new(Inst::Select {
            ty: Ty::U64,
            cond: ValueId::new(0),
            then_val: ValueId::new(1),
            else_val: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }),
    ];
    let mut function = Function::new(
        FuncId::new(0),
        "demo::guarded_select",
        signature,
        BlockId::new(0),
    );
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "returns its first integer under c",
        )
        .with_function(FuncId::new(0))
        .with_formula(post)
        .with_source(
            ProofObligationSourceIdentity::new("post", "trust-assertion:post").with_public(
                PublicObligationIdentity {
                    obligation_id: "obligation:post".into(),
                    semantic_digest: digest(1),
                },
            ),
        ),
    );
    let module_digest = module.stable_digest();
    let mut node = ProofLineageNode::new(
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
    node.obligations.push(ProofId::new(0));
    let mut native = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::TrustIrModule,
        module_digest,
        module,
        ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![node],
            roots: vec![ProofLineageId::new(0)],
        },
    );
    native
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: "obligation:post".into(),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan {
                file,
                line: 1,
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: vec![],
        });
    native
        .requests
        .push(NativeVerificationRequest::TrustWp(trust_wp_request(
            TrustWpVerificationMode::WeakestPrecondition,
        )));
    let mut entry = ProofFormula::new("trust-wp.pure-expr.v1", "c");
    entry.bindings = vec![binding("c", 0, false, ClauseSort::Bool)];
    let public = bind_public(&mut native, entry);
    (public, native)
}

fn execute(native: &NativeVerificationBundle, c: bool, a: u64, b: u64) -> Vec<InterpretValue> {
    Interpreter::with_module(&native.module)
        .execute_func(
            FuncId::new(0),
            [
                InterpretValue::bool(c),
                InterpretValue::int(Ty::U64, i128::from(a)).unwrap(),
                InterpretValue::int(Ty::U64, i128::from(b)).unwrap(),
            ],
        )
        .unwrap()
        .returns
}

#[test]
fn actual_guarded_select_packet_retains_entry_catalog_full_width_and_same_derived_vc() {
    let (public, native) = select_question();
    let input = serde_json::to_vec(&native).unwrap();
    let module_bytes = trust_ir::binary::serialize_module(&native.module).unwrap();
    let proof = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    let entries: Vec<_> = question.entry_preconditions(question.function()).collect();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].proof().id, ProofId::new(1));
    assert_eq!(
        entries[0].public_obligation().obligation_id,
        "obligation:entry"
    );
    let entry = proof.witness().public_question.as_ref().unwrap();
    assert_eq!(entry.digest, question.digest_sha256());
    assert!(entry.uses_declared_entry);
    assert_eq!(
        entry.contracts,
        vec![(
            question.function(),
            entries[0].proof().id,
            entries[0].proof().formula.clone().unwrap()
        )]
    );
    assert_eq!(
        proof.witness().contracts,
        vec![(
            question.proof_id(),
            question.proof().formula.clone().unwrap()
        )]
    );
    assert!(matches!(
        proof.witness().coverage,
        NativeBodyWpTranslationCoverage::Untranslated { .. }
    ));
    assert_eq!(
        proof.witness().parameters,
        vec![
            (ValueId::new(0), "__trust_wp_body_v0".into()),
            (ValueId::new(1), "__trust_wp_body_v1".into()),
            (ValueId::new(2), "__trust_wp_body_v2".into()),
        ]
    );
    assert_eq!(proof.witness().derived_request.obligations.len(), 1);
    assert_eq!(
        execute(&native, true, u64::MAX, 0),
        vec![InterpretValue::int(Ty::U64, i128::from(u64::MAX)).unwrap()]
    );
    // This excluded execution really falsifies the bare postcondition r=x.
    assert_eq!(
        execute(&native, false, 0, u64::MAX),
        vec![InterpretValue::int(Ty::U64, i128::from(u64::MAX)).unwrap()]
    );
    let unconditional = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert_eq!(
        verify_native_public_question(&unconditional, wp_request_id(&native))
            .unwrap()
            .result()
            .status,
        VerifyBundleStatus::Failed
    );
    assert_eq!(input, serde_json::to_vec(&native).unwrap());
    assert_eq!(
        module_bytes,
        trust_ir::binary::serialize_module(&native.module).unwrap()
    );
    if let Some(path) = std::env::var_os("TRUST_WP_GUARDED_PACKET_OUTPUT") {
        use std::io::Write;
        let mut wrong_return = native.module.clone();
        wrong_return.functions[0].blocks[0].body[1] = InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        });
        let mut swapped = native.module.clone();
        let Inst::Select {
            then_val, else_val, ..
        } = &mut swapped.functions[0].blocks[0].body[0].inst
        else {
            unreachable!()
        };
        std::mem::swap(then_val, else_val);
        let packet = serde_json::json!({
            "scope": "synthetic canonical IR question; no source, ABI or proof-grade authority",
            "public": public, "native": native, "original_module_bytes": module_bytes,
            "wrong_return_module_bytes": trust_ir::binary::serialize_module(&wrong_return).unwrap(),
            "swapped_module_bytes": trust_ir::binary::serialize_module(&swapped).unwrap(),
            "question_digest": question.digest_sha256(), "function": question.function(),
            "post_proof": question.proof_id(), "entry_proof": entries[0].proof().id,
            "entry_public_obligation": entries[0].public_obligation().obligation_id,
            "entry_formula": entries[0].proof().formula,
            "post_formula": question.proof().formula,
            "witness": proof.witness(), "result": proof.result(),
        });
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap();
        file.write_all(&serde_json::to_vec_pretty(&packet).unwrap())
            .unwrap();
    }
}

#[test]
fn changed_original_entry_proof_param_return_or_binding_cannot_replay_the_guarded_packet() {
    let (public, native) = select_question();
    let original = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    for mutation in 0..7 {
        let mut public = public.clone();
        let mut changed = native.clone();
        match mutation {
            0 => {
                let formula = changed.module.proof_obligations[1]
                    .formula
                    .as_mut()
                    .unwrap();
                formula.payload = "true".into();
                formula.bindings.clear();
                public.contracts[1].predicate = api::ContractPredicate::CanonicalJson {
                    schema: formula.schema.clone(),
                    value: formula.payload.clone().into(),
                };
                public.contracts[1].metadata[0].value = "[]".into();
            }
            1 => {
                let id = ProofId::new(42);
                changed.module.proof_obligations[1].id = id;
                changed.compiler_facts.obligation_sources[1].obligation = id;
                for node in &mut changed.lineage.nodes {
                    for proof in &mut node.obligations {
                        if *proof == ProofId::new(1) {
                            *proof = id;
                        }
                    }
                }
            }
            2 => {
                let formula = changed.module.proof_obligations[1]
                    .formula
                    .as_mut()
                    .unwrap();
                formula.bindings[0].1.place = ClausePlace::Param { index: 1 };
                public.contracts[1].metadata[0].value =
                    serde_json::to_string(&formula.bindings).unwrap();
            }
            3 => {
                changed.module.functions[0].blocks[0].body[1] = InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                })
            }
            4 => {
                let formula = changed.module.proof_obligations[0]
                    .formula
                    .as_mut()
                    .unwrap();
                formula.bindings[1].1.place = ClausePlace::Param { index: 2 };
                public.contracts[0].metadata[0].value =
                    serde_json::to_string(&formula.bindings).unwrap();
            }
            5 => {
                let Inst::Select {
                    then_val, else_val, ..
                } = &mut changed.module.functions[0].blocks[0].body[0].inst
                else {
                    unreachable!()
                };
                std::mem::swap(then_val, else_val);
            }
            _ => {
                let formula = changed.module.proof_obligations[0]
                    .formula
                    .as_mut()
                    .unwrap();
                formula.bindings[0].1.place = ClausePlace::Param { index: 1 };
                public.contracts[0].metadata[0].value =
                    serde_json::to_string(&formula.bindings).unwrap();
            }
        }
        refresh(&public, &mut changed);
        let admitted = trust_ir::ValidatedNativeBundle::new(&changed).unwrap();
        let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
        assert_ne!(
            question.digest_sha256(),
            original.public_question_digest().unwrap()
        );
        // Supply the new digest deliberately: independently rederived data,
        // rather than only the outer digest check, must reject the old proof.
        assert!(
            replay_native_public_question(
                &question,
                wp_request_id(&changed),
                original.result(),
                Some(original.witness()),
                question.digest_sha256()
            )
            .is_err(),
            "mutation {mutation}"
        );
        let regenerated = verify_native_public_question(&question, wp_request_id(&changed));
        if mutation == 2 {
            let error = regenerated.unwrap_err().to_string();
            assert!(
                error.contains("binding") || error.contains("type") || error.contains("sort"),
                "{error}"
            );
        } else {
            assert_eq!(
                regenerated.unwrap().result().status,
                if matches!(mutation, 1 | 6) {
                    VerifyBundleStatus::Verified
                } else {
                    VerifyBundleStatus::Failed
                },
                "mutation {mutation}"
            );
        }
    }
}

#[test]
fn changing_the_emitted_vc_or_declared_entry_witness_is_rejected_independently() {
    let (public, native) = select_question();
    let original = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    for mutation in 0..3 {
        let mut witness = original.witness().clone();
        match mutation {
            0 => witness.derived_request.obligations[0].claim.payload = "true".into(),
            1 => witness.public_question.as_mut().unwrap().contracts[0].1 = ProofId::new(42),
            _ => {
                witness.public_question.as_mut().unwrap().contracts[0]
                    .2
                    .bindings[0]
                    .1
                    .place = ClausePlace::Param { index: 1 }
            }
        }
        assert!(
            replay_native_public_question(
                &question,
                wp_request_id(&native),
                original.result(),
                Some(&witness),
                question.digest_sha256()
            )
            .is_err(),
            "mutation {mutation}"
        );
    }
}
