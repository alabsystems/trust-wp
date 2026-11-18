//! Original entry domains constrain proofs without erasing execution obligations.
use api::native_public_question::{NativePublicProofScope, NativePublicQuestion};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_verifier_api as api;
use trust_wp_lib::trust_ir_body::{replay_native_public_question, verify_native_public_question};

use super::*;

#[path = "guarded_translation.rs"]
mod guarded_translation;

fn wp_request_id(native: &NativeVerificationBundle) -> NativeRequestId {
    let requests: Vec<_> = native
        .requests
        .iter()
        .filter_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .collect();
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].function, FuncId::new(0));
    assert_eq!(requests[0].obligations, [ProofId::new(0)]);
    requests[0].id
}

fn binding(name: &str, index: u32, result: bool, sort: ClauseSort) -> (String, ClauseBinding) {
    (
        name.into(),
        ClauseBinding {
            sort,
            place: if result {
                ClausePlace::ResultSlot { index }
            } else {
                ClausePlace::Param { index }
            },
        },
    )
}

fn public_clause(
    public: &mut api::TrustContractBundle,
    id: &str,
    kind: api::ContractKind,
    formula: &ProofFormula,
) {
    let path = match &public.subject {
        api::BundleSubject::Function { path, .. } => path.clone(),
        _ => unreachable!(),
    };
    public.contracts.push(api::TrustContract {
        contract_id: id.into(),
        kind,
        predicate: api::ContractPredicate::CanonicalJson {
            schema: formula.schema.clone(),
            value: formula.payload.clone().into(),
        },
        source: api::SourceLocation::default(),
        metadata: vec![api::MetadataEntry {
            key: api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
            value: serde_json::to_string(&formula.bindings).unwrap(),
        }],
    });
    let context = api::ObligationContext::new(
        api::ObligationProducer::Compatibility,
        api::ObligationOrigin::Contract {
            contract_id: id.into(),
            contract_kind: kind,
            contract_index: public.contracts.len() - 1,
            predicate_schema: Some(formula.schema.clone()),
        },
    )
    .with_function(api::FunctionContext {
        crate_name: "demo".into(),
        path,
    });
    public.obligations.push(api::TrustObligation {
        obligation_id: format!("obligation:{id}"),
        kind: if kind == api::ContractKind::Ensures {
            api::ObligationKind::Postcondition
        } else {
            api::ObligationKind::Precondition
        },
        contract_id: Some(id.into()),
        proof_item_id: None,
        source: api::SourceLocation::default(),
        description: format!("original {id}"),
        required_strength: None,
        summary_facts: vec![],
        metadata: vec![context.to_metadata_entry().unwrap()],
    });
}

fn bind_public(
    native: &mut NativeVerificationBundle,
    entry: ProofFormula,
) -> api::TrustContractBundle {
    let mut public = api::TrustContractBundle::empty(
        "entry-body",
        api::BundleSubject::Function {
            crate_name: "demo".into(),
            path: native.module.functions[0].name.clone(),
        },
    );
    let post = native.module.proof_obligations[0].formula.as_ref().unwrap();
    public_clause(&mut public, "post", api::ContractKind::Ensures, post);
    public_clause(&mut public, "entry", api::ContractKind::Requires, &entry);
    let mut pre = native.module.proof_obligations[0].clone();
    pre.id = ProofId::new(1);
    pre.kind = ObligationKind::Precondition;
    pre.formula = Some(entry);
    native.module.proof_obligations.push(pre);
    let mut source = native.compiler_facts.obligation_sources[0].clone();
    source.obligation = ProofId::new(1);
    source.public_obligation_id = "obligation:entry".into();
    source.assertion_id = Some(NativeAssertionId::new(1));
    source.cause = NativeObligationCause::Precondition;
    native.compiler_facts.obligation_sources.push(source);
    native.lineage.nodes[0].obligations.push(ProofId::new(1));
    for (index, id) in ["post", "entry"].into_iter().enumerate() {
        let source = native.module.proof_obligations[index]
            .source
            .as_mut()
            .unwrap();
        source.source_id = id.into();
        source.assertion_id = format!("trust-assertion:{id}");
        source.range = None;
        native.compiler_facts.obligation_sources[index].public_obligation_id =
            format!("obligation:{id}");
    }
    refresh(&public, native);
    public
}

fn refresh(public: &api::TrustContractBundle, native: &mut NativeVerificationBundle) {
    for proof in &mut native.module.proof_obligations {
        let source = proof.source.as_mut().unwrap();
        let original = public
            .obligations
            .iter()
            .find(|obligation| obligation.contract_id.as_deref() == Some(source.source_id.as_str()))
            .unwrap();
        let digest = public
            .canonical_obligation_semantic_digest_sha256(original)
            .unwrap();
        source.public = Some(PublicObligationIdentity {
            obligation_id: original.obligation_id.clone(),
            semantic_digest: ProofDigest::sha256(std::array::from_fn(|i| {
                u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
            })),
        });
    }
    refresh_native_bundle_module_identity(native);
}

fn clear_unexecuted_cast_facts(native: &mut NativeVerificationBundle) {
    native.compiler_facts.casts.clear();
    for source in &mut native.compiler_facts.obligation_sources {
        source
            .facts
            .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));
    }
}

fn max_question() -> (api::TrustContractBundle, NativeVerificationBundle) {
    let mut post = ProofFormula::new("trust-wp.pure-expr.v1", "r <= a");
    post.bindings = vec![
        binding("r", 0, true, ClauseSort::BitVec(64)),
        binding("a", 0, false, ClauseSort::BitVec(64)),
    ];
    let mut native = native_bundle_with_signature(
        post,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::U64, Ty::U64],
        vec![Ty::U64],
    );
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), Ty::U64)
        .with_param(ValueId::new(1), Ty::U64);
    entry.body = vec![
        InstrNode::new(Inst::ICmp {
            op: trust_ir::ICmpOp::Uge,
            ty: Ty::U64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Select {
            ty: Ty::U64,
            cond: ValueId::new(2),
            then_val: ValueId::new(0),
            else_val: ValueId::new(1),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }),
    ];
    native.module.functions[0].blocks = vec![entry];
    clear_unexecuted_cast_facts(&mut native);
    let mut pre = ProofFormula::new("trust-wp.pure-expr.v1", "b <= a");
    pre.bindings = vec![
        binding("a", 0, false, ClauseSort::BitVec(64)),
        binding("b", 1, false, ClauseSort::BitVec(64)),
    ];
    let public = bind_public(&mut native, pre);
    (public, native)
}

fn prove(
    public: &api::TrustContractBundle,
    native: &NativeVerificationBundle,
    scope: NativePublicProofScope,
) -> trust_wp_lib::trust_ir_body::NativeBodyWpVerification {
    let admitted = trust_ir::ValidatedNativeBundle::new(native).unwrap();
    let question =
        NativePublicQuestion::for_derivation(public, &admitted, "obligation:post", scope).unwrap();
    let verified = verify_native_public_question(&question, wp_request_id(&native)).unwrap();
    assert_eq!(
        verified.public_question_digest(),
        Some(question.digest_sha256())
    );
    assert_eq!(
        verified.result().status,
        VerifyBundleStatus::Verified,
        "{verified:#?}"
    );
    replay_native_public_question(
        &question,
        wp_request_id(&native),
        verified.result(),
        Some(verified.witness()),
        verified.public_question_digest().unwrap(),
    )
    .unwrap();
    verified
}

#[test]
fn original_max_contract_proves_under_requires_while_excluded_inputs_are_real_bare_counterexamples()
{
    let (public, native) = max_question();
    let before = serde_json::to_vec(&native).unwrap();
    for (a, b, expected) in [(3, 2, 3), (1, 2, 2), (u64::MAX, 0, u64::MAX)] {
        let out = Interpreter::with_module(&native.module)
            .execute_func(
                FuncId::new(0),
                [
                    InterpretValue::int(Ty::U64, i128::from(a)).unwrap(),
                    InterpretValue::int(Ty::U64, i128::from(b)).unwrap(),
                ],
            )
            .unwrap();
        assert_eq!(
            out.returns,
            vec![InterpretValue::int(Ty::U64, i128::from(expected)).unwrap()]
        );
    }
    let proof = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    assert!(proof.uses_declared_entry());
    assert!(matches!(
        proof.witness().coverage,
        trust_wp_lib::trust_ir_body::NativeBodyWpTranslationCoverage::Untranslated { .. }
    ));
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    let failed = verify_native_public_question(&bare, wp_request_id(&native)).unwrap();
    assert_eq!(
        failed.result().status,
        VerifyBundleStatus::Failed,
        "{failed:#?}"
    );
    assert_eq!(serde_json::to_vec(&native).unwrap(), before);
}

#[test]
fn changed_removed_and_forged_entry_domains_do_not_replay_a_conditional_proof() {
    let (public, native) = max_question();
    let proof = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    for change in 0..3 {
        let mut public = public.clone();
        match change {
            0 => {
                public.contracts[1].predicate = api::ContractPredicate::CanonicalJson {
                    schema: "trust-wp.pure-expr.v1".into(),
                    value: "false".into(),
                }
            }
            1 => {
                public.contracts.pop();
                public.obligations.pop();
            }
            _ => {
                let mut context =
                    api::ObligationContext::from_metadata_entry(&public.obligations[1].metadata[0])
                        .unwrap()
                        .unwrap();
                context.function.as_mut().unwrap().path = "demo::other".into();
                public.obligations[1].metadata[0] = context.to_metadata_entry().unwrap();
            }
        }
        let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
        assert!(NativePublicQuestion::new(&public, &admitted, "obligation:post").is_err());
        let bare = NativePublicQuestion::for_derivation(
            &public,
            &admitted,
            "obligation:post",
            NativePublicProofScope::Unconditional,
        )
        .unwrap();
        assert!(
            replay_native_public_question(
                &bare,
                wp_request_id(&native),
                proof.result(),
                Some(proof.witness()),
                proof.public_question_digest().unwrap()
            )
            .is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn unsupported_requires_keeps_a_stronger_bare_true_proof_and_original_translation_shape() {
    let (mut public, mut native) = max_question();
    let formula = native.module.proof_obligations[0].formula.as_mut().unwrap();
    formula.payload = "true".into();
    formula.bindings.clear();
    public.contracts[0].predicate = api::ContractPredicate::CanonicalJson {
        schema: formula.schema.clone(),
        value: "true".into(),
    };
    public.contracts[0].metadata[0].value = "[]".into();
    public.contracts[1].predicate = api::ContractPredicate::CanonicalJson {
        schema: "unsupported.entry.codec.v1".into(),
        value: "unsupported authored requirement".into(),
    };
    refresh(&public, &mut native);
    let proof = prove(&public, &native, NativePublicProofScope::Unconditional);
    assert!(!proof.uses_declared_entry());
    assert!(proof.witness().public_question.is_none());
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let legacy = trust_wp_lib::trust_ir_body::verify_trust_ir_body_request_validated(
        &admitted,
        wp_request_id(&native),
    )
    .unwrap();
    assert_eq!(proof.witness(), legacy.witness());
    assert_eq!(proof.result(), legacy.result());

    public.contracts.truncate(1);
    public.obligations.truncate(1);
    native.module.proof_obligations.truncate(1);
    native.compiler_facts.obligation_sources.truncate(1);
    native.lineage.nodes[0]
        .obligations
        .retain(|id| *id == ProofId::new(0));
    native.module.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    })];
    refresh(&public, &mut native);
    let strong = prove(&public, &native, NativePublicProofScope::Unconditional);
    assert!(matches!(
        strong.witness().coverage,
        trust_wp_lib::trust_ir_body::NativeBodyWpTranslationCoverage::UnsignedAssignmentCfg
    ));
    let declared = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    assert!(matches!(
        declared.witness().coverage,
        trust_wp_lib::trust_ir_body::NativeBodyWpTranslationCoverage::Untranslated { .. }
    ));
}

fn division_question(requirement: &str) -> (api::TrustContractBundle, NativeVerificationBundle) {
    let post = ProofFormula::new("trust-wp.pure-expr.v1", "true");
    let mut native = native_bundle_with_signature(
        post,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::U64],
        vec![Ty::U64],
    );
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    entry.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::UDiv,
            ty: Ty::U64,
            lhs: ValueId::new(1),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }),
    ];
    native.module.functions[0].blocks = vec![entry];
    clear_unexecuted_cast_facts(&mut native);
    let mut pre = ProofFormula::new("trust-wp.pure-expr.v1", requirement);
    pre.bindings = if requirement == "true" {
        vec![]
    } else {
        vec![binding("d", 0, false, ClauseSort::BitVec(64))]
    };
    let public = bind_public(&mut native, pre);
    (public, native)
}

fn fails(public: &api::TrustContractBundle, native: &NativeVerificationBundle) {
    let admitted = trust_ir::ValidatedNativeBundle::new(native).unwrap();
    let question = NativePublicQuestion::new(public, &admitted, "obligation:post").unwrap();
    let failed = verify_native_public_question(&question, wp_request_id(&native)).unwrap();
    assert_eq!(
        failed.result().status,
        VerifyBundleStatus::Failed,
        "{failed:#?}"
    );
    assert!(replay_native_public_question(
        &question,
        wp_request_id(&native),
        failed.result(),
        Some(failed.witness()),
        failed.public_question_digest().unwrap()
    )
    .is_err());
}

#[test]
fn division_definedness_is_owed_under_the_exact_declared_domain_even_with_a_true_post() {
    let (public, native) = division_question("d != 0");
    let zero = InterpretValue::int(Ty::U64, 0).unwrap();
    assert!(Interpreter::with_module(&native.module)
        .execute_func(FuncId::new(0), [zero.clone()])
        .is_err());
    assert_eq!(
        Interpreter::with_module(&native.module)
            .execute_func(FuncId::new(0), [InterpretValue::int(Ty::U64, 1).unwrap(),])
            .unwrap()
            .returns,
        vec![InterpretValue::int(Ty::U64, 1).unwrap()]
    );
    prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    // Both hostile domains admit an actually undefined execution. No changed
    // postcondition or omitted quotient can conceal the owed nonzero guard.
    for requirement in ["d == 0", "true"] {
        let (public, native) = division_question(requirement);
        assert!(Interpreter::with_module(&native.module)
            .execute_func(FuncId::new(0), [zero.clone()])
            .is_err());
        fails(&public, &native);
    }
}

fn callee_question(
    root_requirement: &str,
    divide: bool,
) -> (api::TrustContractBundle, NativeVerificationBundle) {
    let (mut public, mut native) = division_question(root_requirement);
    let mut callee = native.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "callee".into();
    callee.display_path = Some("demo::callee".into());
    if divide {
        callee.blocks[0].body[1]
            .proofs
            .push(trust_ir::ProofAnnotation::DivNonZero);
    } else {
        callee.blocks[0].body = vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })];
    }
    native.module.try_add_function(callee).unwrap();
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    entry.body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    native.module.functions[0].blocks = vec![entry];
    let mut requirement = native.module.proof_obligations[1].formula.clone().unwrap();
    requirement.payload = "d != 0".into();
    public_clause(
        &mut public,
        "callee_entry",
        api::ContractKind::Requires,
        &requirement,
    );
    let last = public.obligations.last_mut().unwrap();
    let mut context = api::ObligationContext::from_metadata_entry(&last.metadata[0])
        .unwrap()
        .unwrap();
    context.function.as_mut().unwrap().path = "demo::callee".into();
    last.metadata[0] = context.to_metadata_entry().unwrap();
    let mut pre = native.module.proof_obligations[1].clone();
    pre.id = ProofId::new(2);
    pre.function = Some(FuncId::new(1));
    pre.formula = Some(requirement);
    let source = pre.source.as_mut().unwrap();
    source.source_id = "callee_entry".into();
    source.assertion_id = "trust-assertion:callee_entry".into();
    native.module.proof_obligations.push(pre);
    let mut source = native.compiler_facts.obligation_sources[1].clone();
    source.obligation = ProofId::new(2);
    source.function = Some(FuncId::new(1));
    source.public_obligation_id = "obligation:callee_entry".into();
    source.assertion_id = Some(NativeAssertionId::new(2));
    source.monomorphization = None;
    source.facts.clear();
    native.compiler_facts.obligation_sources.push(source);
    native.lineage.nodes[0].obligations.push(ProofId::new(2));
    refresh(&public, &mut native);
    (public, native)
}

#[test]
fn a_callee_requirement_is_owed_at_the_call_and_cannot_be_an_invented_premise() {
    let (public, native) = callee_question("d == 0", true);
    assert!(Interpreter::with_module(&native.module)
        .execute_func(FuncId::new(0), [InterpretValue::int(Ty::U64, 0).unwrap(),])
        .is_err());
    fails(&public, &native);
}

#[test]
fn a_total_callee_still_owes_its_declared_requirement_with_a_true_caller_post() {
    let (public, native) = callee_question("d == 0", false);
    assert_eq!(
        Interpreter::with_module(&native.module)
            .execute_func(FuncId::new(0), [InterpretValue::int(Ty::U64, 0).unwrap()])
            .unwrap()
            .returns,
        vec![InterpretValue::int(Ty::U64, 0).unwrap()]
    );
    // No assertion or division can independently make this total body fail:
    // rejection depends on owing the original callee declaration at the call.
    fails(&public, &native);
    let (public, native) = callee_question("d != 0", false);
    assert_eq!(
        Interpreter::with_module(&native.module)
            .execute_func(FuncId::new(0), [InterpretValue::int(Ty::U64, 1).unwrap()])
            .unwrap()
            .returns,
        vec![InterpretValue::int(Ty::U64, 1).unwrap()]
    );
    prove(&public, &native, NativePublicProofScope::DeclaredEntry);
}

#[test]
fn unconditional_root_scope_still_owes_a_total_callees_requires() {
    let mut safe_witness = None;
    for safe in [true, false] {
        let (public, mut native) = callee_question("d == 0", false);
        // The actual argument fixes the callee domain independently of root
        // premises. Both bodies are total; the caller post remains true.
        let body = &mut native.module.functions[0].blocks[0].body;
        body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: trust_ir::Constant::Int(i128::from(safe)),
            })
            .with_result(ValueId::new(2)),
        );
        let Inst::Call { args, .. } = &mut body[1].inst else {
            unreachable!()
        };
        *args = vec![ValueId::new(2)];
        refresh(&public, &mut native);
        for input in [0, u64::MAX] {
            assert_eq!(
                Interpreter::with_module(&native.module)
                    .execute_func(
                        FuncId::new(0),
                        [InterpretValue::int(Ty::U64, input.into()).unwrap()],
                    )
                    .unwrap()
                    .returns,
                vec![InterpretValue::int(Ty::U64, u64::from(safe).into()).unwrap()]
            );
        }
        let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
        let question = NativePublicQuestion::for_derivation(
            &public,
            &admitted,
            "obligation:post",
            NativePublicProofScope::Unconditional,
        )
        .unwrap();
        let result = verify_native_public_question(&question, wp_request_id(&native)).unwrap();
        println!(
            "unconditional total-callee safe={safe} actual={:?}",
            result.result().status
        );
        assert_eq!(
            result.result().status,
            if safe {
                VerifyBundleStatus::Verified
            } else {
                VerifyBundleStatus::Failed
            },
            "root-premise-free does not erase callee Requires: safe={safe}"
        );
        if safe {
            replay_native_public_question(
                &question,
                wp_request_id(&native),
                result.result(),
                Some(result.witness()),
                question.digest_sha256(),
            )
            .unwrap();
            assert!(!result.uses_declared_entry());
            safe_witness = result.witness().public_question.clone();
        }
    }
    let witness =
        safe_witness.expect("callee obligations remain in the original derivation witness");
    assert!(!witness.uses_declared_entry);
    assert_eq!(
        witness
            .contracts
            .iter()
            .map(|(function, proof, _)| (*function, *proof))
            .collect::<Vec<_>>(),
        vec![(FuncId::new(1), ProofId::new(2))]
    );
}

#[test]
fn unconditional_scope_cannot_borrow_a_conditional_result_without_a_witness() {
    let (public, native) = max_question();
    let original = native.clone();
    let conditional = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let declared = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    replay_native_public_question(
        &declared,
        wp_request_id(&native),
        conditional.result(),
        None,
        declared.digest_sha256(),
    )
    .unwrap();
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert_eq!(
        bare.digest_sha256(),
        declared.digest_sha256(),
        "the original question is unchanged"
    );
    assert!(replay_native_public_question(&bare,wp_request_id(&native),conditional.result(),None,bare.digest_sha256()).is_err(),
        "omitting a diagnostic witness cannot transfer conditional evidence into a root-premise-free derivation");
    assert_eq!(native, original);
}

#[test]
fn an_unrelated_original_entry_does_not_narrow_the_selected_body_fragment() {
    let (mut public, mut native) = max_question();
    let ty = native
        .module
        .add_func_type(FuncTy::unrecorded(vec![Ty::I32], vec![Ty::I32], false))
        .unwrap();
    let mut function = Function::new(FuncId::new(1), "demo::unused", ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I32);
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    native.module.try_add_function(function).unwrap();
    let mut requirement = ProofFormula::new("trust-wp.pure-expr.v1", "x > 0");
    requirement.bindings = vec![binding("x", 0, false, ClauseSort::Int)];
    public_clause(
        &mut public,
        "unused_entry",
        api::ContractKind::Requires,
        &requirement,
    );
    let obligation = public.obligations.last_mut().unwrap();
    let mut context = api::ObligationContext::from_metadata_entry(&obligation.metadata[0])
        .unwrap()
        .unwrap();
    context.function.as_mut().unwrap().path = "demo::unused".into();
    obligation.metadata[0] = context.to_metadata_entry().unwrap();
    let mut pre = native.module.proof_obligations[1].clone();
    pre.id = ProofId::new(2);
    pre.function = Some(FuncId::new(1));
    pre.formula = Some(requirement);
    let source = pre.source.as_mut().unwrap();
    source.source_id = "unused_entry".into();
    source.assertion_id = "trust-assertion:unused_entry".into();
    native.module.proof_obligations.push(pre);
    let mut source = native.compiler_facts.obligation_sources[1].clone();
    source.obligation = ProofId::new(2);
    source.function = Some(FuncId::new(1));
    source.public_obligation_id = "obligation:unused_entry".into();
    source.assertion_id = Some(NativeAssertionId::new(2));
    source.monomorphization = None;
    source.facts.clear();
    native.compiler_facts.obligation_sources.push(source);
    native.lineage.nodes[0].obligations.push(ProofId::new(2));
    refresh(&public, &mut native);
    // The unrelated signed function is valid IR, but its entry is outside
    // scalar body WP's supported unsigned binding model and is never consumed.
    prove(&public, &native, NativePublicProofScope::DeclaredEntry);
}

#[test]
fn coherent_entry_maps_still_obey_canonical_program_types_and_the_body_fragment() {
    for sort in [
        ClauseSort::Bool,
        ClauseSort::BitVec(8),
        ClauseSort::BitVec(32),
        ClauseSort::Int,
    ] {
        let (mut public, mut native) = max_question();
        let formula = native.module.proof_obligations[1].formula.as_mut().unwrap();
        formula.bindings[0].1.sort = sort;
        public.contracts[1].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
        refresh(&public, &mut native);
        let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
        // Correspondence is not a sort/SSA/definedness proof. The existing IR
        // clause typing and scalar binder retain their independent duties.
        let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
        let error = verify_native_public_question(&question, wp_request_id(&native))
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("binding") || error.contains("sort") || error.contains("type"),
            "canonical typing/binding refusal required: {error}"
        );
    }
}

#[test]
fn coherently_changed_declared_domain_cannot_relabel_the_original_conditional_evidence() {
    let (mut public, mut native) = max_question();
    let original = prove(&public, &native, NativePublicProofScope::DeclaredEntry);
    let formula = native.module.proof_obligations[1].formula.as_mut().unwrap();
    formula.payload = "true".into();
    formula.bindings.clear();
    public.contracts[1].predicate = api::ContractPredicate::CanonicalJson {
        schema: formula.schema.clone(),
        value: formula.payload.clone().into(),
    };
    public.contracts[1].metadata[0].value = "[]".into();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let changed = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    assert_ne!(
        Some(changed.digest_sha256()),
        original.public_question_digest()
    );
    // Even falsely attributing the old result to the new digest cannot bypass
    // independent regeneration of the original premise-dependent derivation.
    for witness in [None, Some(original.witness())] {
        assert!(replay_native_public_question(
            &changed,
            wp_request_id(&native),
            original.result(),
            witness,
            changed.digest_sha256(),
        )
        .is_err());
    }
    fails(&public, &native);
}

#[test]
fn a_declared_entry_does_not_turn_executed_assumes_or_asserts_into_premises() {
    for assertion in [false, true] {
        let (public, mut native) = division_question("d != 0");
        native.module.functions[0].blocks[0].body.splice(
            0..0,
            [
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                })
                .with_result(ValueId::new(900)),
                InstrNode::new(if assertion {
                    Inst::Assert {
                        cond: ValueId::new(900),
                        kind: trust_ir::AssertKind::Unspecified,
                        site: None,
                    }
                } else {
                    Inst::Assume {
                        cond: ValueId::new(900),
                    }
                }),
            ],
        );
        refresh(&public, &mut native);
        assert!(Interpreter::with_module(&native.module)
            .execute_func(FuncId::new(0), [InterpretValue::int(Ty::U64, 1).unwrap(),])
            .is_err());
        fails(&public, &native);
    }
}
