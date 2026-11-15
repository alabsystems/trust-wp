use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts, verify_trust_ir_body_contracts, TRUST_IR_BODY_WP_SCHEMA,
};

use super::*;

#[path = "validated.rs"]
mod validated;

#[path = "local_calls.rs"]
mod local_calls;

fn boolean_function(contract: &str, negate: bool) -> NativeVerificationBundle {
    let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", contract);
    formula.bindings = vec![
        (
            "x".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "r".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
    ];
    let mut bundle = native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::Bool],
        vec![Ty::Bool],
    );
    let function = bundle.module.function_by_id_mut(FuncId::new(0)).unwrap();
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(false),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(if negate {
            Inst::Select {
                ty: Ty::Bool,
                cond: ValueId::new(0),
                then_val: ValueId::new(1),
                else_val: ValueId::new(2),
            }
        } else {
            Inst::Copy {
                ty: Ty::Bool,
                operand: ValueId::new(0),
            }
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    function.blocks = vec![entry];
    // The generic wire fixture's cast does not occur in this Boolean body.
    bundle.compiler_facts.casts.clear();
    for source in &mut bundle.compiler_facts.obligation_sources {
        source
            .facts
            .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));
    }
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

fn verified(bundle: &NativeVerificationBundle) -> Vec<trust_wp_lib::VerifyBundleResult> {
    let result = verify_trust_ir_body_contracts(bundle).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].status,
        VerifyBundleStatus::Verified,
        "{result:#?}"
    );
    assert!(result[0].bundle_id.starts_with(TRUST_IR_BODY_WP_SCHEMA));
    replay_trust_ir_body_contracts(bundle, &result).unwrap();
    assert_reference_returns(bundle, |input| !input);
    result
}

fn assert_reference_returns(bundle: &NativeVerificationBundle, expected: impl Fn(bool) -> bool) {
    for input in [false, true] {
        let output = trust_ir::interpret::Interpreter::with_module(&bundle.module)
            .execute_func(
                FuncId::new(0),
                [trust_ir::interpret::InterpretValue::bool(input)],
            )
            .expect("every admitted instruction must execute in the shared reference model");
        assert_eq!(
            output.returns,
            vec![trust_ir::interpret::InterpretValue::bool(expected(input))]
        );
    }
}

#[test]
fn scalar_boolean_not_is_refused_by_shared_semantics_before_wp() {
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
    assert!(trust_ir_build::validate_module(&bundle.module)
        .iter()
        .any(|error| matches!(
            error,
            trust_ir_build::ValidationError::UnOpNotOnScalarBool { .. }
        )));
    assert!(
        trust_ir::interpret::Interpreter::with_module(&bundle.module)
            .execute_func(
                FuncId::new(0),
                [trust_ir::interpret::InterpretValue::bool(true)]
            )
            .is_err()
    );
    assert!(verify_trust_ir_body_contracts(&bundle).is_err());
}

#[test]
fn copy_body_agrees_with_the_shared_reference_for_every_input() {
    let bundle = boolean_function("(r : bool) == (x : bool)", false);
    let results = verify_trust_ir_body_contracts(&bundle).unwrap();
    assert_eq!(results[0].status, VerifyBundleStatus::Verified);
    replay_trust_ir_body_contracts(&bundle, &results).unwrap();
    assert_reference_returns(&bundle, |input| input);
}

#[test]
fn typed_body_proves_nonconstant_postcondition_and_replays() {
    let bundle = boolean_function("r == !x", true);
    let result = verified(&bundle);
    let json = serde_json::to_vec(&result).unwrap();
    let restored: Vec<trust_wp_lib::VerifyBundleResult> = serde_json::from_slice(&json).unwrap();
    replay_trust_ir_body_contracts(&bundle, &restored).unwrap();
    assert!(matches!(
        result[0].obligation_results[0].status,
        BundleObligationStatus::Verified { .. }
    ));
}

#[test]
fn wrong_body_and_wrong_contract_never_verify() {
    for bundle in [
        boolean_function("r == !x", false),
        boolean_function("(r : bool) == (x : bool)", true),
    ] {
        let result = verify_trust_ir_body_contracts(&bundle).unwrap();
        assert_ne!(result[0].status, VerifyBundleStatus::Verified);
        assert!(replay_trust_ir_body_contracts(&bundle, &result).is_err());
    }
}

#[test]
fn proof_is_bound_to_original_body_contract_source_and_method() {
    let bundle = boolean_function("r == !x", true);
    let proof = verified(&bundle);
    for other in [
        boolean_function("r == !x", false),
        boolean_function("r != !x", true),
    ] {
        assert!(replay_trust_ir_body_contracts(&other, &proof).is_err());
    }
    let mut changed = bundle.clone();
    changed.compiler_facts.obligation_sources[0]
        .public_obligation_id
        .push_str("-other");
    assert!(replay_trust_ir_body_contracts(&changed, &proof).is_err());
    let legacy = verify_trust_ir_native_bundle(&bundle).unwrap();
    assert!(replay_trust_ir_body_contracts(&bundle, &legacy).is_err());
    let mut changed = proof.clone();
    changed[0].bundle_id.push_str("-other");
    assert!(replay_trust_ir_body_contracts(&bundle, &changed).is_err());
    let mut changed = proof.clone();
    changed[0]
        .aggregate_evidence
        .as_mut()
        .unwrap()
        .artifacts
        .clear();
    assert!(replay_trust_ir_body_contracts(&bundle, &changed).is_err());
    let mut changed = proof.clone();
    if let BundleObligationStatus::Verified { evidence } =
        &mut changed[0].obligation_results[0].status
    {
        evidence.artifacts[0] = evidence.artifacts[0]
            .clone()
            .with_utf8_bytes("forged proof payload");
    }
    assert!(replay_trust_ir_body_contracts(&bundle, &changed).is_err());
}

#[test]
fn every_free_contract_name_requires_a_typed_place_binding() {
    let mut bundle = boolean_function("r == !x", true);
    bundle.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings
        .pop();
    refresh_native_bundle_module_identity(&mut bundle);
    assert!(verify_trust_ir_body_contracts(&bundle).is_err());
}

#[test]
fn shared_compiler_formula_uses_its_canonical_typed_decoder() {
    use trust_ir_contract::{Formula, Sort};
    let mut bundle = boolean_function("r == !x", true);
    let formula = bundle.module.proof_obligations[0].formula.as_mut().unwrap();
    formula.schema = "trust-types.Formula@1".into();
    formula.payload = serde_json::to_string(&Formula::Eq(
        Box::new(Formula::Var("r".into(), Sort::Bool)),
        Box::new(Formula::Not(Box::new(Formula::Var("x".into(), Sort::Bool)))),
    ))
    .unwrap();
    refresh_native_bundle_module_identity(&mut bundle);
    verified(&bundle);
    let formula = bundle.module.proof_obligations[0].formula.as_mut().unwrap();
    formula.payload = serde_json::to_string(&Formula::Eq(
        Box::new(Formula::Var("r".into(), Sort::Bool)),
        Box::new(Formula::Var("x".into(), Sort::Bool)),
    ))
    .unwrap();
    refresh_native_bundle_module_identity(&mut bundle);
    assert_ne!(
        verify_trust_ir_body_contracts(&bundle).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
}

#[test]
fn block_arguments_are_substituted_simultaneously() {
    let mut bundle = boolean_function("r == !x", true);
    let function = bundle.module.function_by_id_mut(FuncId::new(0)).unwrap();
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(false),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1), ValueId::new(0)],
    }));
    let mut next = Block::new(BlockId::new(1))
        .with_param(ValueId::new(2), Ty::Bool)
        .with_param(ValueId::new(3), Ty::Bool);
    next.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(4)),
    );
    next.body.push(
        InstrNode::new(Inst::Select {
            ty: Ty::Bool,
            cond: ValueId::new(3),
            then_val: ValueId::new(2),
            else_val: ValueId::new(4),
        })
        .with_result(ValueId::new(5)),
    );
    next.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(5)],
    }));
    function.blocks = vec![entry, next];
    refresh_native_bundle_module_identity(&mut bundle);
    verified(&bundle);
    let function = bundle.module.function_by_id_mut(FuncId::new(0)).unwrap();
    if let Inst::Br { args, .. } = &mut function.blocks[0].body[1].inst {
        args.swap(0, 1);
    }
    refresh_native_bundle_module_identity(&mut bundle);
    assert_ne!(
        verify_trust_ir_body_contracts(&bundle).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
}

#[test]
fn wrong_binding_extra_binding_duplicate_ssa_and_branch_arity_refuse() {
    let original = boolean_function("r == !x", true);
    let mut bad = original.clone();
    bad.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings[1]
        .1
        .place = ClausePlace::Param { index: 0 };
    refresh_native_bundle_module_identity(&mut bad);
    assert_ne!(
        verify_trust_ir_body_contracts(&bad).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
    let mut bad = original.clone();
    bad.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings
        .push((
            "extra".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 0 },
            },
        ));
    refresh_native_bundle_module_identity(&mut bad);
    assert!(verify_trust_ir_body_contracts(&bad).is_err());
    let mut bad = original.clone();
    bad.module
        .function_by_id_mut(FuncId::new(0))
        .unwrap()
        .blocks[0]
        .body[0]
        .results[0] = ValueId::new(0);
    refresh_native_bundle_module_identity(&mut bad);
    assert!(verify_trust_ir_body_contracts(&bad).is_err());
    let mut bad = original.clone();
    bad.module
        .function_by_id_mut(FuncId::new(0))
        .unwrap()
        .blocks[0]
        .body = vec![InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![],
    })];
    let mut target = Block::new(BlockId::new(1)).with_param(ValueId::new(2), Ty::Bool);
    target.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    bad.module
        .function_by_id_mut(FuncId::new(0))
        .unwrap()
        .blocks
        .push(target);
    refresh_native_bundle_module_identity(&mut bad);
    assert!(verify_trust_ir_body_contracts(&bad).is_err());
}

#[test]
fn branch_wp_reads_both_arms_and_shared_interpreter_semantics() {
    let mut bundle = boolean_function("r == !x", true);
    let function = bundle.module.function_by_id_mut(FuncId::new(0)).unwrap();
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(0),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));
    let mut yes = Block::new(BlockId::new(1));
    yes.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(false),
        })
        .with_result(ValueId::new(1)),
    );
    yes.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    let mut no = Block::new(BlockId::new(2));
    no.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(2)),
    );
    no.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    function.blocks = vec![entry, yes, no];
    refresh_native_bundle_module_identity(&mut bundle);
    verified(&bundle);
    for x in [false, true] {
        let output = trust_ir::interpret::Interpreter::with_module(&bundle.module)
            .execute_func(
                FuncId::new(0),
                vec![trust_ir::interpret::InterpretValue::bool(x)],
            )
            .unwrap();
        assert_eq!(
            output.returns,
            vec![trust_ir::interpret::InterpretValue::bool(!x)]
        );
    }
    let function = bundle.module.function_by_id_mut(FuncId::new(0)).unwrap();
    function.blocks[2].body[0].inst = Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(false),
    };
    refresh_native_bundle_module_identity(&mut bundle);
    assert_ne!(
        verify_trust_ir_body_contracts(&bundle).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
}

#[test]
fn malformed_and_unsupported_bodies_refuse_even_a_tautological_contract() {
    let original = boolean_function("((r : bool) == r) && ((x : bool) == x)", true);
    for invalid in [
        Inst::Copy {
            ty: Ty::Bool,
            operand: ValueId::new(99),
        },
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        },
        Inst::Br {
            target: BlockId::new(0),
            args: vec![ValueId::new(0)],
        },
    ] {
        let mut bundle = original.clone();
        bundle
            .module
            .function_by_id_mut(FuncId::new(0))
            .unwrap()
            .blocks[0]
            .body[0]
            .inst = invalid;
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(verify_trust_ir_body_contracts(&bundle).is_err());
    }
}

// Actual shared TrustIR functions exported by the compiler from:
// fn identity(x: bool) -> bool ensures result == x { x }
// fn wrong(x: bool) -> bool ensures result == x { false }
// The function Pure annotation must not be a premise for either verdict.
#[test]
fn compiler_pure_annotation_preserves_body_sensitive_postcondition_verdicts() {
    for (input, wrong) in [
        (include_str!("fixtures/identity_function.json"), false),
        (include_str!("fixtures/wrong_function.json"), true),
    ] {
        let function: Function = serde_json::from_str(input).unwrap();
        assert_eq!(function.proofs, vec![trust_ir::ProofAnnotation::Pure]);
        let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
        bundle.module.functions[0] = function;
        bundle.provenance.source_language = trust_ir::NativeSourceLanguage::Rust;
        bundle.provenance.source_languages = [
            trust_ir::NativeSourceLanguage::Rust,
            trust_ir::NativeSourceLanguage::TrustIr,
        ]
        .into_iter()
        .collect();
        refresh_native_bundle_module_identity(&mut bundle);
        assert_reference_returns(&bundle, |x| if wrong { false } else { x });
        let results = verify_trust_ir_body_contracts(&bundle).unwrap();
        assert_eq!(results[0].status == VerifyBundleStatus::Verified, !wrong);
        if wrong {
            assert!(replay_trust_ir_body_contracts(&bundle, &results).is_err());
        } else {
            replay_trust_ir_body_contracts(&bundle, &results).unwrap();
        }
    }
}

#[test]
fn pure_marker_does_not_admit_assumptions_attributes_or_effects() {
    for mutation in 0..4 {
        let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
        let function = &mut bundle.module.functions[0];
        function.proofs = vec![trust_ir::ProofAnnotation::Pure];
        match mutation {
            0 => function.proofs.push(trust_ir::ProofAnnotation::NoPanic),
            1 => function.attrs.readonly = true,
            2 => function.blocks[0].body.insert(
                0,
                InstrNode::new(Inst::Fence {
                    ordering: trust_ir::inst::Ordering::SeqCst,
                }),
            ),
            3 => function.blocks[0].body[0]
                .proofs
                .push(trust_ir::ProofAnnotation::Pure),
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
fn unproved_summary_conclusions_never_supply_body_premises() {
    for negate in [false, true] {
        let mut bundle = boolean_function("(r : bool) == (x : bool)", negate);
        let mut summary = trust_ir::FunctionSummary::new();
        summary.params = vec!["x".into()];
        summary
            .ensures
            .push(ProofFormula::new("trust-wp.pure-expr.v1", "false"));
        bundle.module.functions[0].summary = Some(summary);
        refresh_native_bundle_module_identity(&mut bundle);
        let immutable = bundle.clone();
        let result = verify_trust_ir_body_contracts(&bundle).unwrap();
        let admitted = trust_ir::ValidatedNativeBundle::new(&bundle).unwrap();
        let validated =
            trust_wp_lib::trust_ir_body::verify_trust_ir_body_contracts_validated(&admitted)
                .unwrap();
        assert_eq!(validated[0].status, result[0].status);
        if !negate {
            trust_wp_lib::trust_ir_body::replay_trust_ir_body_contracts_validated(
                &admitted, &validated,
            )
            .unwrap();
        }
        assert_eq!(result.len(), 1);
        assert_eq!(
            result[0].status == VerifyBundleStatus::Verified,
            !negate,
            "{result:#?}"
        );
        if !negate {
            replay_trust_ir_body_contracts(&bundle, &result).unwrap();
        }
        assert_eq!(bundle, immutable);
    }
}

#[test]
fn changing_an_unproved_summary_still_invalidates_old_replay() {
    let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
    let mut summary = trust_ir::FunctionSummary::new();
    summary.params = vec!["x".into()];
    summary
        .ensures
        .push(ProofFormula::new("trust-wp.pure-expr.v1", "false"));
    bundle.module.functions[0].summary = Some(summary);
    refresh_native_bundle_module_identity(&mut bundle);
    let proof = verify_trust_ir_body_contracts(&bundle).unwrap();
    assert_eq!(proof[0].status, VerifyBundleStatus::Verified);
    bundle.module.functions[0].summary.as_mut().unwrap().ensures[0].payload = "true".into();
    refresh_native_bundle_module_identity(&mut bundle);
    assert!(replay_trust_ir_body_contracts(&bundle, &proof).is_err());
    let admitted = trust_ir::ValidatedNativeBundle::new(&bundle).unwrap();
    assert!(
        trust_wp_lib::trust_ir_body::replay_trust_ir_body_contracts_validated(&admitted, &proof)
            .is_err()
    );
    let fresh = verify_trust_ir_body_contracts(&bundle).unwrap();
    replay_trust_ir_body_contracts(&bundle, &fresh).unwrap();
}

#[test]
fn summaries_with_premises_authority_or_effect_claims_remain_refused() {
    for mutation in [
        "requires",
        "decreases",
        "proved",
        "effects",
        "arity",
        "empty-name",
    ] {
        let mut bundle = boolean_function("(r : bool) == (x : bool)", true);
        let mut summary = trust_ir::FunctionSummary::new();
        summary.params = vec!["x".into()];
        summary
            .ensures
            .push(ProofFormula::new("trust-wp.pure-expr.v1", "false"));
        match mutation {
            "requires" => summary
                .requires
                .push(ProofFormula::new("trust-wp.pure-expr.v1", "false")),
            "decreases" => summary.decreases.push(ProofFormula::new("smtlib2", "0")),
            "proved" => summary.proved = true,
            "effects" => summary.effects = Some(trust_ir::effects::EffectSummary::pure()),
            "arity" => summary.params.clear(),
            "empty-name" => summary.params[0].clear(),
            _ => unreachable!(),
        }
        bundle.module.functions[0].summary = Some(summary);
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(
            verify_trust_ir_body_contracts(&bundle).is_err(),
            "{mutation}"
        );
    }
}

#[test]
fn named_external_backing_stays_outside_pending_summary_fragment() {
    let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
    bundle.module.imports.push(trust_ir::ModuleImport::new(
        "external",
        ProofDigest::sha256([7; 32]),
    ));
    let mut summary = trust_ir::FunctionSummary::new();
    summary.params = vec!["x".into()];
    summary
        .ensures
        .push(ProofFormula::new("trust-wp.pure-expr.v1", "true"));
    summary.backed_by = Some(trust_ir::ExternRef::new(
        trust_ir::ImportId::new(0),
        "entity-only",
    ));
    bundle.module.functions[0].summary = Some(summary);
    refresh_native_bundle_module_identity(&mut bundle);
    assert_eq!(trust_ir_build::validate_module(&bundle.module), []);
    bundle.validate().unwrap();
    assert!(verify_trust_ir_body_contracts(&bundle).is_err());
}

#[test]
fn duplicate_summary_names_are_refused_at_valid_parameter_arity() {
    let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
    let function = &mut bundle.module.functions[0];
    bundle.module.func_types[function.ty.index() as usize]
        .params
        .push(Ty::Bool);
    function.blocks[0].params.push((ValueId::new(4), Ty::Bool));
    let mut summary = trust_ir::FunctionSummary::new();
    summary.params = vec!["x".into(), "y".into()];
    summary
        .ensures
        .push(ProofFormula::new("trust-wp.pure-expr.v1", "true"));
    function.summary = Some(summary);
    refresh_native_bundle_module_identity(&mut bundle);
    assert_eq!(trust_ir_build::validate_module(&bundle.module), []);
    let proof = verify_trust_ir_body_contracts(&bundle).unwrap();
    assert_eq!(proof[0].status, VerifyBundleStatus::Verified);
    bundle.module.functions[0].summary.as_mut().unwrap().params[1] = "x".into();
    refresh_native_bundle_module_identity(&mut bundle);
    assert_eq!(trust_ir_build::validate_module(&bundle.module), []);
    assert!(verify_trust_ir_body_contracts(&bundle).is_err());
}

#[test]
fn pending_summary_conclusions_keep_the_native_fragment_budgets() {
    for many in [false, true] {
        let mut bundle = boolean_function("(r : bool) == (x : bool)", false);
        let mut summary = trust_ir::FunctionSummary::new();
        summary.params = vec!["x".into()];
        if many {
            summary.ensures = vec![ProofFormula::new("trust-wp.pure-expr.v1", "true"); 1025];
        } else {
            summary.ensures.push(ProofFormula::new(
                "trust-wp.pure-expr.v1",
                "x".repeat(262_145),
            ));
        }
        bundle.module.functions[0].summary = Some(summary);
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(verify_trust_ir_body_contracts(&bundle).is_err());
    }
}
