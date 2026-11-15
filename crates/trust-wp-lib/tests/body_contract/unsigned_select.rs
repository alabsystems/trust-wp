//! Native scalar Select and its equivalent branch/parameter program ask the
//! same original typed contract. These are shared-IR fixtures, not Rust captures.

use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts, replay_trust_ir_body_translation_witnesses,
    trust_ir_native_bundle_to_body_translation_witnesses, verify_trust_ir_body_contracts,
    NativeBodyWpTranslationCoverage,
};

use super::*;

#[derive(Clone, Copy)]
enum Shape {
    Select,
    Branch,
}

fn question(ty: Ty, shape: Shape, wrong_clause: bool) -> NativeVerificationBundle {
    let sort = if ty == Ty::Bool { "bool" } else { "int" };
    let scalar_sort = match &ty {
        Ty::Bool => ClauseSort::Bool,
        Ty::U8 => ClauseSort::BitVec(8),
        Ty::U32 => ClauseSort::BitVec(32),
        Ty::U64 => ClauseSort::BitVec(64),
        _ => panic!("scalar fixture type"),
    };
    let mut formula = ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        serde_json::json!({
            "schema": TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            "variables": [
                {"name":"c", "sort":"bool"},
                {"name":"x", "sort":sort},
                {"name":"y", "sort":sort},
                {"name":"r", "sort":sort}
            ],
            "body": {
                "op":"and",
                "lhs": {"op":"implies", "lhs":{"var":"c"},
                    "rhs":{"op":"eq", "lhs":{"var":"r"}, "rhs":{"var":"x"}}},
                "rhs": {"op":"implies", "lhs":{"op":"not", "expr":{"var":"c"}},
                    "rhs":{"op":if wrong_clause { "ne" } else { "eq" },
                        "lhs":{"var":"r"}, "rhs":{"var":"y"}}}
            }
        })
        .to_string(),
    );
    formula.bindings = vec![
        (
            "c".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "x".into(),
            ClauseBinding {
                sort: scalar_sort.clone(),
                place: ClausePlace::Param { index: 1 },
            },
        ),
        (
            "y".into(),
            ClauseBinding {
                sort: scalar_sort.clone(),
                place: ClausePlace::Param { index: 2 },
            },
        ),
        (
            "r".into(),
            ClauseBinding {
                sort: scalar_sort,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
    ];
    let mut bundle = native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![Ty::Bool, ty.clone(), ty.clone()],
        vec![ty.clone()],
    );
    bundle.compiler_facts.casts.clear();
    for source in &mut bundle.compiler_facts.obligation_sources {
        source
            .facts
            .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));
    }
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), Ty::Bool)
        .with_param(ValueId::new(1), ty.clone())
        .with_param(ValueId::new(2), ty.clone());
    let blocks = match shape {
        Shape::Select => {
            entry.body = vec![
                InstrNode::new(Inst::Select {
                    ty,
                    cond: ValueId::new(0),
                    then_val: ValueId::new(1),
                    else_val: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(3)],
                }),
            ];
            vec![entry]
        }
        Shape::Branch => {
            entry.body.push(InstrNode::new(Inst::CondBr {
                cond: ValueId::new(0),
                then_target: BlockId::new(1),
                then_args: vec![ValueId::new(1)],
                else_target: BlockId::new(1),
                else_args: vec![ValueId::new(2)],
            }));
            let mut join = Block::new(BlockId::new(1)).with_param(ValueId::new(3), ty);
            join.body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }));
            vec![entry, join]
        }
    };
    bundle.module.functions[0].blocks = blocks;
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

fn valid(bundle: &NativeVerificationBundle) {
    bundle.validate().unwrap();
    assert_eq!(trust_ir_build::validate_module(&bundle.module), []);
}

fn proved(bundle: &NativeVerificationBundle) -> Vec<trust_wp_lib::VerifyBundleResult> {
    valid(bundle);
    let original = bundle.clone();
    let results = verify_trust_ir_body_contracts(bundle).unwrap();
    assert_eq!(results.len(), 1);
    assert_eq!(
        results[0].status,
        VerifyBundleStatus::Verified,
        "{results:#?}"
    );
    replay_trust_ir_body_contracts(bundle, &results).unwrap();
    assert_eq!(*bundle, original);
    results
}

#[test]
fn unsigned_select_and_branch_parameters_prove_the_same_original_contract() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    for (ty, maximum) in [
        (Ty::U8, u64::from(u8::MAX)),
        (Ty::U32, u64::from(u32::MAX)),
        (Ty::U64, u64::MAX),
    ] {
        let select = question(ty.clone(), Shape::Select, false);
        let branch = question(ty.clone(), Shape::Branch, false);
        assert_eq!(
            select.module.proof_obligations,
            branch.module.proof_obligations
        );
        let results = proved(&select);
        proved(&branch);
        // Equivalent behavior does not license transferring another program's evidence.
        assert!(replay_trust_ir_body_contracts(&branch, &results).is_err());
        for c in [false, true] {
            for (x, y) in [(0, maximum), (maximum, 0), (maximum / 2, maximum / 2 + 1)] {
                let expected =
                    InterpretValue::int(ty.clone(), i128::from(if c { x } else { y })).unwrap();
                for bundle in [&select, &branch] {
                    let observed = Interpreter::with_module(&bundle.module)
                        .execute_func(
                            FuncId::new(0),
                            [
                                InterpretValue::bool(c),
                                InterpretValue::int(ty.clone(), i128::from(x)).unwrap(),
                                InterpretValue::int(ty.clone(), i128::from(y)).unwrap(),
                            ],
                        )
                        .unwrap();
                    assert_eq!(observed.returns, vec![expected.clone()]);
                }
            }
        }
    }
}

#[test]
fn changed_unsigned_select_body_return_and_public_clause_cannot_reuse_evidence() {
    for ty in [Ty::U8, Ty::U32, Ty::U64] {
        let original = question(ty.clone(), Shape::Select, false);
        let evidence = proved(&original);
        let mut swapped = original.clone();
        if let Inst::Select {
            then_val, else_val, ..
        } = &mut swapped.module.functions[0].blocks[0].body[0].inst
        {
            std::mem::swap(then_val, else_val);
        }
        let mut wrong_return = original.clone();
        wrong_return.module.functions[0].blocks[0].body[1].inst = Inst::Return {
            values: vec![ValueId::new(1)],
        };
        for mut changed in [swapped, wrong_return, question(ty, Shape::Select, true)] {
            refresh_native_bundle_module_identity(&mut changed);
            valid(&changed);
            let results = verify_trust_ir_body_contracts(&changed).unwrap();
            assert_ne!(
                results[0].status,
                VerifyBundleStatus::Verified,
                "{results:#?}"
            );
            assert!(replay_trust_ir_body_contracts(&changed, &evidence).is_err());
        }
    }
}

#[test]
fn changed_unsigned_sources_have_checked_counterexamples_to_the_original_question() {
    for ty in [Ty::U8, Ty::U32, Ty::U64] {
        for shape in [Shape::Select, Shape::Branch] {
            let original = question(ty.clone(), shape, false);
            let evidence = proved(&original);
            let mut swapped = original.clone();
            match &mut swapped.module.functions[0].blocks[0].body[0].inst {
                Inst::Select {
                    then_val, else_val, ..
                } => std::mem::swap(then_val, else_val),
                Inst::CondBr {
                    then_args,
                    else_args,
                    ..
                } => std::mem::swap(then_args, else_args),
                _ => panic!("fixture select or branch"),
            }
            // Rebind the same original formula to the opposite same-sort inputs.
            // The canonical public question still names both x and y.
            let mut rebound = original.clone();
            for obligation in &mut rebound.module.proof_obligations {
                for (_, binding) in &mut obligation.formula.as_mut().unwrap().bindings {
                    if let ClausePlace::Param { index } = &mut binding.place {
                        if *index == 1 {
                            *index = 2;
                        } else if *index == 2 {
                            *index = 1;
                        }
                    }
                }
            }
            for mut changed in [swapped, rebound, question(ty.clone(), shape, true)] {
                refresh_native_bundle_module_identity(&mut changed);
                valid(&changed);
                let results = verify_trust_ir_body_contracts(&changed).unwrap();
                assert_eq!(results.len(), 1);
                assert_eq!(
                    results[0].status,
                    VerifyBundleStatus::Failed,
                    "{results:#?}"
                );
                assert!(replay_trust_ir_body_contracts(&changed, &evidence).is_err());
            }
        }
    }
}

#[test]
fn unsigned_select_keeps_scalar_plan_coverage_separate_from_proof_authority() {
    let boolean = question(Ty::Bool, Shape::Select, false);
    let witness = trust_ir_native_bundle_to_body_translation_witnesses(&boolean).unwrap();
    assert_eq!(
        witness[0].coverage,
        NativeBodyWpTranslationCoverage::BooleanAssignmentCfg
    );
    proved(&boolean);
    for ty in [Ty::U8, Ty::U32, Ty::U64] {
        for shape in [Shape::Select, Shape::Branch] {
            let bundle = question(ty.clone(), shape, false);
            let witness = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
            assert_eq!(
                witness[0].coverage,
                NativeBodyWpTranslationCoverage::UnsignedAssignmentCfg
            );
            replay_trust_ir_body_translation_witnesses(&bundle, &witness).unwrap();
            proved(&bundle);
        }
    }
    let mut internal = boolean;
    let body = &mut internal.module.functions[0].blocks[0].body;
    body.splice(
        0..0,
        [
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(u64::MAX)),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Select {
                ty: Ty::U64,
                cond: ValueId::new(0),
                then_val: ValueId::new(4),
                else_val: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
        ],
    );
    refresh_native_bundle_module_identity(&mut internal);
    proved(&internal);
    let witness = trust_ir_native_bundle_to_body_translation_witnesses(&internal).unwrap();
    assert_eq!(
        witness[0].coverage,
        NativeBodyWpTranslationCoverage::UnsignedAssignmentCfg
    );
}

#[test]
fn unsigned_scalar_plan_retains_copy_and_equality_without_erasing_other_capability() {
    for ty in [Ty::U8, Ty::U32, Ty::U64] {
        let mut bundle = question(ty.clone(), Shape::Select, false);
        let body = &mut bundle.module.functions[0].blocks[0].body;
        body.insert(
            0,
            InstrNode::new(Inst::Copy {
                ty: ty.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
        );
        body.insert(
            1,
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
        );
        let Inst::Select { then_val, .. } = &mut body[2].inst else {
            panic!("original Select")
        };
        *then_val = ValueId::new(4);
        refresh_native_bundle_module_identity(&mut bundle);
        proved(&bundle);
        let witness = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
        assert_eq!(
            witness[0].coverage,
            NativeBodyWpTranslationCoverage::UnsignedAssignmentCfg
        );
        let mut plan = &witness[0].plan;
        for node in &bundle.module.functions[0].blocks[0].body {
            assert_eq!(plan.instruction, *node);
            if !matches!(node.inst, Inst::Return { .. }) {
                assert_eq!(plan.successors.len(), 1);
                plan = &plan.successors[0];
            }
        }
        replay_trust_ir_body_translation_witnesses(&bundle, &witness).unwrap();

        let Inst::ICmp { op, .. } = &mut bundle.module.functions[0].blocks[0].body[1].inst else {
            panic!("retained comparison")
        };
        *op = trust_ir::ICmpOp::Ne;
        refresh_native_bundle_module_identity(&mut bundle);
        // An untranslated proof step does not disable an existing engine rule.
        proved(&bundle);
        let untranslated = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
        assert!(matches!(&untranslated[0].coverage,
            NativeBodyWpTranslationCoverage::Untranslated { reasons }
                if reasons.iter().any(|reason| reason.contains("ICmp"))));
        assert!(replay_trust_ir_body_translation_witnesses(&bundle, &witness).is_err());
    }
}

fn cell(ty: &Ty, load: bool) -> InstrNode {
    if load {
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: ValueId::new(4),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(5))
    } else {
        InstrNode::new(Inst::Alloca {
            ty: ty.clone(),
            count: None,
            align: None,
        })
        .with_result(ValueId::new(4))
    }
}

fn store(ty: &Ty, value: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty: ty.clone(),
        ptr: ValueId::new(4),
        value: ValueId::new(value),
        volatile: false,
        align: None,
    })
}

#[test]
fn unsigned_select_does_not_erase_an_unselected_uninitialized_load() {
    let ty = Ty::U64;
    let mut bundle = question(ty.clone(), Shape::Select, false);
    bundle.module.functions[0].blocks[0].body = vec![
        cell(&ty, false),
        cell(&ty, true),
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(6)),
        InstrNode::new(Inst::Select {
            ty,
            cond: ValueId::new(6),
            then_val: ValueId::new(1),
            else_val: ValueId::new(5),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }),
    ];
    refresh_native_bundle_module_identity(&mut bundle);
    valid(&bundle);
    let error = verify_trust_ir_body_contracts(&bundle)
        .unwrap_err()
        .to_string();
    assert!(error.contains("uninitialized"), "{error}");
}

#[test]
fn unsigned_select_retains_a_load_snapshot_across_a_later_store() {
    let ty = Ty::U64;
    let mut bundle = question(ty.clone(), Shape::Select, false);
    bundle.module.functions[0].blocks[0].body = vec![
        cell(&ty, false),
        store(&ty, 1),
        cell(&ty, true),
        InstrNode::new(Inst::Select {
            ty: ty.clone(),
            cond: ValueId::new(0),
            then_val: ValueId::new(5),
            else_val: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
        store(&ty, 2),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }),
    ];
    refresh_native_bundle_module_identity(&mut bundle);
    let evidence = proved(&bundle);
    bundle.module.functions[0].blocks[0].body[1] = store(&ty, 2);
    refresh_native_bundle_module_identity(&mut bundle);
    valid(&bundle);
    assert_ne!(
        verify_trust_ir_body_contracts(&bundle).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
    assert!(replay_trust_ir_body_contracts(&bundle, &evidence).is_err());
}

#[test]
fn unsigned_select_does_not_erase_unsupported_or_recursive_unselected_calls() {
    for recursive in [false, true] {
        let ty = Ty::U64;
        let mut bundle = question(ty.clone(), Shape::Select, false);
        let signature = bundle
            .module
            .add_func_type(FuncTy::unrecorded(
                vec![ty.clone()],
                vec![ty.clone()],
                false,
            ))
            .unwrap();
        let mut callee = Function::new(
            FuncId::new(1),
            "fixture::unselected",
            signature,
            BlockId::new(1),
        );
        let mut block = Block::new(BlockId::new(1)).with_param(ValueId::new(10), ty.clone());
        block.body = vec![
            InstrNode::new(if recursive {
                Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![ValueId::new(10)],
                }
            } else {
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: ty.clone(),
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(10),
                }
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(11)],
            }),
        ];
        callee.blocks = vec![block];
        bundle.module.try_add_function(callee).unwrap();
        bundle.module.functions[0].blocks[0].body = vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(2)],
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Select {
                ty,
                cond: ValueId::new(6),
                then_val: ValueId::new(1),
                else_val: ValueId::new(5),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ];
        refresh_native_bundle_module_identity(&mut bundle);
        valid(&bundle);
        let error = verify_trust_ir_body_contracts(&bundle)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains(if recursive {
                "recursive"
            } else {
                "outside scalar WP"
            }),
            "{error}"
        );
    }
}

#[test]
fn unsigned_select_keeps_canonical_condition_arm_and_ssa_refusals() {
    for mutation in 0..3 {
        let mut bundle = question(Ty::U64, Shape::Select, false);
        let block = &mut bundle.module.functions[0].blocks[0];
        match mutation {
            0 => {
                if let Inst::Select { cond, .. } = &mut block.body[0].inst {
                    *cond = ValueId::new(1);
                }
            }
            1 => {
                block.body.insert(
                    0,
                    InstrNode::new(Inst::Const {
                        ty: Ty::U8,
                        value: Constant::Int(1),
                    })
                    .with_result(ValueId::new(4)),
                );
                if let Inst::Select { then_val, .. } = &mut block.body[1].inst {
                    *then_val = ValueId::new(4);
                }
            }
            _ => {
                if let Inst::Select { then_val, .. } = &mut block.body[0].inst {
                    *then_val = ValueId::new(4);
                }
                block.body.insert(
                    1,
                    InstrNode::new(Inst::Const {
                        ty: Ty::U64,
                        value: Constant::Int(1),
                    })
                    .with_result(ValueId::new(4)),
                );
            }
        }
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(!trust_ir_build::validate_module(&bundle.module).is_empty());
        assert!(verify_trust_ir_body_contracts(&bundle).is_err());
    }
}

#[test]
fn unsigned_select_composes_nested_continuations_and_the_actual_callee() {
    let ty = Ty::U64;
    let mut bundle = question(ty.clone(), Shape::Select, false);
    let mut callee = bundle.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "fixture::choose".into();
    bundle.module.try_add_function(callee).unwrap();
    bundle.module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(0), ValueId::new(1), ValueId::new(2)],
        })
        .with_result(ValueId::new(4)),
        InstrNode::new(Inst::Select {
            ty: ty.clone(),
            cond: ValueId::new(0),
            then_val: ValueId::new(4),
            else_val: ValueId::new(2),
        })
        .with_result(ValueId::new(5)),
        InstrNode::new(Inst::Select {
            ty,
            cond: ValueId::new(0),
            then_val: ValueId::new(5),
            else_val: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }),
    ];
    refresh_native_bundle_module_identity(&mut bundle);
    let evidence = proved(&bundle);
    if let Inst::Select {
        then_val, else_val, ..
    } = &mut bundle.module.functions[1].blocks[0].body[0].inst
    {
        std::mem::swap(then_val, else_val);
    }
    refresh_native_bundle_module_identity(&mut bundle);
    valid(&bundle);
    assert_ne!(
        verify_trust_ir_body_contracts(&bundle).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
    assert!(replay_trust_ir_body_contracts(&bundle, &evidence).is_err());
}

#[test]
fn unsigned_select_expansion_keeps_the_formula_budget() {
    let mut bundle = question(Ty::U64, Shape::Select, false);
    let block = &mut bundle.module.functions[0].blocks[0];
    block.body.pop();
    let mut previous = ValueId::new(3);
    for next in 4..40 {
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::U64,
                cond: ValueId::new(0),
                then_val: previous,
                else_val: ValueId::new(2),
            })
            .with_result(ValueId::new(next)),
        );
        previous = ValueId::new(next);
    }
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![previous],
    }));
    refresh_native_bundle_module_identity(&mut bundle);
    valid(&bundle);
    let error = verify_trust_ir_body_contracts(&bundle)
        .unwrap_err()
        .to_string();
    assert!(error.contains("formula budget"), "{error}");
}
