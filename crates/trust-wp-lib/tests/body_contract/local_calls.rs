//! Original compiler inputs stay immutable; mutations below are separate questions.
use trust_wp_lib::trust_ir_body::trust_ir_native_bundle_to_body_verify_requests;

use super::*;

const INT_WIDTH: &str = include_str!("fixtures/local_calls/width_is_supported.json");
const WIDTH: &str = include_str!("fixtures/local_calls/width_supported.json");
const CONVERSION: &str = include_str!("fixtures/local_calls/conversion_code.json");

fn captured(text: &str) -> NativeVerificationBundle {
    let bundle: NativeVerificationBundle = serde_json::from_str(text).unwrap();
    bundle.validate().unwrap();
    assert_eq!(bundle.module.stable_digest(), bundle.trust_ir_module_digest);
    bundle
}

fn checked(bundle: &NativeVerificationBundle) -> Vec<trust_wp_lib::VerifyBundleResult> {
    let immutable = bundle.clone();
    let results = verify_trust_ir_body_contracts(bundle).unwrap();
    assert_ne!(results, []);
    assert!(
        results
            .iter()
            .all(|r| r.status == VerifyBundleStatus::Verified),
        "{results:#?}"
    );
    let bytes = serde_json::to_vec(&results).unwrap();
    let restored: Vec<trust_wp_lib::VerifyBundleResult> = serde_json::from_slice(&bytes).unwrap();
    replay_trust_ir_body_contracts(bundle, &restored).unwrap();
    assert_eq!(*bundle, immutable);
    assert!(bundle
        .module
        .proof_obligations
        .iter()
        .all(|p| p.status == ProofStatus::Pending));
    results
}

#[test]
fn original_local_call_postconditions_prove_and_replay() {
    for text in [INT_WIDTH, WIDTH, CONVERSION] {
        let bundle = captured(text);
        assert!(
            trust_ir_native_bundle_to_verify_requests(&bundle).is_err(),
            "formula-only replay must still refuse machine-width bindings"
        );
        let results = checked(&bundle);
        assert_eq!(results.len(), 1);
    }
}

#[test]
fn original_local_calls_agree_with_shared_reference_execution() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    for (text, integer_width) in [(INT_WIDTH, true), (WIDTH, false)] {
        let bundle = captured(text);
        for width in [0, 1, 7, 8, 16, 32, 63, 64, 65, 128, 129, u32::MAX] {
            let result = Interpreter::with_module(&bundle.module)
                .execute_func(
                    FuncId::new(0),
                    [InterpretValue::int(Ty::U32, i128::from(width)).unwrap()],
                )
                .unwrap();
            let expected = if integer_width {
                (1..=64).contains(&width)
            } else {
                [8, 16, 32, 64, 128].contains(&width)
            };
            assert_eq!(
                result.returns,
                vec![InterpretValue::int(Ty::U8, i128::from(u8::from(expected))).unwrap()]
            );
        }
    }
    let bundle = captured(CONVERSION);
    for src in [0, 8, 16, 32, 64, 128, u32::MAX] {
        for dst in [0, 8, 16, 32, 64, 128, u32::MAX] {
            for source_signed in [0, 1, 2, 255] {
                for dest_signed in [0, 1, 2, 255] {
                    let result = Interpreter::with_module(&bundle.module)
                        .execute_func(
                            FuncId::new(0),
                            [
                                InterpretValue::int(Ty::U32, i128::from(src)).unwrap(),
                                InterpretValue::int(Ty::U8, i128::from(source_signed)).unwrap(),
                                InterpretValue::int(Ty::U32, i128::from(dst)).unwrap(),
                                InterpretValue::int(Ty::U8, i128::from(dest_signed)).unwrap(),
                            ],
                        )
                        .unwrap();
                    let expected = if ![8, 16, 32, 64, 128].contains(&src)
                        || ![8, 16, 32, 64, 128].contains(&dst)
                        || source_signed > 1
                        || dest_signed > 1
                    {
                        0
                    } else if src == dst {
                        u8::from(source_signed == dest_signed)
                    } else if dst < src {
                        0
                    } else if source_signed == 0 {
                        2
                    } else if dest_signed == 1 {
                        3
                    } else {
                        0
                    };
                    assert_eq!(
                        result.returns,
                        vec![InterpretValue::int(Ty::U8, i128::from(expected)).unwrap()]
                    );
                }
            }
        }
    }
}

#[test]
fn callee_instructions_and_false_assumes_cannot_be_replaced_by_summaries() {
    let original = captured(INT_WIDTH);
    let accepted = checked(&original);
    for false_assume in [false, true] {
        let mut changed = original.clone();
        let callee = &mut changed.module.functions[1];
        let mut summary = trust_ir::FunctionSummary::new();
        summary.params = vec!["width".into()];
        summary
            .ensures
            .push(ProofFormula::new("trust-wp.pure-expr.v1", "false"));
        callee.summary = Some(summary);
        if false_assume {
            callee.blocks[0].body.splice(
                0..0,
                [
                    InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    })
                    .with_result(ValueId::new(900)),
                    InstrNode::new(Inst::Assume {
                        cond: ValueId::new(900),
                    }),
                ],
            );
        } else {
            let value = callee
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find_map(|n| match &mut n.inst {
                    Inst::Const {
                        ty: Ty::U8,
                        value: Constant::Int(value),
                    } if *value == 1 => Some(value),
                    _ => None,
                })
                .unwrap();
            *value = 200;
        }
        refresh_native_bundle_module_identity(&mut changed);
        let results = verify_trust_ir_body_contracts(&changed).unwrap();
        assert!(
            results
                .iter()
                .all(|r| r.status != VerifyBundleStatus::Verified),
            "{results:#?}"
        );
        assert!(replay_trust_ir_body_contracts(&changed, &accepted).is_err());
    }
}

fn double_negation(contract: &str) -> NativeVerificationBundle {
    let mut bundle = boolean_function(contract, false);
    let mut callee = bundle.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "local_negation".into();
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
    callee.blocks = vec![entry, yes, no];
    bundle.module.try_add_function(callee).unwrap();
    let mut wrapper = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    for (input, output) in [(0, 1), (1, 2)] {
        wrapper.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(input)],
            })
            .with_result(ValueId::new(output)),
        );
    }
    wrapper.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    bundle.module.functions[0].blocks = vec![wrapper];
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

#[test]
fn repeated_calls_multiple_returns_and_colliding_ssa_ids_compose() {
    let bundle = double_negation("(r : bool) == (x : bool)");
    let accepted = checked(&bundle);
    assert_reference_returns(&bundle, |x| x);
    let mut changed = bundle.clone();
    match &mut changed.module.functions[0].blocks[0].body[1].inst {
        Inst::Call { args, .. } => args[0] = ValueId::new(0),
        _ => unreachable!(),
    }
    refresh_native_bundle_module_identity(&mut changed);
    let results = verify_trust_ir_body_contracts(&changed).unwrap();
    assert_ne!(results[0].status, VerifyBundleStatus::Verified);
    assert!(replay_trust_ir_body_contracts(&changed, &accepted).is_err());
    let false_claim = double_negation("(r : bool) != (x : bool)");
    assert_ne!(
        verify_trust_ir_body_contracts(&false_claim).unwrap()[0].status,
        VerifyBundleStatus::Verified
    );
}

#[test]
fn callee_formals_are_substituted_simultaneously_without_name_capture() {
    let mut formula = ProofFormula::new(
        "trust-wp.pure-expr.v1",
        "(r : bool) == (y : bool) && ((x : bool) == (x : bool))",
    );
    formula.bindings = [
        ("x", ClausePlace::Param { index: 0 }),
        ("y", ClausePlace::Param { index: 1 }),
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
        vec![Ty::Bool, Ty::Bool],
        vec![Ty::Bool],
    );
    bundle.compiler_facts.casts.clear();
    for source in &mut bundle.compiler_facts.obligation_sources {
        source
            .facts
            .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));
    }
    let mut wrapper = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), Ty::Bool)
        .with_param(ValueId::new(1), Ty::Bool);
    wrapper.body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(1), ValueId::new(0)],
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }),
    ];
    bundle.module.functions[0].blocks = vec![wrapper];
    let mut callee = bundle.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "first_argument".into();
    callee.blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    })];
    bundle.module.try_add_function(callee).unwrap();
    refresh_native_bundle_module_identity(&mut bundle);
    checked(&bundle);
    for x in [false, true] {
        for y in [false, true] {
            use trust_ir::interpret::{InterpretValue, Interpreter};
            let result = Interpreter::with_module(&bundle.module)
                .execute_func(
                    FuncId::new(0),
                    [InterpretValue::bool(x), InterpretValue::bool(y)],
                )
                .unwrap();
            assert_eq!(result.returns, vec![InterpretValue::bool(y)]);
        }
    }
}

#[test]
fn recursive_missing_preconditioned_and_effectful_callees_refuse() {
    let original = captured(INT_WIDTH);
    for change in 0..6 {
        let mut bundle = original.clone();
        let callee = &mut bundle.module.functions[1];
        match change {
            0 => {
                callee.blocks =
                    vec![Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U32)];
                callee.blocks[0].body = vec![
                    InstrNode::new(Inst::Call {
                        callee: FuncId::new(1),
                        args: vec![ValueId::new(0)],
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(1)],
                    }),
                ];
            }
            1 => callee.blocks.clear(),
            2 => {
                let mut summary = trust_ir::FunctionSummary::new();
                summary.params = vec!["width".into()];
                summary
                    .requires
                    .push(ProofFormula::new("trust-wp.pure-expr.v1", "false"));
                callee.summary = Some(summary);
            }
            3 => callee.attrs.readonly = true,
            4 => {
                let id = callee
                    .blocks
                    .iter()
                    .flat_map(|b| &b.body)
                    .find_map(|n| match n.inst {
                        Inst::Load { ptr, .. } => Some(ptr),
                        _ => None,
                    })
                    .unwrap();
                for b in &mut callee.blocks {
                    b.body
                        .retain(|n| !matches!(n.inst, Inst::Store { ptr, .. } if ptr == id));
                }
            }
            5 => {
                let mut summary = trust_ir::FunctionSummary::new();
                summary.params = vec!["width".into()];
                summary.effects = Some(trust_ir::effects::EffectSummary::pure());
                callee.summary = Some(summary);
            }
            _ => unreachable!(),
        }
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(
            trust_ir_native_bundle_to_body_verify_requests(&bundle).is_err(),
            "change {change}"
        );
    }
}

#[test]
fn unsigned_byte_input_domain_is_complete_and_never_narrowed() {
    for (claim, valid) in [("r == x && r <= 255", true), ("r == x && r < 255", false)] {
        let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", claim);
        formula.bindings = [
            ("x", ClausePlace::Param { index: 0 }),
            ("r", ClausePlace::ResultSlot { index: 0 }),
        ]
        .into_iter()
        .map(|(name, place)| {
            (
                name.into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(8),
                    place,
                },
            )
        })
        .collect();
        let mut bundle = native_bundle_with_signature(
            formula,
            TrustWpVerificationMode::WeakestPrecondition,
            vec![Ty::U8],
            vec![Ty::U8],
        );
        bundle.compiler_facts.casts.clear();
        for source in &mut bundle.compiler_facts.obligation_sources {
            source
                .facts
                .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));
        }
        let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U8);
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        bundle.module.functions[0].blocks = vec![entry];
        refresh_native_bundle_module_identity(&mut bundle);
        let results = verify_trust_ir_body_contracts(&bundle).unwrap();
        assert_eq!(
            results[0].status == VerifyBundleStatus::Verified,
            valid,
            "{results:#?}"
        );
        assert_eq!(
            replay_trust_ir_body_contracts(&bundle, &results).is_ok(),
            valid
        );
        for x in 0..=255 {
            use trust_ir::interpret::{InterpretValue, Interpreter};
            let value = InterpretValue::int(Ty::U8, x).unwrap();
            assert_eq!(
                Interpreter::with_module(&bundle.module)
                    .execute_func(FuncId::new(0), [value.clone()])
                    .unwrap()
                    .returns,
                vec![value]
            );
        }
    }
}

#[test]
fn unsigned_byte_domains_and_literals_keep_exact_machine_bounds() {
    let original = captured(INT_WIDTH);
    for value in [-1, 256] {
        let mut changed = original.clone();
        let literal = changed.module.functions[1]
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.body)
            .find_map(|n| match &mut n.inst {
                Inst::Const {
                    ty: Ty::U8,
                    value: Constant::Int(v),
                } => Some(v),
                _ => None,
            })
            .unwrap();
        *literal = value;
        refresh_native_bundle_module_identity(&mut changed);
        assert!(trust_ir_native_bundle_to_body_verify_requests(&changed).is_err());
    }
    let mut changed = original;
    changed.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings[0]
        .1
        .sort = ClauseSort::BitVec(16);
    refresh_native_bundle_module_identity(&mut changed);
    assert!(trust_ir_native_bundle_to_body_verify_requests(&changed).is_err());
}
