use super::*;

fn captured(name: &str) -> NativeVerificationBundle {
    let (_, text) = CAPTURES
        .iter()
        .find(|(candidate, _)| *candidate == name)
        .unwrap();
    derived_v9_capture(text)
}

fn checked(bundle: &NativeVerificationBundle) -> Vec<trust_wp_lib::VerifyBundleResult> {
    let result = verify_trust_ir_body_contracts(bundle).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].status,
        VerifyBundleStatus::Verified,
        "{result:#?}"
    );
    let bytes = serde_json::to_vec(&result).unwrap();
    let restored: Vec<trust_wp_lib::VerifyBundleResult> = serde_json::from_slice(&bytes).unwrap();
    replay_trust_ir_body_contracts(bundle, &restored).unwrap();
    result
}

fn word_question(upper: u64, constant: Option<u64>) -> NativeVerificationBundle {
    let mut formula = ProofFormula::new(
        TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        serde_json::json!({
            "schema":TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            "variables":[{"name":"r","sort":"int"}],
            "body":{"op":"le","lhs":{"var":"r"},"rhs":{"int":upper}}
        })
        .to_string(),
    );
    formula.bindings = vec![(
        "r".into(),
        ClauseBinding {
            sort: ClauseSort::BitVec(64),
            place: ClausePlace::ResultSlot { index: 0 },
        },
    )];
    let mut bundle = native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        if constant.is_some() {
            vec![]
        } else {
            vec![Ty::U64]
        },
        vec![Ty::U64],
    );
    bundle.compiler_facts.casts.clear();
    for source in &mut bundle.compiler_facts.obligation_sources {
        source
            .facts
            .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));
    }
    let mut block = Block::new(BlockId::new(0));
    if let Some(value) = constant {
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(value)),
            })
            .with_result(ValueId::new(0)),
        );
    } else {
        block.params.push((ValueId::new(0), Ty::U64));
    }
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    bundle.module.functions[0].blocks = vec![block];
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

#[test]
fn full_unsigned_domain_includes_the_entire_upper_half() {
    let complete = word_question(u64::MAX, None);
    checked(&complete);
    let narrowed_claim = word_question(u64::try_from(i64::MAX).unwrap(), None);
    let result = verify_trust_ir_body_contracts(&narrowed_claim).unwrap();
    assert_ne!(result[0].status, VerifyBundleStatus::Verified);
    assert!(replay_trust_ir_body_contracts(&narrowed_claim, &result).is_err());
    use trust_ir::interpret::{InterpretValue, Interpreter};
    for value in [
        0,
        1,
        (1_u64 << 63) - 1,
        1_u64 << 63,
        (1_u64 << 63) + 1,
        u64::MAX,
    ] {
        let input = InterpretValue::int(Ty::U64, i128::from(value)).unwrap();
        assert_eq!(
            Interpreter::with_module(&complete.module)
                .execute_func(FuncId::new(0), [input.clone()])
                .unwrap()
                .returns,
            vec![input]
        );
        checked(&word_question(value, Some(value)));
    }
    let false_constant = word_question(u64::try_from(i64::MAX).unwrap(), Some(u64::MAX));
    let result = verify_trust_ir_body_contracts(&false_constant).unwrap();
    assert_eq!(result[0].status, VerifyBundleStatus::Failed, "{result:#?}");
    assert!(replay_trust_ir_body_contracts(&false_constant, &result).is_err());
}

#[test]
fn original_full_width_programs_match_an_independent_unsigned_oracle() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    let values = [
        0,
        1,
        127,
        128,
        255,
        256,
        u64::from(u32::MAX),
        1_u64 << 32,
        (1_u64 << 63) - 1,
        1_u64 << 63,
        (1_u64 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    for (name, text) in CAPTURES {
        let bundle = derived_v9_capture(text);
        for width in [0, 1, 2, 8, 16, 31, 32, 33, 63, 64, 65, 128, u32::MAX] {
            let supported = (1..=64).contains(&width);
            let max_unsigned = if supported {
                u64::try_from((1_u128 << width) - 1).unwrap()
            } else {
                u64::MAX
            };
            let max_signed = if supported {
                u64::try_from((1_u128 << (width - 1)) - 1).unwrap()
            } else {
                u64::try_from(i64::MAX).unwrap()
            };
            let max_magnitude = if supported {
                u64::try_from(1_u128 << (width - 1)).unwrap()
            } else {
                1_u64 << 63
            };
            if matches!(*name, "signed_max" | "signed_min_magnitude") {
                let expected = if *name == "signed_max" {
                    max_signed
                } else {
                    max_magnitude
                };
                let result = Interpreter::with_module(&bundle.module)
                    .execute_func(
                        FuncId::new(0),
                        [InterpretValue::int(Ty::U32, i128::from(width)).unwrap()],
                    )
                    .unwrap();
                assert_eq!(
                    result.returns,
                    vec![InterpretValue::int(Ty::U64, i128::from(expected)).unwrap()]
                );
            } else {
                for value in values {
                    let (result_ty, expected) = match *name {
                        "clamp_unsigned_to_width" => (Ty::U64, value.min(max_unsigned)),
                        "unsigned_fits" => (Ty::U8, u64::from(supported && value <= max_unsigned)),
                        "signed_fits_nonneg" => {
                            (Ty::U8, u64::from(supported && value <= max_signed))
                        }
                        "signed_fits_magnitude" => {
                            (Ty::U8, u64::from(supported && value <= max_magnitude))
                        }
                        _ => unreachable!(),
                    };
                    let result = Interpreter::with_module(&bundle.module)
                        .execute_func(
                            FuncId::new(0),
                            [
                                InterpretValue::int(Ty::U64, i128::from(value)).unwrap(),
                                InterpretValue::int(Ty::U32, i128::from(width)).unwrap(),
                            ],
                        )
                        .unwrap();
                    assert_eq!(
                        result.returns,
                        vec![InterpretValue::int(result_ty, i128::from(expected)).unwrap()],
                        "{name}({value}, {width})"
                    );
                }
            }
        }
    }
}

#[test]
fn changed_wide_callee_or_false_assume_cannot_replay_the_original_proof() {
    let original = captured("signed_max");
    let accepted = checked(&original);
    for assume in [false, true] {
        let mut changed = original.clone();
        let nodes = &mut changed.module.functions[1].blocks;
        if assume {
            let false_value = nodes[0]
                .body
                .iter()
                .find_map(|n| match n.inst {
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    } => n.results.first().copied(),
                    _ => None,
                })
                .unwrap();
            for node in &mut nodes[0].body {
                if let Inst::Assume { cond } = &mut node.inst {
                    *cond = false_value;
                    break;
                }
            }
        } else {
            let value = nodes
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find_map(|n| match &mut n.inst {
                    Inst::Const {
                        ty: Ty::U64,
                        value: Constant::Int(v),
                    } if *v == i128::from(i64::MAX) => Some(v),
                    _ => None,
                })
                .unwrap();
            *value = i128::from(u64::MAX);
        }
        refresh_native_bundle_module_identity(&mut changed);
        let result = verify_trust_ir_body_contracts(&changed).unwrap();
        assert_ne!(
            result[0].status,
            VerifyBundleStatus::Verified,
            "{result:#?}"
        );
        assert!(replay_trust_ir_body_contracts(&changed, &accepted).is_err());
    }
}

#[test]
fn wide_constants_and_bindings_cannot_wrap_or_lose_width() {
    for value in [-1, i128::from(u64::MAX) + 1] {
        let mut bundle = word_question(u64::MAX, Some(0));
        bundle.module.functions[0].blocks[0].body[0].inst = Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(value),
        };
        refresh_native_bundle_module_identity(&mut bundle);
        assert!(verify_trust_ir_body_contracts(&bundle).is_err());
    }
    let mut bundle = word_question(u64::MAX, None);
    bundle.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings[0]
        .1
        .sort = ClauseSort::BitVec(63);
    refresh_native_bundle_module_identity(&mut bundle);
    assert!(verify_trust_ir_body_contracts(&bundle).is_err());
}

fn branch_chain(count: u32) -> NativeVerificationBundle {
    let mut bundle = word_question(u64::MAX, None);
    let mut blocks = Vec::new();
    for index in 0..count {
        let mut block = Block::new(BlockId::new(index));
        if index == 0 {
            block.params.push((ValueId::new(0), Ty::U64));
        }
        block.body.push(InstrNode::new(if index + 1 == count {
            Inst::Return {
                values: vec![ValueId::new(0)],
            }
        } else {
            Inst::Br {
                target: BlockId::new(index + 1),
                args: vec![],
            }
        }));
        blocks.push(block);
    }
    bundle.module.functions[0].blocks = blocks;
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

#[test]
fn bounded_block_admission_keeps_the_next_block_refused() {
    checked(&branch_chain(256));
    let error = verify_trust_ir_body_contracts(&branch_chain(257))
        .unwrap_err()
        .to_string();
    assert!(error.contains("resource limits"), "{error}");
}

#[test]
fn local_calls_still_share_one_expansion_budget() {
    let mut bundle = branch_chain(256);
    let mut callee = bundle.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "long_identity".into();
    bundle.module.try_add_function(callee).unwrap();
    let mut wrapper = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    for index in 1..=17 {
        wrapper.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(index - 1)],
            })
            .with_result(ValueId::new(index)),
        );
    }
    wrapper.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(17)],
    }));
    bundle.module.functions[0].blocks = vec![wrapper];
    refresh_native_bundle_module_identity(&mut bundle);
    bundle.validate().unwrap();
    let error = verify_trust_ir_body_contracts(&bundle)
        .unwrap_err()
        .to_string();
    assert!(error.contains("work budget"), "{error}");
}

#[test]
fn executed_assertions_and_dead_division_keep_their_safety_obligations() {
    for assertion in [false, true] {
        let mut bundle = word_question(u64::MAX, None);
        let block = &mut bundle.module.functions[0].blocks[0];
        if assertion {
            block.body.splice(
                0..0,
                [
                    InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(true),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Assert {
                        cond: ValueId::new(1),
                        kind: trust_ir::AssertKind::Unspecified,
                        site: None,
                    }),
                ],
            );
        } else {
            block.body.insert(
                0,
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::UDiv,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(1)),
            );
        }
        refresh_native_bundle_module_identity(&mut bundle);
        bundle.validate().unwrap();
        let results = verify_trust_ir_body_contracts(&bundle).unwrap();
        assert_eq!(results.len(), 1);
        if assertion {
            assert_eq!(
                results[0].status,
                VerifyBundleStatus::Verified,
                "{results:#?}"
            );
            replay_trust_ir_body_contracts(&bundle, &results).unwrap();
        } else {
            assert_eq!(
                results[0].status,
                VerifyBundleStatus::Failed,
                "{results:#?}"
            );
            assert!(format!("{:?}", results[0].obligation_results)
                .contains("checked whole-predicate counterexample"));
            assert!(replay_trust_ir_body_contracts(&bundle, &results).is_err());
        }
    }
}

#[test]
fn deeper_claims_keep_nesting_duplicates_and_payload_limits() {
    use trust_wp_core::verify_bundle::decode_trust_formula_v1_claim;
    for (depth, duplicate) in [(240, false), (240, true), (270, false)] {
        let mut bundle = word_question(u64::MAX, None);
        let formula = bundle.module.proof_obligations[0].formula.as_mut().unwrap();
        let mut body = if duplicate {
            format!("{{\"op\":\"le\",\"lhs\":{{\"var\":\"r\"}},\"rhs\":{{\"int\":0}},\"rhs\":{{\"int\":{}}}}}", u64::MAX)
        } else {
            serde_json::from_str::<serde_json::Value>(&formula.payload).unwrap()["body"].to_string()
        };
        for _ in 0..depth {
            body = format!("{{\"op\":\"not\",\"expr\":{body}}}");
        }
        formula.payload = format!("{{\"schema\":\"{}\",\"variables\":[{{\"name\":\"r\",\"sort\":\"int\"}}],\"body\":{body}}}", TRUST_FORMULA_CLAIM_SCHEMA_VERSION);
        if duplicate {
            assert!(decode_trust_formula_v1_claim(&formula.payload)
                .unwrap_err()
                .to_string()
                .contains("duplicate JSON object key"));
        }
        refresh_native_bundle_module_identity(&mut bundle);
        if depth == 240 && !duplicate {
            checked(&bundle);
        } else {
            assert!(verify_trust_ir_body_contracts(&bundle).is_err());
        }
    }
    let mut oversized = word_question(u64::MAX, None);
    oversized.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .payload
        .push_str(&" ".repeat(262_145));
    refresh_native_bundle_module_identity(&mut oversized);
    let error = verify_trust_ir_body_contracts(&oversized)
        .unwrap_err()
        .to_string();
    assert!(error.contains("payload budget"), "{error}");
}
