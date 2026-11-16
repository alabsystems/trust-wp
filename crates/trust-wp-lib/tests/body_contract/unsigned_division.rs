//! Original compiler questions retain their full caller/callee and sibling inventory.
use trust_ir::{
    interpret::{InterpretValue, Interpreter},
    ValidatedNativeBundle,
};
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_request_validated, verify_trust_ir_body_request_validated,
    NativeBodyWpTranslationCoverage,
};

use super::*;

const CAPTURES: &[(&str, &str, usize)] = &[
    (
        "megabytes_of",
        include_str!("fixtures/budget/megabytes_of.json"),
        2,
    ),
    (
        "per_job_bytes",
        include_str!("fixtures/budget/per_job_bytes.json"),
        1,
    ),
    (
        "split_budget_ms",
        include_str!("fixtures/budget/split_budget_ms.json"),
        2,
    ),
];

fn wp_ids(bundle: &NativeVerificationBundle) -> Vec<NativeRequestId> {
    bundle
        .requests
        .iter()
        .filter_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request.id),
            _ => None,
        })
        .collect()
}

fn checked(
    bundle: &NativeVerificationBundle,
) -> trust_wp_lib::trust_ir_body::NativeBodyWpVerification {
    let admitted = ValidatedNativeBundle::new(bundle).unwrap();
    let id = wp_ids(bundle)[0];
    let result = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
    assert_eq!(
        result.result().status,
        VerifyBundleStatus::Verified,
        "{:?}",
        result.result()
    );
    replay_trust_ir_body_request_validated(&admitted, id, result.result(), Some(result.witness()))
        .unwrap();
    result
}

fn failed(bundle: &NativeVerificationBundle) {
    let admitted = ValidatedNativeBundle::new(bundle).unwrap();
    let result = verify_trust_ir_body_request_validated(&admitted, wp_ids(bundle)[0]).unwrap();
    assert_eq!(
        result.result().status,
        VerifyBundleStatus::Failed,
        "{result:#?}"
    );
    assert!(replay_trust_ir_body_request_validated(
        &admitted,
        wp_ids(bundle)[0],
        result.result(),
        Some(result.witness())
    )
    .is_err());
}

#[test]
fn original_budget_callers_prove_all_five_contracts_and_independently_replay() {
    let mut failures = Vec::new();
    for (name, text, count) in CAPTURES {
        let bundle: NativeVerificationBundle = serde_json::from_str(text).unwrap();
        let before = bundle.clone();
        let original_bytes = trust_ir::binary::serialize_module(&bundle.module).unwrap();
        let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
        let ids = wp_ids(&bundle);
        assert_eq!(ids.len(), *count, "{name}");
        for id in ids {
            let result = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
            if result.result().status != VerifyBundleStatus::Verified {
                failures.push(format!("{name} request {id:?}: {:?}", result.result()));
                continue;
            }
            assert_eq!(
                result.witness().native_bundle_digest,
                bundle.stable_digest()
            );
            assert_eq!(
                result.witness().module_digest,
                bundle.module.stable_digest()
            );
            assert!(matches!(
                result.witness().coverage,
                NativeBodyWpTranslationCoverage::Untranslated { .. }
            ));
            replay_trust_ir_body_request_validated(
                &admitted,
                id,
                result.result(),
                Some(result.witness()),
            )
            .unwrap();
        }
        assert_eq!(bundle, before);
        assert_eq!(
            trust_ir::binary::serialize_module(&bundle.module).unwrap(),
            original_bytes
        );
        for args in [
            vec![0, 0],
            vec![1, 1],
            vec![u64::MAX, 1],
            vec![u64::MAX, u64::MAX],
        ] {
            let arity = bundle.module.func_types[0].params.len();
            let values: Vec<_> = args[..arity]
                .iter()
                .map(|x| InterpretValue::int(Ty::U64, i128::from(*x)).unwrap())
                .collect();
            Interpreter::with_module(&bundle.module)
                .execute_func(FuncId::new(0), values)
                .unwrap();
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[derive(Clone, Copy)]
enum Shape {
    Unit,
    ZeroDead,
    FalseAssert,
    AssertDivisor,
    Guarded,
    WrongGuard,
}

fn question(ty: Ty, shape: Shape) -> NativeVerificationBundle {
    let width = match ty {
        Ty::U8 => 8,
        Ty::U32 => 32,
        Ty::U64 => 64,
        _ => panic!(),
    };
    let mut formula = ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, serde_json::json!({
        "schema":TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
        "variables":[{"name":"r","sort":"int"},{"name":"x","sort":"int"}],
        "body":{"op":if matches!(shape, Shape::Guarded | Shape::WrongGuard | Shape::AssertDivisor) {"le"} else {"eq"},"lhs":{"var":"r"},"rhs":{"var":"x"}}
    }).to_string());
    formula.bindings = vec![
        (
            "r".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(width),
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
        (
            "x".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(width),
                place: ClausePlace::Param { index: 0 },
            },
        ),
    ];
    let mut bundle = native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::WeakestPrecondition,
        vec![ty.clone(), ty.clone()],
        vec![ty.clone()],
    );
    bundle.compiler_facts.casts.clear();
    for source in &mut bundle.compiler_facts.obligation_sources {
        source
            .facts
            .retain(|x| !matches!(x, NativeCompilerFactRef::Cast(_)));
    }
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), ty.clone())
        .with_param(ValueId::new(1), ty.clone());
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(
        InstrNode::new(Inst::ICmp {
            op: trust_ir::ICmpOp::Ne,
            ty: ty.clone(),
            lhs: if matches!(shape, Shape::WrongGuard) {
                ValueId::new(0)
            } else {
                ValueId::new(1)
            },
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(4)),
    );
    if matches!(shape, Shape::Guarded | Shape::WrongGuard) {
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(4),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));
        let mut divide = Block::new(BlockId::new(1));
        divide.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::UDiv,
                ty: ty.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(5)),
        );
        divide.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(5)],
        }));
        let mut bypass = Block::new(BlockId::new(2));
        bypass.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        bundle.module.functions[0].blocks = vec![entry, divide, bypass];
    } else {
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(!matches!(shape, Shape::FalseAssert)),
            })
            .with_result(ValueId::new(6)),
        );
        entry.body.push(InstrNode::new(Inst::Assert {
            cond: if matches!(shape, Shape::AssertDivisor) {
                ValueId::new(4)
            } else {
                ValueId::new(6)
            },
            kind: trust_ir::AssertKind::DivByZero,
            site: None,
        }));
        entry.body.last_mut().unwrap().proofs = vec![trust_ir::ProofAnnotation::DivNonZero];
        let rhs = match shape {
            Shape::ZeroDead => ValueId::new(2),
            Shape::AssertDivisor => ValueId::new(1),
            _ => ValueId::new(3),
        };
        entry.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::UDiv,
                ty,
                lhs: ValueId::new(0),
                rhs,
            })
            .with_result(ValueId::new(5)),
        );
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![if matches!(shape, Shape::ZeroDead) {
                ValueId::new(0)
            } else {
                ValueId::new(5)
            }],
        }));
        bundle.module.functions[0].blocks = vec![entry];
    }
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

#[test]
fn bounded_unsigned_quotients_agree_with_canonical_execution_including_full_u64() {
    for ty in [Ty::U8, Ty::U32, Ty::U64] {
        checked(&question(ty.clone(), Shape::Unit));
        let guarded = question(ty.clone(), Shape::Guarded);
        checked(&guarded);
        let max = match ty {
            Ty::U8 => u64::from(u8::MAX),
            Ty::U32 => u64::from(u32::MAX),
            _ => u64::MAX,
        };
        for (x, y) in [(0, 0), (1, 0), (max, 1), (max, 2), (max, max)] {
            let out = Interpreter::with_module(&guarded.module)
                .execute_func(
                    FuncId::new(0),
                    [
                        InterpretValue::int(ty.clone(), i128::from(x)).unwrap(),
                        InterpretValue::int(ty.clone(), i128::from(y)).unwrap(),
                    ],
                )
                .unwrap();
            assert_eq!(
                out.returns,
                vec![
                    InterpretValue::int(ty.clone(), i128::from(if y == 0 { x } else { x / y }))
                        .unwrap()
                ]
            );
        }
    }
}

#[test]
fn false_assertions_and_zero_divisors_remain_owed_even_for_dead_quotients() {
    for shape in [
        Shape::ZeroDead,
        Shape::FalseAssert,
        Shape::AssertDivisor,
        Shape::WrongGuard,
    ] {
        let bundle = question(Ty::U64, shape);
        failed(&bundle);
        let y = if matches!(shape, Shape::FalseAssert) {
            1
        } else {
            0
        };
        assert!(Interpreter::with_module(&bundle.module)
            .execute_func(
                FuncId::new(0),
                [
                    InterpretValue::int(Ty::U64, 1).unwrap(),
                    InterpretValue::int(Ty::U64, y).unwrap()
                ]
            )
            .is_err());
    }
}

#[test]
fn division_labels_never_admit_other_proof_premises_or_signed_division() {
    let mut annotated = question(Ty::U64, Shape::Unit);
    let assertion = annotated.module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Assert { .. }))
        .unwrap();
    assertion.proofs.push(trust_ir::ProofAnnotation::NoOverflow);
    refresh_native_bundle_module_identity(&mut annotated);
    let admitted = ValidatedNativeBundle::new(&annotated).unwrap();
    let error = verify_trust_ir_body_request_validated(&admitted, wp_ids(&annotated)[0])
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("instruction proof annotations are not premises"),
        "{error}"
    );

    let mut signed = question(Ty::U64, Shape::Unit);
    let divide = signed.module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::BinOp { .. }))
        .unwrap();
    let Inst::BinOp { op, .. } = &mut divide.inst else {
        unreachable!()
    };
    *op = trust_ir::BinOp::SDiv;
    refresh_native_bundle_module_identity(&mut signed);
    let admitted = ValidatedNativeBundle::new(&signed).unwrap();
    let error = verify_trust_ir_body_request_validated(&admitted, wp_ids(&signed)[0])
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("instruction outside scalar WP fragment"),
        "{error}"
    );
}

#[test]
fn changed_return_binding_or_guard_cannot_reuse_original_quotient_evidence() {
    let original = question(Ty::U64, Shape::Guarded);
    let evidence = checked(&original);
    let mut wrong_return = original.clone();
    wrong_return.module.functions[0].blocks[1].body[1].inst = Inst::Return {
        values: vec![ValueId::new(1)],
    };
    let mut wrong_binding = original.clone();
    wrong_binding.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings[0]
        .1
        .place = ClausePlace::Param { index: 1 };
    let mut false_goal = original.clone();
    false_goal.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .payload = false_goal.module.proof_obligations[0]
        .formula
        .as_ref()
        .unwrap()
        .payload
        .replace("\"le\"", "\"gt\"");
    for mut changed in [
        wrong_return,
        wrong_binding,
        false_goal,
        question(Ty::U64, Shape::WrongGuard),
    ] {
        refresh_native_bundle_module_identity(&mut changed);
        failed(&changed);
        let admitted = ValidatedNativeBundle::new(&changed).unwrap();
        assert!(replay_trust_ir_body_request_validated(
            &admitted,
            wp_ids(&changed)[0],
            evidence.result(),
            Some(evidence.witness())
        )
        .is_err());
    }
}

#[test]
fn original_callee_divisor_mutation_is_checked_without_dropping_siblings() {
    let mut bundle: NativeVerificationBundle = serde_json::from_str(CAPTURES[2].1).unwrap();
    let original = bundle.clone();
    let evidence = checked(&original);
    let callee = bundle.module.function_by_id_mut(FuncId::new(1)).unwrap();
    let node = callee.blocks[3]
        .body
        .iter_mut()
        .find(|n| {
            matches!(
                n.inst,
                Inst::BinOp {
                    op: trust_ir::BinOp::UDiv,
                    ..
                }
            )
        })
        .unwrap();
    let Inst::BinOp { rhs, .. } = &mut node.inst else {
        unreachable!()
    };
    *rhs = ValueId::new(24);
    refresh_native_bundle_module_identity(&mut bundle);
    assert_eq!(bundle.requests, original.requests);
    assert!(Interpreter::with_module(&bundle.module)
        .execute_func(
            FuncId::new(0),
            [
                InterpretValue::int(Ty::U64, 1).unwrap(),
                InterpretValue::int(Ty::U64, 1).unwrap()
            ]
        )
        .is_err());
    failed(&bundle);
    let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
    assert!(replay_trust_ir_body_request_validated(
        &admitted,
        wp_ids(&bundle)[0],
        evidence.result(),
        Some(evidence.witness())
    )
    .is_err());
}

#[test]
fn original_contract_division_keeps_its_definedness_and_euclidean_meaning() {
    let clause = |body: serde_json::Value| {
        let mut bundle = question(Ty::U64, Shape::Unit);
        let formula = bundle.module.proof_obligations[0].formula.as_mut().unwrap();
        formula.bindings.clear();
        formula.payload = serde_json::json!({
            "schema":TRUST_FORMULA_CLAIM_SCHEMA_VERSION,"variables":[],"body":body
        })
        .to_string();
        refresh_native_bundle_module_identity(&mut bundle);
        bundle
    };
    for denominator in [serde_json::json!({"int":0}), serde_json::json!({"var":"x"})] {
        let div = serde_json::json!({"op":"div","lhs":{"var":"x"},"rhs":denominator});
        let mut bundle = question(Ty::U64, Shape::Unit);
        let formula = bundle.module.proof_obligations[0].formula.as_mut().unwrap();
        formula.payload = serde_json::json!({
            "schema":TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
            "variables":[{"name":"r","sort":"int"},{"name":"x","sort":"int"}],
            "body":{"op":"and","lhs":{"op":"eq","lhs":{"var":"r"},"rhs":{"var":"x"}},
                "rhs":{"op":"eq","lhs":div,"rhs":div}}
        })
        .to_string();
        refresh_native_bundle_module_identity(&mut bundle);
        let admitted = ValidatedNativeBundle::new(&bundle).unwrap();
        let error = verify_trust_ir_body_request_validated(&admitted, wp_ids(&bundle)[0])
            .unwrap_err()
            .to_string();
        assert!(error.contains("unreadable claim names"), "{error}");
        assert!(trust_wp_core::verify_bundle::decode_trust_formula_v1_claim(
            &bundle.module.proof_obligations[0]
                .formula
                .as_ref()
                .unwrap()
                .payload
        )
        .unwrap_err()
        .to_string()
        .contains("divisor must be syntactically nonzero"));
    }
    // Typed JSON division is Euclidean, including negative contract integers;
    // it is not the unsigned body operation or Rust's truncated division.
    let quotient = serde_json::json!({"op":"div","lhs":{"int":-3},"rhs":{"int":2}});
    checked(&clause(
        serde_json::json!({"op":"eq","lhs":quotient,"rhs":{"int":-2}}),
    ));
    failed(&clause(
        serde_json::json!({"op":"eq","lhs":quotient,"rhs":{"int":-1}}),
    ));
    let mut negative_divisor = clause(serde_json::json!({"op":"eq",
        "lhs":{"op":"div","lhs":{"int":3},"rhs":{"int":-2}},"rhs":{"int":-1}}));
    checked(&negative_divisor);
    let formula = negative_divisor.module.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap();
    *formula = ProofFormula::new("trust-wp.pure-expr.v1", "-3 / 2 == -1");
    refresh_native_bundle_module_identity(&mut negative_divisor);
    let admitted = ValidatedNativeBundle::new(&negative_divisor).unwrap();
    let error = verify_trust_ir_body_request_validated(&admitted, wp_ids(&negative_divisor)[0])
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("ill-sorted or unsupported scalar operator"),
        "{error}"
    );
}
