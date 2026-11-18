//! Exact compiler captures: all requests, source identities and contracts are
//! retained. Mutants below are separate diagnostic inputs, never source facts.
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts, trust_ir_native_bundle_to_body_verify_requests,
    verify_trust_ir_body_contracts,
};

use super::*;

const EXTENSION: &str = include_str!("fixtures/widthconv/extension_bits.json");
const SHIFT: &str = include_str!("fixtures/widthconv/shift_mask.json");

fn captured(text: &str) -> NativeVerificationBundle {
    let bundle = derived_v9_capture(text);
    bundle.validate().unwrap();
    assert_eq!(bundle.module.stable_digest(), bundle.trust_ir_module_digest);
    let binary = trust_ir::binary::serialize_module(&bundle.module).unwrap();
    assert_eq!(
        trust_ir::binary::deserialize_module(&binary).unwrap(),
        bundle.module
    );
    bundle
}

fn run(bundle: &NativeVerificationBundle) -> Vec<trust_wp_lib::VerifyBundleResult> {
    verify_trust_ir_body_contracts(bundle).unwrap()
}

#[test]
fn translation_witness_discloses_unsigned_memory_without_losing_native_proofs() {
    use trust_wp_lib::trust_ir_body::{
        replay_trust_ir_body_translation_witnesses,
        trust_ir_native_bundle_to_body_translation_witnesses, NativeBodyWpTranslationCoverage,
    };
    for text in [EXTENSION, SHIFT] {
        let bundle = captured(text);
        let witnesses = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
        assert_eq!(witnesses.len(), 2);
        assert!(witnesses.iter().all(|row| matches!(&row.coverage,
            NativeBodyWpTranslationCoverage::Untranslated { reasons } if !reasons.is_empty())));
        replay_trust_ir_body_translation_witnesses(&bundle, &witnesses).unwrap();
        let results = run(&bundle);
        assert!(results
            .iter()
            .all(|row| row.status == VerifyBundleStatus::Verified));
        replay_trust_ir_body_contracts(&bundle, &results).unwrap();
    }
}

#[test]
fn actual_unsigned_widthconv_contracts_prove_and_replay() {
    for source in [EXTENSION, SHIFT] {
        let bundle = captured(source);
        let immutable = bundle.clone();
        assert!(matches!(
            trust_ir_native_bundle_to_verify_requests(&bundle),
            Err(TrustIrNativeBundleError::UnsupportedClauseBinding {
                reason: TrustIrUnsupportedClauseBindingReason::UnmodeledSort { .. },
                ..
            })
        ));
        let requests = trust_ir_native_bundle_to_body_verify_requests(&bundle).unwrap();
        let results = run(&bundle);
        assert_eq!(results.len(), 2);
        assert!(
            results
                .iter()
                .all(|result| result.status == VerifyBundleStatus::Verified),
            "{results:#?}"
        );
        let bytes = serde_json::to_vec(&results).unwrap();
        let restored: Vec<trust_wp_lib::VerifyBundleResult> =
            serde_json::from_slice(&bytes).unwrap();
        replay_trust_ir_body_contracts(&bundle, &restored).unwrap();
        assert_eq!(
            bundle, immutable,
            "no original rows or source input may change"
        );
        assert_eq!(requests.len(), 2);
    }
}

#[test]
fn actual_unsigned_wrong_result_and_false_assume_do_not_verify() {
    let original = captured(SHIFT);
    let accepted = run(&original);
    for false_assume in [false, true] {
        let mut changed = original.clone();
        let mut found = false;
        for node in changed.module.functions[0]
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.body)
        {
            if false_assume {
                if let Inst::Assume { cond } = &mut node.inst {
                    // The original value 12 is the explicit Boolean false.
                    *cond = ValueId::new(12);
                    found = true;
                    break;
                }
            } else if let Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(value),
            } = &mut node.inst
            {
                if *value == 7 {
                    *value = 200;
                    found = true;
                    break;
                }
            }
        }
        assert!(found);
        refresh_native_bundle_module_identity(&mut changed);
        let results = run(&changed);
        assert!(
            results
                .iter()
                .all(|result| result.status != VerifyBundleStatus::Verified),
            "{results:#?}"
        );
        assert!(replay_trust_ir_body_contracts(&changed, &accepted).is_err());
    }
}

#[test]
fn actual_unsigned_wrong_post_and_width_do_not_verify() {
    let original = captured(SHIFT);
    let accepted = run(&original);
    let mut changed = original.clone();
    let formula = changed
        .module
        .proof_obligations
        .iter_mut()
        .find(|p| p.id == ProofId::new(0))
        .unwrap()
        .formula
        .as_mut()
        .unwrap();
    let mut payload: serde_json::Value = serde_json::from_str(&formula.payload).unwrap();
    payload["body"]["rhs"]["int"] = serde_json::json!(-1);
    formula.payload = payload.to_string();
    refresh_native_bundle_module_identity(&mut changed);
    let results = run(&changed);
    assert_ne!(results[0].status, VerifyBundleStatus::Verified);
    assert!(replay_trust_ir_body_contracts(&changed, &accepted).is_err());

    let mut wrong_width = original.clone();
    let formula = wrong_width
        .module
        .proof_obligations
        .iter_mut()
        .find(|p| p.id == ProofId::new(0))
        .unwrap()
        .formula
        .as_mut()
        .unwrap();
    formula.bindings[0].1.sort = ClauseSort::BitVec(31);
    refresh_native_bundle_module_identity(&mut wrong_width);
    assert!(trust_ir_native_bundle_to_body_verify_requests(&wrong_width).is_err());
}

#[test]
fn actual_unsigned_memory_initialization_and_instruction_checks_remain_required() {
    for source in [EXTENSION, SHIFT] {
        let mut changed = captured(source);
        for block in &mut changed.module.functions[0].blocks {
            block
                .body
                .retain(|node| !matches!(node.inst, Inst::Store { .. }));
        }
        refresh_native_bundle_module_identity(&mut changed);
        let error = trust_ir_native_bundle_to_body_verify_requests(&changed)
            .unwrap_err()
            .to_string();
        assert!(error.contains("uninitialized"), "{error}");
    }
}

#[test]
fn unsigned_constants_and_comparisons_retain_machine_width_checks() {
    let original = captured(SHIFT);
    for value in [-1, i128::from(u32::MAX) + 1] {
        let mut changed = original.clone();
        let value_slot = changed.module.functions[0]
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.body)
            .find_map(|node| match &mut node.inst {
                Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(value),
                } => Some(value),
                _ => None,
            })
            .expect("captured unsigned constant");
        *value_slot = value;
        refresh_native_bundle_module_identity(&mut changed);
        assert!(trust_ir_native_bundle_to_body_verify_requests(&changed).is_err());
    }
    let mut changed = original;
    let comparison = changed.module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find_map(|node| match &mut node.inst {
            Inst::ICmp {
                op, ty: Ty::U32, ..
            } => Some(op),
            _ => None,
        })
        .expect("captured unsigned comparison");
    *comparison = trust_ir::ICmpOp::Slt;
    refresh_native_bundle_module_identity(&mut changed);
    assert!(trust_ir_native_bundle_to_body_verify_requests(&changed).is_err());
}

#[test]
fn unsigned_captures_agree_with_the_shared_reference_at_boundaries() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    let shift = captured(SHIFT);
    let extension = captured(EXTENSION);
    let integer = |value| InterpretValue::int(Ty::U32, i128::from(value)).unwrap();
    for bits in [0_u32, 1, 7, 8, 16, 31, 32, 64, 128, 1 << 31, u32::MAX] {
        let result = Interpreter::with_module(&shift.module)
            .execute_func(FuncId::new(0), [integer(bits)])
            .expect("admitted body executes in shared semantics");
        let expected = if [8, 16, 32, 64, 128].contains(&bits) {
            bits - 1
        } else {
            0
        };
        assert_eq!(result.returns, vec![integer(expected)]);
        for container in [0_u32, 8, 16, 32, 64, 128, u32::MAX] {
            let result = Interpreter::with_module(&extension.module)
                .execute_func(FuncId::new(0), [integer(bits), integer(container)])
                .expect("admitted body executes in shared semantics");
            let expected = if [8, 16, 32, 64].contains(&bits)
                && [16, 32, 64, 128].contains(&container)
                && bits < container
            {
                container - bits
            } else {
                0
            };
            assert_eq!(
                result.returns,
                vec![integer(expected)],
                "{bits} -> {container}"
            );
        }
    }
}
