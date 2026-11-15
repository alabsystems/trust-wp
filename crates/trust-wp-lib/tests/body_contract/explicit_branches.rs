//! Native WP and replay of the explicit shared-IR branch calculus fixtures.
//! These modules are not compiler captures. The original wire body remains
//! unchanged when the test attaches its contract and request metadata.

use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_contracts, trust_ir_native_bundle_to_body_verify_requests,
    verify_trust_ir_body_contracts,
};

use super::*;

#[derive(Clone, Copy)]
struct Fixture {
    name: &'static str,
    bytes: &'static [u8],
    correct: bool,
}

const FIXTURES: &[Fixture] = &[
    Fixture {
        name: "permuted",
        bytes: include_bytes!("fixtures/explicit_calculus/permuted.tirb"),
        correct: true,
    },
    Fixture {
        name: "aliased",
        bytes: include_bytes!("fixtures/explicit_calculus/aliased.tirb"),
        correct: true,
    },
    Fixture {
        name: "wrongBranch",
        bytes: include_bytes!("fixtures/explicit_calculus/wrongBranch.tirb"),
        correct: false,
    },
    Fixture {
        name: "wrongCondition",
        bytes: include_bytes!("fixtures/explicit_calculus/wrongCondition.tirb"),
        correct: false,
    },
    Fixture {
        name: "wrongArgument",
        bytes: include_bytes!("fixtures/explicit_calculus/wrongArgument.tirb"),
        correct: false,
    },
];
const POST: &str =
    "((c : bool) && ((r : bool) == (l : bool))) || (!(c : bool) && ((r : bool) == (q : bool)))";

#[test]
fn translation_witness_regenerates_original_questions_and_refuses_valid_mutations() {
    use trust_wp_lib::trust_ir_body::{
        replay_trust_ir_body_translation_witnesses,
        trust_ir_native_bundle_to_body_translation_witnesses, NativeBodyWpTranslationCoverage,
    };
    let original = attached(FIXTURES[0], POST);
    let witnesses = trust_ir_native_bundle_to_body_translation_witnesses(&original).unwrap();
    assert_eq!(witnesses.len(), 1);
    let witness = &witnesses[0];
    assert_eq!(witness.native_bundle_digest, original.stable_digest());
    assert_eq!(witness.module_digest, original.module.stable_digest());
    assert_eq!(
        witness.native_request_digest,
        original.requests[0].stable_digest()
    );
    assert_eq!(
        witness.function_body_digest,
        original
            .module
            .function_body_digest(witness.function)
            .unwrap()
    );
    assert_eq!(
        witness.contracts[0].1,
        *original.module.proof_obligations[0]
            .formula
            .as_ref()
            .unwrap()
    );
    assert_eq!(
        witness.coverage,
        NativeBodyWpTranslationCoverage::BooleanAssignmentCfg
    );
    assert_eq!(
        witness.derived_request,
        trust_ir_native_bundle_to_body_verify_requests(&original).unwrap()[0]
    );
    let restored: Vec<trust_wp_lib::trust_ir_body::NativeBodyWpTranslationWitness> =
        serde_json::from_slice(&serde_json::to_vec(&witnesses).unwrap()).unwrap();
    replay_trust_ir_body_translation_witnesses(&original, &restored).unwrap();
    check(&original, true);

    let mut changed = witnesses.clone();
    changed[0].plan.successors.swap(0, 1);
    assert!(replay_trust_ir_body_translation_witnesses(&original, &changed).is_err());
    let mut changed = witnesses.clone();
    changed[0].derived_request.obligations[0].claim.payload = trust_formula_true().into();
    assert_eq!(changed[0].derived_request.validation_diagnostics(), []);
    assert!(replay_trust_ir_body_translation_witnesses(&original, &changed).is_err());
    let mut changed = witnesses.clone();
    changed[0].native_request_digest = digest(198);
    assert!(replay_trust_ir_body_translation_witnesses(&original, &changed).is_err());
    let mut changed = witnesses.clone();
    changed[0].parameters[0].1.push_str("_different");
    assert!(replay_trust_ir_body_translation_witnesses(&original, &changed).is_err());
    for changed_input in [
        attached(FIXTURES[2], POST),
        attached(FIXTURES[0], &format!("!({POST})")),
    ] {
        changed_input.validate().unwrap();
        assert_eq!(trust_ir_build::validate_module(&changed_input.module), []);
        assert!(replay_trust_ir_body_translation_witnesses(&changed_input, &witnesses).is_err());
    }
}

fn decoded(fixture: Fixture) -> Module {
    let module = trust_ir::binary::deserialize_module(fixture.bytes).unwrap();
    assert_eq!(
        trust_ir::binary::serialize_module(&module).unwrap(),
        fixture.bytes
    );
    assert_eq!(module.proof_obligations, []);
    assert_eq!(trust_ir_build::validate_module(&module), []);
    module
}

fn attached(fixture: Fixture, contract: &str) -> NativeVerificationBundle {
    let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", contract);
    formula.bindings = vec![
        (
            "c".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "l".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 1 },
            },
        ),
        (
            "q".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 2 },
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
        vec![Ty::Bool; 3],
        vec![Ty::Bool],
    );
    let obligations = std::mem::take(&mut bundle.module.proof_obligations);
    bundle.module = decoded(fixture);
    let original_digest = bundle.module.stable_digest();
    bundle.module.proof_obligations = obligations;
    bundle.module.proof_obligations[0].description =
        "explicit shared-IR calculus postcondition".into();
    bundle.module.proof_obligations[0]
        .source
        .as_mut()
        .unwrap()
        .source_id = format!("explicit-calculus:{}:choose", fixture.name);
    bundle.producer = NativeBundleProducer::TrustIr;
    bundle.provenance.source_language = trust_ir::NativeSourceLanguage::TrustIr;
    bundle.provenance.source_languages = [
        trust_ir::NativeSourceLanguage::TrustIr,
        trust_ir::NativeSourceLanguage::Unknown,
    ]
    .into_iter()
    .collect();
    bundle.provenance.source_artifact = Some(format!("explicit-calculus/{}.tirb", fixture.name));
    bundle.provenance.source_digest = Some(ProofDigest::sha256_domain(
        "trust-wp.explicit-calculus-fixture.v1",
        fixture.bytes,
    ));
    bundle.compiler_facts = trust_ir::NativeCompilerFacts::default();
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: "vc:trust-wp:postcondition:0".into(),
            function: Some(FuncId::new(0)),
            // This location denotes the attached test contract, not Rust source.
            span: Some(SourceSpan {
                file: 0,
                line: 1,
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: vec![],
        });
    bundle.lineage.nodes[0].source_module = original_digest;
    bundle.lineage.nodes[0].transform = ProofTransform::new(
        ProofTransformStage::SolverAdapter,
        "attach-source-postcondition",
        "explicit-calculus-fixture",
        "1",
    );
    if let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[0] {
        request.provenance.replay = Some(
            ProofReplayIdentity::new("trust-wp", "explicit shared-IR Boolean branch fixture")
                .with_transcript_digest(original_digest),
        );
    }
    refresh_native_bundle_module_identity(&mut bundle);
    let mut body = bundle.module.clone();
    body.proof_obligations.clear();
    assert_eq!(
        trust_ir::binary::serialize_module(&body).unwrap(),
        fixture.bytes
    );
    bundle
}

fn observed(fixture: Fixture, c: bool, l: bool, q: bool) -> bool {
    let module = decoded(fixture);
    let output = trust_ir::interpret::Interpreter::with_module(&module)
        .execute_func(
            FuncId::new(0),
            [c, l, q].map(trust_ir::interpret::InterpretValue::bool),
        )
        .unwrap();
    assert_eq!(output.returns.len(), 1);
    output.returns[0].as_bool().unwrap()
}

fn check(
    bundle: &NativeVerificationBundle,
    expected: bool,
) -> Vec<trust_wp_lib::VerifyBundleResult> {
    let requests = trust_ir_native_bundle_to_body_verify_requests(bundle).unwrap();
    let direct: Vec<_> = requests
        .into_iter()
        .map(trust_wp_lib::verify_bundle)
        .collect();
    let results = verify_trust_ir_body_contracts(bundle).unwrap();
    assert_eq!(
        serde_json::to_value(&results).unwrap(),
        serde_json::to_value(direct).unwrap()
    );
    assert_eq!(results.len(), 1);
    assert_eq!(
        results[0].status,
        if expected {
            VerifyBundleStatus::Verified
        } else {
            VerifyBundleStatus::Failed
        },
        "{results:#?}"
    );
    assert_eq!(
        replay_trust_ir_body_contracts(bundle, &results).is_ok(),
        expected
    );
    if expected {
        let wire = serde_json::to_vec(&results).unwrap();
        let restored: Vec<trust_wp_lib::VerifyBundleResult> =
            serde_json::from_slice(&wire).unwrap();
        replay_trust_ir_body_contracts(bundle, &restored).unwrap();
    }
    results
}

fn record(
    label: &str,
    fixture: Fixture,
    bundle: &NativeVerificationBundle,
    results: &[trust_wp_lib::VerifyBundleResult],
) {
    if let Some(root) = std::env::var_os("TRUST_WP_EXPLICIT_EVIDENCE_DIR") {
        let root = std::path::PathBuf::from(root);
        std::fs::create_dir_all(&root).unwrap();
        let value = serde_json::json!({
            "origin": "explicit shared-IR calculus fixture, not compiler output",
            "fixture": fixture.name,
            "original_module_bytes": fixture.bytes,
            "bundle": bundle,
            "requests": trust_ir_native_bundle_to_body_verify_requests(bundle).unwrap(),
            "results": results,
        });
        std::fs::write(
            root.join(format!("{label}.json")),
            serde_json::to_vec_pretty(&value).unwrap(),
        )
        .unwrap();
    }
}

#[test]
fn explicit_branch_modules_verify_and_replay_only_the_correct_contract() {
    for &fixture in FIXTURES {
        let bundle = attached(fixture, POST);
        let results = check(&bundle, fixture.correct);
        record(
            &format!("universal-{}", fixture.name),
            fixture,
            &bundle,
            &results,
        );
    }
    for &fixture in &FIXTURES[..2] {
        check(&attached(fixture, &format!("!({POST})")), false);
    }
}

#[test]
fn explicit_branch_modules_agree_with_every_boolean_input() {
    for &fixture in FIXTURES {
        for c in [false, true] {
            for l in [false, true] {
                for q in [false, true] {
                    let intended = if c { l } else { q };
                    let actual = observed(fixture, c, l, q);
                    let contract = format!(
                        "!(((c : bool) == {c}) && ((l : bool) == {l}) && ((q : bool) == {q})) || ((r : bool) == {intended})"
                    );
                    let bundle = attached(fixture, &contract);
                    let results = check(&bundle, actual == intended);
                    record(
                        &format!("input-{}-{c}-{l}-{q}", fixture.name),
                        fixture,
                        &bundle,
                        &results,
                    );
                    if fixture.correct {
                        assert_eq!(actual, intended);
                        let wrong = format!(
                            "!(((c : bool) == {c}) && ((l : bool) == {l}) && ((q : bool) == {q})) || ((r : bool) != {intended})"
                        );
                        check(&attached(fixture, &wrong), false);
                    }
                }
            }
        }
    }
}

#[test]
fn explicit_branch_proof_cannot_move_to_another_body_or_contract() {
    let bundle = attached(FIXTURES[0], POST);
    let proof = check(&bundle, true);
    for &fixture in &FIXTURES[1..] {
        assert!(replay_trust_ir_body_contracts(&attached(fixture, POST), &proof).is_err());
    }
    assert!(
        replay_trust_ir_body_contracts(&attached(FIXTURES[0], &format!("!({POST})")), &proof)
            .is_err()
    );
}

#[test]
fn explicit_branch_inspection_rejects_invalid_original_inputs() {
    let mut malformed = attached(FIXTURES[0], POST);
    if let Inst::CondBr { then_args, .. } =
        &mut malformed.module.functions[0].blocks[0].body[0].inst
    {
        then_args.clear();
    } else {
        panic!("fixture must retain its original conditional branch");
    }
    refresh_native_bundle_module_identity(&mut malformed);
    assert!(trust_ir_native_bundle_to_body_verify_requests(&malformed).is_err());
    assert!(verify_trust_ir_body_contracts(&malformed).is_err());
    let mut mismatched = attached(FIXTURES[0], POST);
    mismatched.trust_ir_module_digest = digest(0x7f);
    assert!(trust_ir_native_bundle_to_body_verify_requests(&mismatched).is_err());
    assert!(verify_trust_ir_body_contracts(&mismatched).is_err());
}
