// Test-only legacy comparison. Copy to tests/body_contract/shared_codec_sp.rs
// and register it as a child of tests/trust_ir_native_bundle.rs.
use serde_json::json;

use super::*;

fn fallback_bundle(false_assertion: bool) -> NativeVerificationBundle {
    let reflexive_x = json!({"op":"eq", "lhs":{"var":"x"}, "rhs":{"var":"x"}});
    let result_atom = json!({
        "op": if false_assertion { "ne" } else { "eq" },
        "lhs":{"result":true}, "rhs":{"result":true}
    });
    let payload = json!({
        "schema":"trust_wp.trust-formula.v1",
        "variables":[{"name":"x", "sort":"Int"}],
        "result":{"sort":"Int"},
        "body":{
            "op":"implies",
            "lhs":{"op":"and", "lhs":reflexive_x.clone(),
                "rhs":{"op":"and", "lhs":{"bool":true}, "rhs":reflexive_x.clone()}},
            "rhs":{"op":"and", "lhs":result_atom,
                "rhs":{"op":"and", "lhs":reflexive_x, "rhs":{"bool":true}}}
        }
    })
    .to_string();
    let mut formula = ProofFormula::new(TRUST_FORMULA_CLAIM_SCHEMA_VERSION, payload);
    formula.bindings = vec![
        (
            "x".into(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "result".into(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
    ];
    let mut bundle = native_bundle_with_signature(
        formula,
        TrustWpVerificationMode::StrongestPostcondition,
        vec![Ty::U64],
        vec![Ty::U64],
    );
    // The parent fixture normally supplies explicit native replay atoms.
    // Exercise the fallback without manufacturing any replay provenance.
    bundle.requests = vec![NativeVerificationRequest::TrustWp(
        trust_wp_request_with_replay_context(TrustWpVerificationMode::StrongestPostcondition, None),
    )];
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
}

#[test]
fn shared_codec_sp_fallback_cannot_mint_native_provenance_even_after_rehashing() {
    let mut identities = Vec::new();
    for false_assertion in [false, true] {
        let bundle = fallback_bundle(false_assertion);
        let original_bytes = trust_ir::binary::serialize_module(&bundle.module).unwrap();
        assert_eq!(bundle.trust_ir_module_digest, bundle.module.stable_digest());
        identities.push(bundle.trust_ir_module_digest);
        let expected = TrustIrNativeBundleError::InvalidNativeBundle {
            errors: vec!["native verification request 7 requires TrustWp strongest-postcondition replay atoms".into()],
        };
        assert_eq!(
            trust_ir_native_bundle_to_verify_requests(&bundle).unwrap_err(),
            expected
        );
        let error = verify_trust_ir_native_bundle(&bundle).unwrap_err();
        assert!(
            matches!(&error, TrustWpLibError::TrustIrNativeBundle(inner)
            if inner == &expected),
            "{error:?}"
        );
        assert_eq!(
            trust_ir::binary::serialize_module(&bundle.module).unwrap(),
            original_bytes
        );
    }
    assert_ne!(
        identities[0], identities[1],
        "changed original assertion bytes change the original module identity"
    );
}

#[test]
fn shared_codec_sp_fallback_rehashed_result_place_is_still_refused() {
    let mut bundle = fallback_bundle(false);
    bundle.requests = vec![NativeVerificationRequest::TrustWp(trust_wp_request(
        TrustWpVerificationMode::StrongestPostcondition,
    ))];
    let before = bundle.trust_ir_module_digest;
    let formula = bundle.module.proof_obligations[0].formula.as_mut().unwrap();
    let (_, binding) = formula
        .bindings
        .iter_mut()
        .find(|(name, _)| name == "result")
        .unwrap();
    let place = ClausePlace::ResultSlot { index: 1 };
    binding.place = place;
    refresh_native_bundle_module_identity(&mut bundle);
    assert_ne!(bundle.trust_ir_module_digest, before);
    assert_eq!(bundle.trust_ir_module_digest, bundle.module.stable_digest());
    assert_binding_refused(
        &bundle,
        TrustIrClauseCarrier::Obligation,
        "result",
        TrustIrUnsupportedClauseBindingReason::UnresolvedPlace {
            place,
            error: ClauseTypingError::ResultOutOfRange { index: 1, arity: 1 },
        },
    );
}

#[test]
fn shared_codec_sp_explicit_native_context_keeps_precedence_over_fallback() {
    let mut bundle = fallback_bundle(false);
    bundle.requests = vec![NativeVerificationRequest::TrustWp(trust_wp_request(
        TrustWpVerificationMode::StrongestPostcondition,
    ))];
    let requests =
        trust_ir_native_bundle_to_verify_requests(&bundle).expect("explicit context converts");
    let context = &requests[0].obligations[0].metadata.proof_context;
    assert_eq!(context.assumptions.len(), 1);
    assert_eq!(context.assertions.len(), 1);
    assert_eq!(context.assumptions[0].native_replay_atom_id, Some(0));
    assert_eq!(context.assertions[0].native_replay_atom_id, Some(1));
    assert_eq!(
        context.assumptions[0].claim.payload,
        trust_formula_linear_assumption_atom()
    );
    assert_eq!(
        context.assertions[0].claim.payload,
        trust_formula_linear_assertion_atom()
    );
}
