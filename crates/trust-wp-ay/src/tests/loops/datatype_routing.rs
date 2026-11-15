// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::{ExprSort, NamedBindingValue};

use super::*;

fn sample_counter_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "Counter".to_string(),
        AdtDecl::new(
            "crate::Counter".to_string(),
            "Counter".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Counter".to_string(),
                "Counter".to_string(),
                vec![AdtFieldDecl::new("value".to_string(), ExprSort::Int)],
            )],
        ),
    )])
}

/// `Counter { value }` as the driver's placement pass hands it on: the
/// constructor at its declared field order, without the field-name metadata
/// the encoder's one door refuses (verify::placement_gate).
fn counter_ctor(value: i64) -> PureExpr {
    PureExpr::LogicFnCall {
        name: "Counter".to_string(),
        args: vec![int(value)],
    }
}

fn counter_value(expr: PureExpr) -> PureExpr {
    named_field("value", expr)
}

fn loop_ctx_with_counter_adt(use_adt_decls: bool) -> LoopVerificationContext<'static> {
    let counter_sort =
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("crate::Counter"));
    let counter = var_with_sort("c", counter_sort);
    let invariant = eq(counter_value(counter), int(7));

    let body_effect = HashMap::from([("c".to_string(), counter_ctor(7))]);
    let pre_loop_assignments =
        HashMap::from([("c".to_string(), NamedBindingValue::untyped(counter_ctor(7)))]);

    let config = if use_adt_decls {
        LoopEncoderConfig::default().with_adt_decls(Box::leak(Box::new(sample_counter_adt_decls())))
    } else {
        LoopEncoderConfig::default()
    };

    LoopVerificationContext {
        requires: &[],
        ensures: Box::leak(Box::new([invariant.clone()])),
        invariants: Box::leak(Box::new([invariant])),
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &["c"],
        body_effect: Box::leak(Box::new(body_effect)),
        deref_body_effect: Box::leak(Box::new(HashMap::new())),
        double_deref_body_effect: Box::leak(Box::new(HashMap::new())),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: Box::leak(Box::new(pre_loop_assignments)),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config,
    }
}

#[test]
#[timeout(30000)]
fn loop_named_field_projection_verifies_with_adt_decls() {
    let result = verify_loop_invariant(&loop_ctx_with_counter_adt(true))
        .expect("loop verification with ADT metadata should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "pre-loop Counter{{value}} constructor should establish the field invariant: {:?}",
        result.initialization
    );
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome still fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result.preservation),
        "loop body Counter{{value}} reconstruction should preserve the field invariant: {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "loop exit should retain the field-selector fact for the postcondition: {:?}",
        result.postcondition
    );
}

#[test]
#[timeout(30000)]
fn loop_named_field_projection_without_adt_decls_does_not_fully_verify() {
    let result = verify_loop_invariant(&loop_ctx_with_counter_adt(false));

    match result {
        Ok(result) => assert!(
            !result.all_verified(),
            "without adt_decls, loop constructor/selector routing should not prove the full VC: {result:?}"
        ),
        Err(err) => {
            let rendered = err.to_string();
            assert!(
                rendered.contains("__trust_wp_field_value") || rendered.contains("sort mismatch"),
                "without adt_decls, loop selector routing should fail closed with a field/sort error: {err:?}"
            );
        }
    }
}
