// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Build a two-function logic-fn fixture (compute + unused) for filter tests.
fn make_filter_logic_fn_fixture() -> (Vec<LogicFnDef>, Vec<LogicMode>, PureExpr) {
    let compute = LogicFnDef::new(
        "compute".to_string(),
        "test::compute".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    )
    .with_mode(LogicMode::Open);
    let unused = LogicFnDef::new(
        "unused".to_string(),
        "test::unused".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    )
    .with_mode(LogicMode::Default);
    let return_expr = PureExpr::LogicFnCall {
        name: "compute".to_string(),
        args: vec![PureExpr::Var("i".to_string(), None)],
    };
    (
        vec![compute, unused],
        vec![LogicMode::Open, LogicMode::Default],
        return_expr,
    )
}

#[test]
#[timeout(30000)]
fn filter_logic_fns_scans_selected_type_invariant_bodies() {
    use std::sync::Arc;

    use trust_wp_core::logic::{type_invariant_method_name, TypeInvariantDef};

    let good_bucket = LogicFnDef::new(
        "good_bucket".to_string(),
        "test::MyHashMap::good_bucket".to_string(),
        vec!["self".to_string(), "l".to_string(), "h".to_string()],
        PureExpr::Bool(true),
    );
    let no_double_binding = LogicFnDef::new(
        "no_double_binding".to_string(),
        "test::List::no_double_binding".to_string(),
        vec!["self".to_string()],
        PureExpr::Bool(true),
    );
    let unused = LogicFnDef::new(
        "unused".to_string(),
        "test::unused".to_string(),
        vec![],
        PureExpr::Bool(true),
    );
    let logic_fns = vec![good_bucket, no_double_binding, unused];
    let invariant_body = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
            method: "good_bucket".to_string(),
            args: vec![PureExpr::Var("l".to_string(), None), PureExpr::Int(0)],
        }),
        BinOp::And,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("l".to_string(), None)),
            method: "no_double_binding".to_string(),
            args: vec![],
        }),
    );
    let type_invariants = vec![TypeInvariantDef::new(
        "MyHashMap".to_string(),
        "self".to_string(),
        invariant_body,
    )];
    let require_invariant = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("map".to_string(), None)),
        method: type_invariant_method_name("MyHashMap"),
        args: vec![],
    };
    let body_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();
    let ctx = LoopVerificationContext {
        requires: std::slice::from_ref(&require_invariant),
        ensures: &[],
        invariants: &[],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            type_invariants: Some(&type_invariants),
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    };

    let (filtered_fns, _) =
        filter_logic_fns_for_loop_ctx(&ctx).expect("well-formed config should not error");
    let names = filtered_fns
        .expect("type invariant body should retain logic fns")
        .into_iter()
        .map(|logic_fn| logic_fn.name().to_string())
        .collect::<std::collections::HashSet<_>>();

    assert!(names.contains("good_bucket"));
    assert!(names.contains("no_double_binding"));
    assert!(!names.contains("unused"));
}

#[test]
#[timeout(30000)]
fn filter_logic_fns_prunes_all_without_return_expr() {
    let (logic_fns, modes, _return_expr) = make_filter_logic_fn_fixture();
    let body_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            mode_overrides: Some(&modes),
            ..LoopEncoderConfig::default()
        },
    };
    let (filtered_fns, filtered_modes) =
        filter_logic_fns_for_loop_ctx(&ctx).expect("well-formed config should not error");
    assert!(
        filtered_fns.is_none(),
        "without return_expr, filtered logic fns should be None (all pruned)"
    );
    assert!(
        filtered_modes.is_none(),
        "without return_expr, filtered mode overrides should be None"
    );
}

#[test]
#[timeout(30000)]
fn filter_logic_fns_retains_referenced_with_return_expr() {
    let (logic_fns, modes, return_expr) = make_filter_logic_fn_fixture();
    let body_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            mode_overrides: Some(&modes),
            ..LoopEncoderConfig::default()
        },
    };
    let (filtered_fns, filtered_modes) =
        filter_logic_fns_for_loop_ctx(&ctx).expect("well-formed config should not error");

    let filtered_fns = filtered_fns.expect("return_expr should keep compute");
    assert_eq!(
        filtered_fns.len(),
        1,
        "return_expr referencing 'compute' should retain exactly one logic fn"
    );
    assert_eq!(
        filtered_fns[0].name(),
        "compute",
        "retained logic fn should be 'compute', not {:?}",
        filtered_fns[0].name()
    );

    let filtered_modes =
        filtered_modes.expect("mode overrides should be filtered alongside logic_fns");
    assert_eq!(
        filtered_modes,
        vec![LogicMode::Open],
        "filtered mode overrides should match retained logic fn (Open for compute)"
    );
}

/// Mismatched `mode_overrides` and `logic_fns` lengths are silently dropped
/// (#2316, #2700). The overrides are computed from the full logic_fn_defs set,
/// but logic_fns may be a filtered subset. Rather than returning an encoding
/// error, the overrides are dropped so filter_logic_functions_for_goal falls
/// back to default mode scoping.
#[test]
#[timeout(30000)]
fn mismatched_mode_overrides_length_drops_overrides_silently() {
    let logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    )
    .with_mode(LogicMode::Default);
    let logic_fns = vec![logic_fn];
    // Two mode overrides for one logic function — length mismatch.
    let modes = vec![LogicMode::Default, LogicMode::Open];
    let body_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            mode_overrides: Some(&modes),
            ..LoopEncoderConfig::default()
        },
    };

    // Should NOT error — overrides are dropped, verification proceeds
    let result = verify_loop_invariant(&ctx);
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}
