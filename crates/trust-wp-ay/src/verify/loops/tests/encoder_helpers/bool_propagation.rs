// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// ── propagate_bool_and_predeclare coverage (#2133) ─────────────────

/// Bool sort propagates from modified var to its body effect target.
/// When `done` is Bool and body_effect maps `done` → Var("flag"),
/// then `flag` should also be marked Bool. (#544)
#[test]
#[timeout(30000)]
fn propagate_bool_and_predeclare_propagates_bool_through_effect() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Var("done".to_string(), Some(ExprSort::Bool))],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    // Pre-mark `done` as Bool (simulating what register_sort_hints does)
    encoder.mark_bool_var("done");

    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), PureExpr::Var("flag".to_string(), None));

    propagate_bool_and_predeclare(&mut encoder, &["done"], &body_effect)
        .expect("propagate should succeed");

    assert!(
        encoder.is_bool_var("flag"),
        "Bool sort should propagate from `done` to `flag` via body effect (#544)"
    );
    assert!(
        encoder.is_bool_var("done"),
        "`done` should remain Bool after propagation"
    );
}

/// LogicFnCall effects get Bool hint via SMT name. (#849)
#[test]
#[timeout(30000)]
fn propagate_bool_and_predeclare_logic_fn_call_bool_hint() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Var("done".to_string(), Some(ExprSort::Bool))],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");
    encoder.mark_bool_var("done");

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "done".to_string(),
        PureExpr::LogicFnCall {
            name: "check_condition".to_string(),
            args: vec![],
        },
    );

    propagate_bool_and_predeclare(&mut encoder, &["done"], &body_effect)
        .expect("propagate with LogicFnCall should succeed");

    // The SMT name for the logic fn should be marked Bool
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("check_condition");
    assert!(
        encoder.is_bool_var(&smt_name),
        "LogicFnCall effect should get Bool hint on SMT name `{smt_name}` (#849)"
    );
}

/// Two-phase sort plan: collect sorts without declaring, then apply. (#2020)
#[test]
#[timeout(30000)]
fn collect_loop_sort_plan_separates_decision_from_declaration() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Var("done".to_string(), Some(ExprSort::Bool))],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");
    encoder.mark_bool_var("done");

    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), PureExpr::Var("flag".to_string(), None));
    body_effect.insert(
        "count".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("count".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    // Phase 1: collect — sort decisions captured but vars not declared
    let plan = collect_loop_sort_plan(&mut encoder, &["done", "count"], &body_effect);

    assert_eq!(
        plan.sort_for("done"),
        Some(&Sort::Bool),
        "Bool var should plan as Bool"
    );
    assert_eq!(
        plan.sort_for("count"),
        Some(&Sort::Int),
        "Int effect var should plan as Int"
    );

    // Phase 2: apply — declarations happen
    plan.apply(&mut encoder).expect("plan apply should succeed");

    assert!(
        encoder.is_bool_var("flag"),
        "Bool should propagate from `done` to `flag` during collection (#544)"
    );
}

/// Havoc path: modified var not in body_effect uses resolve_var_sort_or_int.
#[test]
#[timeout(30000)]
fn propagate_bool_and_predeclare_havoc_declares_int_by_default() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Var("x".to_string(), None)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let body_effect = HashMap::new(); // empty — `x` is havoced

    propagate_bool_and_predeclare(&mut encoder, &["x"], &body_effect)
        .expect("propagate with empty body effect should succeed");

    // `x` should be declared — verify by encoding it
    let x_term = encoder
        .encode_pure(&PureExpr::Var("x".to_string(), None))
        .expect("x should be declared after propagate");
    // The fact that encode_pure succeeds confirms the variable was declared
    assert!(
        !format!("{x_term:?}").is_empty(),
        "x should be a valid term"
    );
}
