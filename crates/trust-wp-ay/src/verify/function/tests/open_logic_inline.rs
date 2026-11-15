// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The type-invariant requirement expansion unfolds open logic bodies with no
//! requires context, so it must never unfold a definition guarded by
//! `#[requires]`: its body is an equation only where the requires hold.

use std::sync::Arc;

use trust_wp_core::{
    formula::{BinOp, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

use super::super::expanded_type_invariant_requirements;

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn gt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Gt, Arc::new(rhs))
}

#[test]
fn open_logic_fn_call_inlines_only_unguarded_definitions() {
    let call = PureExpr::LogicFnCall {
        name: "pos".to_string(),
        args: vec![var("y")],
    };
    let unguarded = LogicFnDef::new(
        "pos".to_string(),
        "crate::pos".to_string(),
        vec!["x".to_string()],
        gt(var("x"), PureExpr::Int(0)),
    )
    .with_mode(LogicMode::Open);
    let expanded = expanded_type_invariant_requirements(&[call.clone()], &[], &[unguarded]);
    assert_eq!(expanded, vec![gt(var("y"), PureExpr::Int(0))]);

    let guarded = LogicFnDef::new_with_requires(
        "pos".to_string(),
        "crate::pos".to_string(),
        vec!["x".to_string()],
        vec![gt(var("x"), PureExpr::Int(5))],
        gt(var("x"), PureExpr::Int(0)),
    )
    .with_mode(LogicMode::Open);
    let expanded = expanded_type_invariant_requirements(&[call], &[], &[guarded]);
    assert!(
        expanded.is_empty(),
        "a guarded definition must not be unfolded: {expanded:?}"
    );
}

#[test]
fn open_logic_method_call_inlines_only_unguarded_definitions() {
    let call = PureExpr::MethodCall {
        receiver: Arc::new(var("y")),
        method: "above".to_string(),
        args: vec![var("w")],
    };
    let def = |requires: Vec<PureExpr>| {
        LogicFnDef::new_with_requires(
            "above".to_string(),
            "crate::above".to_string(),
            vec!["self".to_string(), "z".to_string()],
            requires,
            gt(var("self"), var("z")),
        )
        .with_mode(LogicMode::Open)
    };
    let expanded = expanded_type_invariant_requirements(&[call.clone()], &[], &[def(vec![])]);
    assert_eq!(expanded, vec![gt(var("y"), var("w"))]);

    let expanded = expanded_type_invariant_requirements(
        &[call],
        &[],
        &[def(vec![gt(var("z"), PureExpr::Int(0))])],
    );
    assert!(
        expanded.is_empty(),
        "a guarded definition must not be unfolded: {expanded:?}"
    );
}
