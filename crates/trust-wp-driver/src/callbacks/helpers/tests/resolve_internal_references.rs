// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use super::*;

#[test]
fn resolve_internal_references_substitutes_var_inside_final() {
    // When "set" → call_1 and "length1" → Final(Var("set")).len(),
    // resolving should produce "length1" → Final(call_1).len()
    let call_1 = PureExpr::Var("call_1".to_string(), None);
    let mut subs = HashMap::new();
    subs.insert("set".to_string(), call_1.clone());
    subs.insert(
        "length1".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "set".to_string(),
                None,
            )))),
            method: "len".to_string(),
            args: vec![],
        },
    );

    resolve_internal_references(&mut subs);

    // "set" → call_1 unchanged
    assert_eq!(subs["set"], call_1);
    // "length1" → Final(call_1).len() (Var("set") resolved to call_1)
    assert_eq!(
        subs["length1"],
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Final(Arc::new(call_1))),
            method: "len".to_string(),
            args: vec![],
        },
    );
}

#[test]
fn resolve_internal_references_preserves_bare_final_carrier_binding() {
    let mut subs = HashMap::new();
    subs.insert(
        "call_4".to_string(),
        PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        },
    );
    subs.insert(
        "v".to_string(),
        PureExpr::Final(Arc::new(PureExpr::Var(
            "call_4".to_string(),
            Some(ExprSort::Seq),
        ))),
    );

    resolve_internal_references(&mut subs);

    assert_eq!(
        subs["v"],
        PureExpr::Final(Arc::new(PureExpr::Var(
            "call_4".to_string(),
            Some(ExprSort::Seq),
        ))),
        "bare post-state carriers must stay symbolic instead of collapsing through seq_empty()"
    );
}

#[test]
fn resolve_internal_references_no_self_reference() {
    // "x" → Var("x") + 1 should NOT create a cycle
    let mut subs = HashMap::new();
    subs.insert(
        "x".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let original = subs["x"].clone();
    resolve_internal_references(&mut subs);

    // Self-reference excluded from substitution map, so expression unchanged
    assert_eq!(subs["x"], original);
}
