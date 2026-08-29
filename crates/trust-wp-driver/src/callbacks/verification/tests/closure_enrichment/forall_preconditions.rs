// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::closure_enrichment::instantiate_forall_precondition_rules;

#[test]
fn instantiate_forall_precondition_rules_adds_ground_precondition() {
    let tuple0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple0".to_string(),
        args: vec![],
    };
    let forall_rule = PureExpr::Forall {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                    method: "postcondition_mut".to_string(),
                    args: vec![
                        tuple0.clone(),
                        PureExpr::Var("st1".to_string(), None),
                        PureExpr::Var("r".to_string(), None),
                    ],
                }),
                BinOp::Implies,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
                    method: "precondition".to_string(),
                    args: vec![tuple0.clone()],
                }),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    let ground_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "f".to_string(),
            None,
        )))),
        method: "postcondition_mut".to_string(),
        args: vec![
            tuple0.clone(),
            PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };
    let expected = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "f".to_string(),
            None,
        )))),
        method: "precondition".to_string(),
        args: vec![tuple0.clone()],
    };

    let mut requires = vec![forall_rule, ground_call];
    let added = instantiate_forall_precondition_rules(&mut requires);

    assert_eq!(added, 1);
    assert!(
        requires.contains(&expected),
        "grounded precondition should be synthesized from forall rule"
    );
}

#[test]
fn instantiate_forall_precondition_rules_skips_non_matching_calls() {
    let tuple0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple0".to_string(),
        args: vec![],
    };
    let forall_rule = PureExpr::Forall {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                    method: "postcondition_mut".to_string(),
                    args: vec![
                        tuple0.clone(),
                        PureExpr::Var("st1".to_string(), None),
                        PureExpr::Var("r".to_string(), None),
                    ],
                }),
                BinOp::Implies,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
                    method: "precondition".to_string(),
                    args: vec![tuple0.clone()],
                }),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    // Receiver mismatch (`g` instead of `f`) should not instantiate.
    let ground_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("g".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            tuple0.clone(),
            PureExpr::Final(Arc::new(PureExpr::Var("g".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let mut requires = vec![forall_rule, ground_call];
    let added = instantiate_forall_precondition_rules(&mut requires);
    assert_eq!(added, 0);
}

// ── instantiate_forall_precondition_rules edge case tests ──────────────

#[test]
fn instantiate_forall_precondition_rules_empty_requires_returns_zero() {
    let mut requires: Vec<PureExpr> = vec![];
    let added = instantiate_forall_precondition_rules(&mut requires);
    assert_eq!(added, 0, "empty requires should add nothing");
    assert!(requires.is_empty());
}

#[test]
fn instantiate_forall_precondition_rules_no_matching_ground_calls() {
    let tuple0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple0".to_string(),
        args: vec![],
    };
    // A forall rule for receiver "f" with arg tuple0
    let forall_rule = PureExpr::Forall {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                    method: "postcondition_mut".to_string(),
                    args: vec![
                        tuple0.clone(),
                        PureExpr::Var("st1".to_string(), None),
                        PureExpr::Var("r".to_string(), None),
                    ],
                }),
                BinOp::Implies,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
                    method: "precondition".to_string(),
                    args: vec![tuple0.clone()],
                }),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    // No ground postcondition_mut calls — just the forall rule
    let mut requires = vec![forall_rule];
    let added = instantiate_forall_precondition_rules(&mut requires);
    assert_eq!(added, 0, "no ground calls should produce no instantiations");
    assert_eq!(
        requires.len(),
        1,
        "only the original forall rule should remain"
    );
}

#[test]
fn instantiate_forall_precondition_rules_deduplicates() {
    let tuple0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple0".to_string(),
        args: vec![],
    };
    let forall_rule = PureExpr::Forall {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                    method: "postcondition_mut".to_string(),
                    args: vec![
                        tuple0.clone(),
                        PureExpr::Var("st1".to_string(), None),
                        PureExpr::Var("r".to_string(), None),
                    ],
                }),
                BinOp::Implies,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
                    method: "precondition".to_string(),
                    args: vec![tuple0.clone()],
                }),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    // Two identical ground calls — should only produce one instantiation
    let ground_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            tuple0.clone(),
            PureExpr::Var("s1".to_string(), None),
            PureExpr::Var("r1".to_string(), None),
        ],
    };
    let ground_call_dup = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            tuple0.clone(),
            PureExpr::Var("s1".to_string(), None),
            PureExpr::Var("r2".to_string(), None),
        ],
    };

    let mut requires = vec![forall_rule, ground_call, ground_call_dup];
    let added = instantiate_forall_precondition_rules(&mut requires);
    // Both ground calls match: (f, tuple0, s1) — same recv, same arg, same post_state
    // Wait: s1 is the same post_state but r1/r2 differ. The function extracts (recv, arg[0], arg[1])
    // so arg[1]=st=s1 for both. The dedup is on the grounded precondition expr.
    // grounded = s1.precondition(tuple0) — same for both ground calls. Should dedup to 1.
    assert_eq!(
        added, 1,
        "duplicate ground instantiations should be deduped"
    );
}
