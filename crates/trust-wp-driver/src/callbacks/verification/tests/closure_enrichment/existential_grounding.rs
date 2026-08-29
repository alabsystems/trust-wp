// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::closure_enrichment::{enrich_existential_body_for_test, ClosureEnsuresEntry};

fn postcondition_mut_call(receiver_name: &str) -> PureExpr {
    postcondition_mut_call_with_receiver(PureExpr::Var(receiver_name.to_string(), None))
}

fn postcondition_mut_call_with_receiver(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("res".to_string(), None),
        ],
    }
}

fn postcondition_once_call_with_receiver(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition_once".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("res".to_string(), None),
        ],
    }
}

fn result_equals(value: i64) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(value)),
    )
}

#[test]
fn enrich_existential_body_uses_matching_receiver_instead_of_first_entry() {
    let mut expr = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call("c2")),
        triggers: vec![],
    };
    let closure_ensures = vec![
        ClosureEnsuresEntry {
            receiver_name: "c1".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(1)],
        },
        ClosureEnsuresEntry {
            receiver_name: "c2".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(2)],
        },
    ];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));

    let expected = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(postcondition_mut_call("c2")),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("res".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(2)),
            )),
        )),
        triggers: vec![],
    };
    assert_eq!(expr, expected);
}

#[test]
fn enrich_existential_body_ambiguous_receiver_fails_closed() {
    let original = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call("c")),
        triggers: vec![],
    };
    let mut expr = original.clone();
    let closure_ensures = vec![
        ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(1)],
        },
        ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(2)],
        },
    ];

    assert!(!enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    assert_eq!(expr, original);
}

#[test]
fn enrich_existential_body_matches_wrapped_postcondition_once_receiver() {
    let receiver = PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "c2".to_string(),
        None,
    )))));
    let mut expr = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_once_call_with_receiver(receiver.clone())),
        triggers: vec![],
    };
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "c2".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(2)],
    }];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));

    let expected = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(postcondition_once_call_with_receiver(receiver)),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("res".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(2)),
            )),
        )),
        triggers: vec![],
    };
    assert_eq!(expr, expected);
}
