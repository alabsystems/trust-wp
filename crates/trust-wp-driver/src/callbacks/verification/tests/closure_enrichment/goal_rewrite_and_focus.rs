// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::{
    closure_enrichment::rewrite_trivial_closure_precondition_goal,
    ghost_context::{
        assumption_targets_focus_vars, collect_focus_var_names, select_focus_connected_assumptions,
    },
};

#[test]
fn trivial_closure_precondition_goal_rewrites_direct_receiver() {
    let mut goal = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        }],
    };
    let trivial_receivers = HashSet::from(["c".to_string()]);

    let rewritten = rewrite_trivial_closure_precondition_goal(&mut goal, &trivial_receivers);
    assert!(rewritten, "precondition(c, ..) should be discharged");
    assert_eq!(goal, PureExpr::Bool(true));
}

#[test]
fn trivial_closure_precondition_goal_rewrites_wrapped_receiver() {
    let mut goal = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("c".to_string(), None),
        ))))),
        method: "precondition".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        }],
    };
    let trivial_receivers = HashSet::from(["c".to_string()]);

    let rewritten = rewrite_trivial_closure_precondition_goal(&mut goal, &trivial_receivers);
    assert!(
        rewritten,
        "wrapped receiver should still resolve to closure `c`"
    );
    assert_eq!(goal, PureExpr::Bool(true));
}

#[test]
fn trivial_closure_precondition_goal_rewrites_tuple_receiver() {
    let mut goal = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
        method: "precondition".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        }],
    };
    let trivial_receivers = HashSet::from(["c".to_string()]);

    let rewritten = rewrite_trivial_closure_precondition_goal(&mut goal, &trivial_receivers);
    assert!(
        rewritten,
        "tuple-encoded closure receiver should be discharged when trivial closure set is non-empty"
    );
    assert_eq!(goal, PureExpr::Bool(true));
}

#[test]
fn trivial_closure_precondition_goal_keeps_non_trivial_receiver() {
    let original = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        }],
    };
    let mut goal = original.clone();
    let trivial_receivers = HashSet::from(["c".to_string()]);

    let rewritten = rewrite_trivial_closure_precondition_goal(&mut goal, &trivial_receivers);
    assert!(!rewritten, "receiver `f` is not a concrete trivial closure");
    assert_eq!(goal, original);
}

#[test]
fn collect_focus_var_names_collects_from_contract_and_body() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "g2".to_string(),
            None,
        )))),
    )];
    let body = PureExpr::Var("tmp".to_string(), None);

    let focus = collect_focus_var_names(&requires, &ensures, Some(&body));
    assert!(focus.contains("x"));
    assert!(focus.contains("result"));
    assert!(focus.contains("g2"));
    assert!(focus.contains("tmp"));
}

#[test]
fn assumption_targets_focus_vars_matches_var_and_deref_lhs() {
    let mut focus = HashSet::new();
    focus.insert("x".to_string());
    focus.insert("g2".to_string());

    let var_eq = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );
    let deref_eq = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "g2".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(2)),
    );
    let other_eq = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(3)),
    );

    assert!(assumption_targets_focus_vars(&var_eq, &focus));
    assert!(assumption_targets_focus_vars(&deref_eq, &focus));
    assert!(!assumption_targets_focus_vars(&other_eq, &focus));
}

#[test]
fn assumption_targets_focus_vars_matches_equality_rhs() {
    let mut focus = HashSet::new();
    focus.insert("p1".to_string());

    let rhs_focus = PureExpr::BinOp(
        Arc::new(PureExpr::Var("own1".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("p1".to_string(), None)),
    );

    assert!(assumption_targets_focus_vars(&rhs_focus, &focus));
}

#[test]
fn select_focus_connected_assumptions_keeps_transitive_non_equality() {
    let mut focus = HashSet::new();
    focus.insert("p1".to_string());
    focus.insert("p2".to_string());

    let assumptions = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("own1".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("p1".to_string(), None)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("own2".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("p2".to_string(), None)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("own1".to_string(), None)),
            BinOp::Ne,
            Arc::new(PureExpr::Var("own2".to_string(), None)),
        ),
    ];

    let selected = select_focus_connected_assumptions(&assumptions, &focus);

    assert_eq!(
        selected.len(),
        3,
        "transitive chain should keep all assumptions"
    );
    assert!(selected.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::BinOp(lhs, BinOp::Ne, rhs)
                if matches!(lhs.as_ref(), PureExpr::Var(name, None) if name == "own1")
                    && matches!(rhs.as_ref(), PureExpr::Var(name, None) if name == "own2")
        )
    }));
}

/// Non-equality assumptions containing focus variables should be kept. (#1711)
#[test]
fn assumption_targets_focus_vars_keeps_non_equality_with_focus_var() {
    let mut focus = HashSet::new();
    focus.insert("x".to_string());

    let and_assumption = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        )),
    );
    assert!(assumption_targets_focus_vars(&and_assumption, &focus));

    let implies_assumption = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
    );
    assert!(assumption_targets_focus_vars(&implies_assumption, &focus));

    let forall_assumption = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Var("i".to_string(), None)),
        )),
        triggers: vec![],
    };
    assert!(assumption_targets_focus_vars(&forall_assumption, &focus));
}

/// Non-equality assumptions without focus variables should be dropped. (#1711)
#[test]
fn assumption_targets_focus_vars_drops_non_equality_without_focus_var() {
    let mut focus = HashSet::new();
    focus.insert("x".to_string());

    let and_no_focus = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("z".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        )),
    );
    assert!(!assumption_targets_focus_vars(&and_no_focus, &focus));
}

/// Complex LHS expressions should be checked for focus variable references. (#1711)
#[test]
fn assumption_targets_focus_vars_complex_lhs_with_focus_var() {
    let mut focus = HashSet::new();
    focus.insert("v".to_string());

    let method_eq = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );
    assert!(assumption_targets_focus_vars(&method_eq, &focus));

    let method_eq_no_focus = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("w".to_string(), None)),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );
    assert!(!assumption_targets_focus_vars(&method_eq_no_focus, &focus));

    let logic_fn_eq = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "my_fn".to_string(),
            args: vec![PureExpr::Var("v".to_string(), None)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );
    assert!(assumption_targets_focus_vars(&logic_fn_eq, &focus));
}
