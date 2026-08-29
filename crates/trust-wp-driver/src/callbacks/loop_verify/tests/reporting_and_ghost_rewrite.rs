// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::ExprSort;

use super::{
    filter_post_loop_borrow_resolution_vars, is_trust_wp_ghost_def_path,
    rewrite_loop_ensures_for_ghost_return, worst_result, BinOp, PureExpr, UnknownReason,
    VerificationResult,
};

#[test]
fn test_worst_result_preserves_unknown_reason() {
    let result = worst_result(
        VerificationResult::Unknown(UnknownReason::Timeout),
        VerificationResult::Verified(None),
    );

    match result {
        VerificationResult::Unknown(reason) => {
            assert!(
                matches!(reason, UnknownReason::Timeout),
                "expected Timeout, got {reason:?}"
            );
        }
        other => panic!("expected Unknown(Timeout), got {other:?}"),
    }
}

#[test]
fn test_worst_result_failed_overrides_unknown() {
    let result = worst_result(
        VerificationResult::Unknown(UnknownReason::Timeout),
        VerificationResult::Failed(trust_wp_ay::Counterexample {
            values: Vec::new(),
            violated_postcondition: None,
        }),
    );
    assert!(matches!(result, VerificationResult::Failed(_)));
}

#[test]
fn test_worst_result_merges_unknown_reason_from_second_operand() {
    let result = worst_result(
        VerificationResult::Unknown(UnknownReason::Unspecified),
        VerificationResult::Unknown(UnknownReason::Incomplete),
    );

    match result {
        VerificationResult::Unknown(reason) => {
            assert!(
                matches!(reason, UnknownReason::Incomplete),
                "expected Incomplete, got {reason:?}"
            );
        }
        other => panic!("expected Unknown(Incomplete), got {other:?}"),
    }
}

#[test]
fn test_is_trust_wp_ghost_def_path_requires_exact_match() {
    assert!(is_trust_wp_ghost_def_path(
        "trust_wp_std",
        "trust_wp_std::ghost::Ghost"
    ));
    assert!(!is_trust_wp_ghost_def_path(
        "user_crate",
        "user_crate::ghost::Ghost"
    ));
    assert!(!is_trust_wp_ghost_def_path(
        "user_crate",
        "user_crate::Ghost"
    ));
}

#[test]
fn test_is_trust_wp_ghost_def_path_cross_crate_reexport() {
    // trust_wp_std re-exports creusot_std::Ghost, so tcx reports
    // crate="trust_wp_std" but path="creusot_std::Ghost".
    assert!(is_trust_wp_ghost_def_path(
        "trust_wp_std",
        "creusot_std::Ghost"
    ));
    assert!(is_trust_wp_ghost_def_path(
        "trust_wp_std",
        "trust_wp_std::Ghost"
    ));
    assert!(is_trust_wp_ghost_def_path(
        "creusot_std",
        "creusot_std::ghost::Ghost"
    ));
    assert!(is_trust_wp_ghost_def_path(
        "creusot_std",
        "creusot_std::Ghost"
    ));
}

#[test]
fn test_non_trust_wp_ghost_path_does_not_trigger_rewrite() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "result".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    )];
    let return_expr = PureExpr::Var("ret".to_string(), None);

    let rewritten = rewrite_loop_ensures_for_ghost_return(
        &ensures,
        is_trust_wp_ghost_def_path("my_crate", "my_crate::ghost::Ghost"),
        Some(&return_expr),
    );
    assert_eq!(rewritten, ensures);
}

#[test]
fn test_trust_wp_ghost_path_triggers_rewrite() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "result".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    )];
    let return_expr = PureExpr::Var("ret".to_string(), None);

    let rewritten = rewrite_loop_ensures_for_ghost_return(
        &ensures,
        is_trust_wp_ghost_def_path("trust_wp_std", "trust_wp_std::ghost::Ghost"),
        Some(&return_expr),
    );
    let expected = vec![PureExpr::BinOp(
        Arc::new(return_expr.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    )];
    assert_eq!(rewritten, expected);
}

#[test]
fn test_ghost_rewrite_preserves_quantifier_var_sort_and_triggers() {
    let ensures = vec![PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "result".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
        )),
        triggers: vec![vec![PureExpr::Deref(Arc::new(PureExpr::Var(
            "result".to_string(),
            None,
        )))]],
    }];
    let return_expr = PureExpr::Var("ret".to_string(), Some(ExprSort::Int));

    let rewritten = rewrite_loop_ensures_for_ghost_return(&ensures, true, Some(&return_expr));

    assert_eq!(
        rewritten,
        vec![PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(return_expr.clone()),
                BinOp::Eq,
                Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            )),
            triggers: vec![vec![return_expr]],
        }]
    );
}

#[test]
fn test_creusot_contracts_ghost_path_triggers_rewrite() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "result".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    )];
    let return_expr = PureExpr::Var("ret".to_string(), None);

    // creusot_contracts::Ghost should trigger the ghost return rewrite
    let rewritten = rewrite_loop_ensures_for_ghost_return(
        &ensures,
        is_trust_wp_ghost_def_path("creusot_contracts", "creusot_contracts::ghost::Ghost"),
        Some(&return_expr),
    );
    let expected = vec![PureExpr::BinOp(
        Arc::new(return_expr.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    )];
    assert_eq!(rewritten, expected);
}

#[test]
fn test_creusot_contracts_ghost_short_path_triggers_rewrite() {
    assert!(is_trust_wp_ghost_def_path(
        "creusot_contracts",
        "creusot_contracts::Ghost"
    ));
    assert!(is_trust_wp_ghost_def_path(
        "creusot_contracts",
        "ghost::Ghost"
    ));
    assert!(is_trust_wp_ghost_def_path("creusot_contracts", "Ghost"));
}

#[test]
fn filter_post_loop_borrow_resolution_vars_drops_mutated_vars() {
    let mut deref_effects = std::collections::HashMap::new();
    deref_effects.insert("v".to_string(), PureExpr::Int(1));
    deref_effects.insert("w".to_string(), PureExpr::Int(2));

    let post_loop_writes = std::collections::HashSet::from(["v".to_string()]);
    let filtered = filter_post_loop_borrow_resolution_vars(deref_effects, &post_loop_writes);

    assert!(
        !filtered.contains_key("v"),
        "vars mutated after loop must be excluded from loop-local borrow resolution"
    );
    assert!(
        filtered.contains_key("w"),
        "unmodified vars must keep loop-local borrow resolution"
    );
}

#[test]
fn filter_post_loop_borrow_resolution_vars_keeps_all_when_empty() {
    let mut deref_effects = std::collections::HashMap::new();
    deref_effects.insert("v".to_string(), PureExpr::Int(1));
    deref_effects.insert("w".to_string(), PureExpr::Int(2));

    let filtered = filter_post_loop_borrow_resolution_vars(
        deref_effects.clone(),
        &std::collections::HashSet::default(),
    );
    assert_eq!(filtered, deref_effects);
}
