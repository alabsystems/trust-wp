// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- alias substitution unit tests (#1376) ---

/// AC2: Alias substitution NOT applied when the target variable is modified.
/// If `old_n = n` but `n` is in `modified_vars`, substitution must not fire
/// because `n` changes during the loop body — `old_n` captures the pre-loop
/// value, which differs from the post-body `n`.
#[test]
#[timeout(30000)]
fn alias_substitution_skipped_when_target_modified() {
    // Model: old_n = n; loop { n += 1; i += 1; if i >= 10 { break } }
    // modified_vars: [i, n] (n is modified!)
    // Invariant: old_n + i == n (captures the relationship between pre-loop n and current n)
    let requires = vec![n_ge(0)];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("old_n".to_string(), None)),
            BinOp::Add,
            Arc::new(i_var()),
        )),
        BinOp::Eq,
        Arc::new(n_var()),
    )];
    let modified_vars: Vec<&str> = vec!["i", "n"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(Arc::new(i_var()), BinOp::Add, Arc::new(PureExpr::Int(1))),
    );
    body_effect.insert(
        "n".to_string(),
        PureExpr::BinOp(Arc::new(n_var()), BinOp::Add, Arc::new(PureExpr::Int(1))),
    );
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert("old_n".to_string(), NamedBindingValue::untyped(n_var()));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("should encode successfully");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify (old_n = n, i = 0 -> old_n + i == n): got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify (both i and n increment): got {:?}",
        result.preservation
    );
}

/// AC3: Alias substitution NOT applied when the alias variable itself is modified.
#[test]
#[timeout(30000)]
fn alias_substitution_skipped_when_alias_modified() {
    let requires = vec![n_ge(0)];
    let invariants = vec![i_ge_zero()];
    let modified_vars: Vec<&str> = vec!["i", "old_n"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(Arc::new(i_var()), BinOp::Add, Arc::new(PureExpr::Int(1))),
    );
    body_effect.insert(
        "old_n".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("old_n".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert("old_n".to_string(), NamedBindingValue::untyped(n_var()));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("should encode successfully");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify (i = 0 >= 0): got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify (i >= 0 -> i + 1 >= 0): got {:?}",
        result.preservation
    );
}

/// AC4: Invariant `old_v == v` simplifies to trivially true after alias
/// substitution maps `old_v -> v`, becoming `v == v`.
#[test]
#[timeout(30000)]
fn alias_substitution_simplifies_equality_to_true() {
    let requires: Vec<PureExpr> = vec![];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("old_v".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("v".to_string(), None)),
    )];
    let modified_vars: Vec<&str> = vec!["i"];
    let body_effect = i_effect(1);
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert(
        "old_v".to_string(),
        NamedBindingValue::untyped(PureExpr::Var("v".to_string(), None)),
    );

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("should encode successfully");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify (old_v == v becomes v == v after substitution): got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify (v == v is trivially true): got {:?}",
        result.preservation
    );
}
