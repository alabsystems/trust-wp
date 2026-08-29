// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// The `expr_references_any_var` helper correctly identifies variables.
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_basic() {
    let modified: HashSet<&str> = ["i", "j"].iter().copied().collect();

    // Variable directly in set
    let i_var = PureExpr::Var("i".to_string(), None);
    assert!(
        expr_references_any_var(&i_var, &modified),
        "variable 'i' should be detected in modified set {{i, j}}"
    );

    // Variable not in set
    let n_var = PureExpr::Var("n".to_string(), None);
    assert!(
        !expr_references_any_var(&n_var, &modified),
        "variable 'n' should not be found in modified set {{i, j}}"
    );

    // Nested in BinOp: n >= 0 (no modified vars)
    let n_ge_0 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    assert!(
        !expr_references_any_var(&n_ge_0, &modified),
        "BinOp(n >= 0) should not reference any modified var"
    );

    // Nested in BinOp: i == 0 (modified var)
    let i_eq_0 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );
    assert!(
        expr_references_any_var(&i_eq_0, &modified),
        "BinOp(i == 0) should detect modified var 'i'"
    );

    // Mixed: i + n (has modified var)
    let i_plus_n = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    assert!(
        expr_references_any_var(&i_plus_n, &modified),
        "BinOp(i + n) should detect modified var 'i' even with unmodified 'n'"
    );

    // Literal: no vars
    assert!(
        !expr_references_any_var(&PureExpr::Int(42), &modified),
        "Int literal should never reference any variable"
    );
    assert!(
        !expr_references_any_var(&PureExpr::Bool(true), &modified),
        "Bool literal should never reference any variable"
    );
}

/// Direct `verify_postcondition` negative test: contradictory ensures fails.
///
/// Tests that `verify_postcondition` can reject incorrect postconditions.
/// Uses a trivial single-variable case (invariant says x >= 0, ensures
/// says x < 0) to avoid ay solver timeouts on more complex negative
/// queries (#1466). This provides negative coverage for postcondition
/// verification that the full-pipeline tests cannot due to timeouts.
/// (#1466, #904)
#[test]
#[timeout(30000)]
fn test_postcondition_rejects_contradictory_ensures_direct() {
    // invariant: x >= 0, ensures: x < 0. Directly contradictory.
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(0)),
    )];
    let modified_vars: Vec<&str> = vec!["x"];

    let result = verify_postcondition(
        &invariants,
        None, // no loop condition — simplest case
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition VC should encode without error");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Postcondition should fail: invariant x >= 0 contradicts ensures x < 0. \
         If this passes, postcondition VC is unsound. Got {result:?}"
    );
}

/// Bound variables in Forall/Exists shadow the var set. (#1468)
///
/// `forall(|i| i > 0)` where `i` is a modified var: the `i` inside the
/// forall is a bound variable, not a free reference to the modified var.
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_forall_bound_var_shadowing() {
    let modified: HashSet<&str> = ["i"].iter().copied().collect();

    // forall(|i| i > 0): bound variable `i` should not count as a reference
    // to modified var `i`.
    let forall_expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![],
    };

    assert!(
        !expr_references_any_var(&forall_expr, &modified),
        "forall-bound `i` should NOT be treated as free reference to modified var `i`"
    );

    // Same for Exists
    let exists_expr = PureExpr::Exists {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![],
    };
    assert!(
        !expr_references_any_var(&exists_expr, &modified),
        "exists-bound `i` should NOT be treated as free reference to modified var `i`"
    );

    // Forall with a FREE reference to modified var should still return true
    let forall_with_free = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Var("j".to_string(), None)),
        )),
        triggers: vec![],
    };
    assert!(
        expr_references_any_var(&forall_with_free, &modified),
        "Free `i` inside forall(|j| ...) should still be detected"
    );
}

/// Trigger-only free variables must count as references. (#2116)
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_trigger_only_free_var() {
    let modified: HashSet<&str> = ["i"].iter().copied().collect();

    let forall_trigger_only = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("i".to_string(), None)]],
    };
    assert!(
        expr_references_any_var(&forall_trigger_only, &modified),
        "Free `i` appearing only in a forall trigger should be detected"
    );

    let exists_trigger_only = PureExpr::Exists {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("i".to_string(), None)]],
    };
    assert!(
        expr_references_any_var(&exists_trigger_only, &modified),
        "Free `i` appearing only in an exists trigger should be detected"
    );
}

/// Quantifier binders shadow same-named trigger variables too. (#1468)
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_trigger_bound_var_shadowing() {
    let modified: HashSet<&str> = ["i"].iter().copied().collect();

    let forall_trigger_shadowed = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("i".to_string(), None)]],
    };
    assert!(
        !expr_references_any_var(&forall_trigger_shadowed, &modified),
        "Binder-shadowed `i` in a forall trigger should not count as a free reference"
    );

    let exists_trigger_shadowed = PureExpr::Exists {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("i".to_string(), None)]],
    };
    assert!(
        !expr_references_any_var(&exists_trigger_shadowed, &modified),
        "Binder-shadowed `i` in an exists trigger should not count as a free reference"
    );
}

/// Let-bound variable shadows the var set in body but not in value. (#1468)
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_let_bound_var_shadowing() {
    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    // let x = x + 1; body(x): `x` in value is free, `x` in body is bound
    let let_expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Var("x".to_string(), None)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    // The value references free `x`, so the whole expression references it
    assert!(
        expr_references_any_var(&let_expr, &modified),
        "Free `x` in let value should be detected"
    );

    // let x = 42; body(x): no free `x` anywhere
    let let_no_free = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(42)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        !expr_references_any_var(&let_no_free, &modified),
        "let-bound `x` in body should NOT be treated as free reference"
    );
}

/// Match-arm pattern bindings shadow the var set in arm bodies. (#1468)
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_match_pattern_shadowing() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    // match scrutinee { Binding(x) => x > 0 }
    // The `x` in the arm body is bound by the pattern, not a free reference.
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("x".to_string()),
            body: PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ),
        }],
    };
    assert!(
        !expr_references_any_var(&match_expr, &modified),
        "Pattern-bound `x` in match arm should NOT be treated as free reference"
    );

    // match x { Wildcard => x > 0 }: scrutinee references `x`
    let match_scrutinee_ref = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::Int(0),
        }],
    };
    assert!(
        expr_references_any_var(&match_scrutinee_ref, &modified),
        "Free `x` in scrutinee should be detected"
    );
}

/// Closure parameters shadow the var set in the closure body. (#1468)
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_closure_param_shadowing() {
    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    // |x| x + 1: the `x` is a closure param, not free
    let closure_expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    };
    assert!(
        !expr_references_any_var(&closure_expr, &modified),
        "Closure-param `x` should NOT be treated as free reference"
    );

    // |y| x + y: `x` is free, `y` is bound
    let closure_with_free = PureExpr::Closure {
        params: vec![("y".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        )),
    };
    assert!(
        expr_references_any_var(&closure_with_free, &modified),
        "Free `x` in closure body should be detected"
    );
}

// ── UnOp / MethodCall / LogicFnCall / LetAssume / LetObligation gaps (#2514) ──

/// UnOp(Not, inner) recurses into inner expression.
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_unop_recurse() {
    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    let not_x = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    );
    assert!(
        expr_references_any_var(&not_x, &modified),
        "UnOp(Not, Var(x)) should detect modified var 'x'"
    );

    let not_y = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Var("y".to_string(), None)),
    );
    assert!(
        !expr_references_any_var(&not_y, &modified),
        "UnOp(Not, Var(y)) should not detect 'y' which is not in modified set"
    );
}

/// MethodCall: modified var in receiver or args is detected.
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_method_call() {
    let modified: HashSet<&str> = ["v"].iter().copied().collect();

    let recv_ref = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    assert!(
        expr_references_any_var(&recv_ref, &modified),
        "modified var 'v' in receiver should be detected"
    );

    let arg_ref = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("other".to_string(), None)),
        method: "push".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    assert!(
        expr_references_any_var(&arg_ref, &modified),
        "modified var 'v' in args should be detected"
    );

    let no_ref = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("other".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    assert!(
        !expr_references_any_var(&no_ref, &modified),
        "MethodCall without modified var should return false"
    );
}

/// LogicFnCall: modified var in args is detected.
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_logic_fn_call() {
    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    let with_ref = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Var("x".to_string(), None)],
    };
    assert!(
        expr_references_any_var(&with_ref, &modified),
        "modified var 'x' in LogicFnCall args should be detected"
    );

    let without_ref = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert!(
        !expr_references_any_var(&without_ref, &modified),
        "LogicFnCall without modified var should return false"
    );
}

/// LetAssume: both assumption and body are checked (no shadowing).
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_let_assume() {
    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    let in_assumption = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Var("x".to_string(), None)),
        body: Arc::new(PureExpr::Int(0)),
    };
    assert!(
        expr_references_any_var(&in_assumption, &modified),
        "modified var in LetAssume assumption should be detected"
    );

    let in_body = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        expr_references_any_var(&in_body, &modified),
        "modified var in LetAssume body should be detected"
    );

    let neither = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::Int(0)),
    };
    assert!(
        !expr_references_any_var(&neither, &modified),
        "LetAssume without modified var should return false"
    );
}

/// LetObligation: both obligation and body are checked (no shadowing).
#[test]
#[timeout(30000)]
fn test_expr_references_any_var_let_obligation() {
    let modified: HashSet<&str> = ["x"].iter().copied().collect();

    let in_obligation = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Var("x".to_string(), None)),
        body: Arc::new(PureExpr::Int(0)),
    };
    assert!(
        expr_references_any_var(&in_obligation, &modified),
        "modified var in LetObligation obligation should be detected"
    );

    let in_body = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        expr_references_any_var(&in_body, &modified),
        "modified var in LetObligation body should be detected"
    );
}

// ── Performance regression guards (#2535 F7) ──────────────────────────

/// Guard against O(B × V) from HashSet cloning at every Forall/Exists binder.
///
/// With 100 nested quantifiers and 100 vars in the set, the current code
/// clones a 100-element HashSet 100 times. This test exercises that path
/// with a timeout guard.
#[test]
#[timeout(30000)]
fn perf_deeply_nested_quantifiers_hashset_clone() {
    let n_quantifiers = 100;
    let n_vars = 100;
    let var_set: HashSet<&str> = (0..n_vars)
        .map(|i| {
            // Leak the string to get a &'static str — fine in tests
            Box::leak(format!("v_{i}").into_boxed_str()) as &str
        })
        .collect();

    // Build: forall q_0. forall q_1. ... forall q_99. v_0 + v_1
    // The innermost expression references v_0 and v_1 which are in var_set.
    // None of the quantifier-bound variables (q_*) shadow the search set.
    let inner = add(var("v_0"), var("v_1"));
    let mut expr = inner;
    for i in 0..n_quantifiers {
        expr = forall(&format!("q_{i}"), expr);
    }

    // Each forall level clones the HashSet. Result should be true
    // because v_0 is in var_set.
    assert!(
        expr_references_any_var(&expr, &var_set),
        "v_0 in deeply nested body should be detected through {} quantifier levels",
        n_quantifiers
    );
}
