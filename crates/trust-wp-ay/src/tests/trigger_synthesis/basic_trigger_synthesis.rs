// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_expr_mentions_var_basic() {
    assert!(expr_mentions_any_var(&var("x"), &["x".to_string()]));
    assert!(!expr_mentions_any_var(&var("y"), &["x".to_string()]));
    assert!(expr_mentions_any_var(
        &binop(var("x"), trust_wp_core::formula::BinOp::Add, int(1)),
        &["x".to_string()]
    ));
}

#[test]
#[timeout(30000)]
fn test_expr_mentions_var_in_logic_fn_call() {
    let expr = logic_fn_call("f", vec![var("x")]);
    assert!(expr_mentions_any_var(&expr, &["x".to_string()]));
    assert!(!expr_mentions_any_var(&expr, &["y".to_string()]));
}

#[test]
#[timeout(30000)]
fn test_expr_mentions_var_in_method_call() {
    let expr = method_call(var("seq"), "index_logic", vec![var("i")]);
    assert!(expr_mentions_any_var(&expr, &["i".to_string()]));
    assert!(expr_mentions_any_var(&expr, &["seq".to_string()]));
    assert!(!expr_mentions_any_var(&expr, &["j".to_string()]));
}

#[test]
#[timeout(30000)]
fn test_synthesize_single_logic_fn_trigger() {
    // forall<i: Int> 0 <= i && i < len ==> f(i) > 0
    // Should synthesize trigger {:pattern f(i)}
    let body = implies(
        and(le(int(0), var("i")), gt(var("len"), var("i"))),
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
    );
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(triggers.len(), 1, "should synthesize one trigger pattern");
    assert_eq!(triggers[0].len(), 1, "trigger pattern should have one term");
    assert_eq!(
        triggers[0][0],
        logic_fn_call("f", vec![var("i")]),
        "trigger should be f(i)"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_method_call_trigger() {
    // forall<i: Int> 0 <= i && i < seq.len() ==> seq.index_logic(i) > 0
    // Should synthesize trigger {:pattern seq.index_logic(i)}
    let body = implies(
        and(
            le(int(0), var("i")),
            gt(method_call(var("seq"), "len", vec![]), var("i")),
        ),
        gt(
            method_call(var("seq"), "index_logic", vec![var("i")]),
            int(0),
        ),
    );
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(triggers.len(), 1, "should synthesize one trigger pattern");
    assert_eq!(triggers[0].len(), 1);
    // The trigger should be seq.index_logic(i) since it mentions the bound var
    // and is a method call (good specificity)
    match &triggers[0][0] {
        PureExpr::MethodCall { method, .. } => {
            assert_eq!(method, "index_logic");
        }
        _ => panic!("expected MethodCall trigger, got: {:?}", triggers[0][0]),
    }
}

#[test]
#[timeout(30000)]
fn test_synthesize_no_trigger_for_arithmetic_only() {
    // forall<i: Int> i > 0 ==> i + 1 > 0
    // No function calls — should return empty (fall through to ay)
    let body = implies(
        gt(var("i"), int(0)),
        gt(
            binop(var("i"), trust_wp_core::formula::BinOp::Add, int(1)),
            int(0),
        ),
    );
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.is_empty(),
        "arithmetic-only body should produce no triggers"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_multi_trigger_for_two_vars() {
    // forall<i, j> f(i) > 0 && g(j) > 0
    // f(i) covers only i, g(j) covers only j. Should synthesize multi-trigger.
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        gt(logic_fn_call("g", vec![var("j")]), int(0)),
    );
    let vars = vec!["i".to_string(), "j".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(triggers.len(), 1, "should synthesize one multi-trigger");
    assert_eq!(triggers[0].len(), 2, "multi-trigger should have two terms");
}

#[test]
#[timeout(30000)]
fn test_synthesize_prefers_full_coverage_single_trigger() {
    // forall<i> f(i) > 0 && g(i) > 0
    // Both f(i) and g(i) cover i. Both are emitted as alternative trigger
    // patterns so the solver has multiple instantiation opportunities.
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        gt(logic_fn_call("g", vec![var("i")]), int(0)),
    );
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.len() >= 2,
        "both f(i) and g(i) cover i — should emit multiple alternatives: {triggers:?}"
    );
    // Each alternative should be a single-element pattern (not a multi-pattern).
    for (idx, pattern) in triggers.iter().enumerate() {
        assert_eq!(
            pattern.len(),
            1,
            "alternative {idx} should be a single-element pattern, not a multi-pattern"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_collect_nested_quantifier_vars() {
    // forall<i> forall<j> body — both triggerless
    let body = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(gt(var("i"), var("j"))),
        triggers: vec![],
    };
    let (vars, innermost) = collect_nested_quantifier_vars(QuantifierKind::Forall, "i", &body);
    assert_eq!(vars, vec!["i", "j"]);
    assert_eq!(*innermost, gt(var("i"), var("j")));
}

#[test]
#[timeout(30000)]
fn test_collect_nested_stops_at_different_kind() {
    // forall<i> exists<j> body — different kind, should stop
    let body = PureExpr::Exists {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(gt(var("i"), var("j"))),
        triggers: vec![],
    };
    let (vars, _) = collect_nested_quantifier_vars(QuantifierKind::Forall, "i", &body);
    assert_eq!(
        vars,
        vec!["i"],
        "should not collect exists var when kind is forall"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_preferred_over_method_call_at_same_depth() {
    // forall<i> seq.get(i) > 0 && f(i) > 0
    // LogicFnCall gets a -5 bonus, so f(i) should be the first (best-scored)
    // alternative. Both candidates are emitted as alternatives.
    let body = and(
        gt(method_call(var("seq"), "get", vec![var("i")]), int(0)),
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
    );
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.len() >= 2,
        "both seq.get(i) and f(i) cover i — should emit multiple alternatives: {triggers:?}"
    );
    assert_eq!(triggers[0].len(), 1);
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, .. } => {
            assert_eq!(
                name, "f",
                "LogicFnCall should be the first (best-scored) alternative"
            );
        }
        _ => panic!("expected LogicFnCall as first trigger alternative"),
    }
}

#[test]
#[timeout(30000)]
fn test_synthesize_prefers_consequent_trigger_for_generic_deref_like_body() {
    // generic_deref-like shape:
    // inv(y) ==> T::deref_mut.precondition(y)
    //
    // The synthesized trigger should favor the consequent `precondition(y)`
    // over the cheaper antecedent `inv(y)` so E-matching follows the proof
    // goal rather than the guard helper.
    let body = implies(
        logic_fn_call("inv", vec![var("y")]),
        method_call(var("T_deref_mut"), "precondition", vec![var("y")]),
    );
    let vars = vec!["y".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        !triggers.is_empty(),
        "expected at least one synthesized trigger: {triggers:?}"
    );
    assert_eq!(
        triggers[0],
        vec![method_call(
            var("T_deref_mut"),
            "precondition",
            vec![var("y")]
        )],
        "consequent precondition trigger should outrank antecedent inv(y): {triggers:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_finds_trigger_inside_closure_body() {
    // forall<i> |x| f(i) > x
    // The logic fn call f(i) is inside a closure body. collect_trigger_candidates
    // descends into Closure, so it should find f(i) as a trigger candidate.
    let closure_body = gt(logic_fn_call("f", vec![var("i")]), var("x"));
    let body = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(triggers.len(), 1, "should find trigger inside closure body");
    assert_eq!(triggers[0].len(), 1);
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "f");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], var("i"));
        }
        _ => panic!(
            "expected LogicFnCall trigger from inside closure, got: {:?}",
            triggers[0][0]
        ),
    }
}

#[test]
#[timeout(30000)]
fn test_expr_mentions_var_through_closure() {
    // |x| f(i) — should detect that bound var `i` is mentioned inside closure
    let closure = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(logic_fn_call("f", vec![var("i")])),
    };
    assert!(
        expr_mentions_any_var(&closure, &["i".to_string()]),
        "should detect bound var inside closure body"
    );
    assert!(
        !expr_mentions_any_var(&closure, &["z".to_string()]),
        "should not detect unrelated var inside closure body"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_mentions_var_respects_let_shadowing() {
    // let i = 5 in f(i) — the inner `i` is shadowed and should not count
    // as a reference to the quantifier-bound `i`.
    let expr = PureExpr::Let {
        var: "i".to_string(),
        value: Arc::new(int(5)),
        body: Arc::new(logic_fn_call("f", vec![var("i")])),
    };
    assert!(
        !expr_mentions_any_var(&expr, &["i".to_string()]),
        "shadowed let binding should not count as quantifier var reference"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_mentions_var_respects_match_binding_shadowing() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("opt")),
        arms: vec![trust_wp_core::formula::MatchArm {
            pattern: Pattern::Binding("i".to_string()),
            body: logic_fn_call("f", vec![var("i")]),
        }],
    };
    assert!(
        !expr_mentions_any_var(&expr, &["i".to_string()]),
        "match-arm binding should shadow quantifier var with same name"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_ignores_let_shadowed_bound_var() {
    // forall<i> let i = 5 in f(i) > 0
    // The only function call references the shadowed let-bound i, so
    // synthesis should not treat it as coverage for the quantifier i.
    let body = PureExpr::Let {
        var: "i".to_string(),
        value: Arc::new(int(5)),
        body: Arc::new(gt(logic_fn_call("f", vec![var("i")]), int(0))),
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.is_empty(),
        "shadowed let-bound i should not produce trigger coverage"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_ignores_match_shadowed_bound_var() {
    // forall<i> match opt { i => f(i) > 0 }
    // Pattern binding `i` shadows quantifier i in arm body.
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("opt")),
        arms: vec![trust_wp_core::formula::MatchArm {
            pattern: Pattern::Binding("i".to_string()),
            body: gt(logic_fn_call("f", vec![var("i")]), int(0)),
        }],
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.is_empty(),
        "match-bound i should not produce trigger coverage"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_closure_only_body_no_external_fn() {
    // forall<i> |x| i + x > 0
    // Closure body is arithmetic only (no function calls) — should produce no triggers.
    let closure_body = gt(
        binop(var("i"), trust_wp_core::formula::BinOp::Add, var("x")),
        int(0),
    );
    let body = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.is_empty(),
        "arithmetic-only closure body should produce no triggers"
    );
}

#[test]
#[timeout(30000)]
fn test_synthesize_closure_with_nested_quantifier_shadowing() {
    // |x| f(i) > 0 AND forall<j> g(j) > 0
    // Trigger synthesis descends into closures and into nested quantifier
    // bodies (#1118), but g(j) only references inner `j`, not outer `i`.
    let inner_forall = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(gt(logic_fn_call("g", vec![var("j")]), int(0))),
        triggers: vec![],
    };
    let closure_body = and(gt(logic_fn_call("f", vec![var("i")]), int(0)), inner_forall);
    let body = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should find trigger inside closure but outside inner quantifier"
    );
    assert_eq!(triggers[0].len(), 1);
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(
                name, "f",
                "trigger should be f(i), not g(j) from inner quantifier"
            );
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], var("i"));
        }
        _ => panic!(
            "expected LogicFnCall trigger f(i), got: {:?}",
            triggers[0][0]
        ),
    }
}
