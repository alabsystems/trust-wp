// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(5000)]
fn match_expr_bound_var_creates_binding() {
    let bound_vars = &["st1".to_string()];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    let result = try_match_expr(
        &var("st1"),      // body expr (bound var)
        &var("concrete"), // ground expr
        bound_vars,
        &existing,
        &mut new_bindings,
    );

    assert!(result);
    assert_eq!(new_bindings.len(), 1);
    assert_eq!(new_bindings[0].0, "st1");
    assert!(exprs_structurally_equal(
        &new_bindings[0].1,
        &var("concrete")
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_bound_var_existing_binding_matches() {
    let bound_vars = &["st1".to_string()];
    let mut existing = HashMap::new();
    existing.insert("st1".to_string(), var("concrete"));
    let mut new_bindings = Vec::new();

    let result = try_match_expr(
        &var("st1"),
        &var("concrete"),
        bound_vars,
        &existing,
        &mut new_bindings,
    );

    assert!(result);
    assert!(new_bindings.is_empty()); // No new binding needed
}

#[test]
#[timeout(5000)]
fn match_expr_bound_var_existing_binding_conflicts() {
    let bound_vars = &["st1".to_string()];
    let mut existing = HashMap::new();
    existing.insert("st1".to_string(), var("other"));
    let mut new_bindings = Vec::new();

    let result = try_match_expr(
        &var("st1"),
        &var("concrete"),
        bound_vars,
        &existing,
        &mut new_bindings,
    );

    assert!(!result); // Conflict — "st1" already bound to "other"
}

#[test]
#[timeout(5000)]
fn match_expr_bound_var_new_binding_conflict_in_round() {
    let bound_vars = &["st1".to_string()];
    let existing = HashMap::new();
    let mut new_bindings = vec![("st1".to_string(), var("first"))];

    let result = try_match_expr(
        &var("st1"),
        &var("second"), // Different from "first"
        bound_vars,
        &existing,
        &mut new_bindings,
    );

    assert!(!result); // Conflict within same round
}

#[test]
#[timeout(5000)]
fn match_expr_free_var_must_match_by_name() {
    let bound_vars: &[String] = &[];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    // Free var matches same name
    assert!(try_match_expr(
        &var("x"),
        &var("x"),
        bound_vars,
        &existing,
        &mut new_bindings
    ));

    // Free var does not match different name
    assert!(!try_match_expr(
        &var("x"),
        &var("y"),
        bound_vars,
        &existing,
        &mut new_bindings
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_free_var_with_existing_binding() {
    // Free variable "x" with existing binding { "x" -> Int(42) }
    // should match ground Int(42) but not Int(43)
    let bound_vars: &[String] = &[];
    let mut existing = HashMap::new();
    existing.insert("x".to_string(), int(42));
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &var("x"),
        &int(42),
        bound_vars,
        &existing,
        &mut new_bindings
    ));
    assert!(!try_match_expr(
        &var("x"),
        &int(43),
        bound_vars,
        &existing,
        &mut new_bindings
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_logic_fn_call_recursive() {
    let bound_vars = &["st1".to_string()];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    let body = logic_fn_call("resolve", vec![var("st1")]);
    let ground = logic_fn_call("resolve", vec![var("f_final")]);

    let result = try_match_expr(&body, &ground, bound_vars, &existing, &mut new_bindings);

    assert!(result);
    assert_eq!(new_bindings.len(), 1);
    assert_eq!(new_bindings[0].0, "st1");
    assert!(exprs_structurally_equal(
        &new_bindings[0].1,
        &var("f_final")
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_logic_fn_different_names_fails() {
    let bound_vars: &[String] = &[];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    let body = logic_fn_call("resolve", vec![var("x")]);
    let ground = logic_fn_call("other_fn", vec![var("x")]);

    assert!(!try_match_expr(
        &body,
        &ground,
        bound_vars,
        &existing,
        &mut new_bindings
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_method_call_recursive() {
    let bound_vars = &["st1".to_string(), "st2".to_string()];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    let body = method_call(var("st1"), "postcondition_mut", vec![var("st2")]);
    let ground = method_call(var("f"), "postcondition_mut", vec![var("f_final")]);

    let result = try_match_expr(&body, &ground, bound_vars, &existing, &mut new_bindings);

    assert!(result);
    assert_eq!(new_bindings.len(), 2);
    let binding_map: HashMap<_, _> = new_bindings.into_iter().collect();
    assert!(exprs_structurally_equal(
        binding_map.get("st1").unwrap(),
        &var("f")
    ));
    assert!(exprs_structurally_equal(
        binding_map.get("st2").unwrap(),
        &var("f_final")
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_method_call_wrong_method_fails() {
    let bound_vars: &[String] = &[];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    let body = method_call(var("x"), "postcondition_mut", vec![]);
    let ground = method_call(var("x"), "len", vec![]);

    assert!(!try_match_expr(
        &body,
        &ground,
        bound_vars,
        &existing,
        &mut new_bindings
    ));
}

#[test]
#[timeout(5000)]
fn match_expr_structural_fallback() {
    // Non-var, non-method, non-logic-fn expressions fall through to structural eq
    let bound_vars: &[String] = &[];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &int(42),
        &int(42),
        bound_vars,
        &existing,
        &mut new_bindings
    ));
    assert!(!try_match_expr(
        &int(42),
        &int(43),
        bound_vars,
        &existing,
        &mut new_bindings
    ));
}

#[test]
#[timeout(5000)]
fn match_method_call_basic() {
    use super::MethodCallPattern;

    let body_recv = var("st1");
    let body_args = vec![var("st2")];
    let body = MethodCallPattern {
        receiver: &body_recv,
        args: &body_args,
    };

    let ground_recv = var("f");
    let ground_args = vec![var("f_final")];
    let ground = MethodCallPattern {
        receiver: &ground_recv,
        args: &ground_args,
    };

    let bound_vars = &["st1".to_string(), "st2".to_string()];
    let existing = HashMap::new();

    let result = try_match_method_call(&body, &ground, bound_vars, &existing);
    assert!(result.is_some());
    let bindings = result.unwrap();
    let binding_map: HashMap<_, _> = bindings.into_iter().collect();
    assert!(exprs_structurally_equal(
        binding_map.get("st1").unwrap(),
        &var("f")
    ));
    assert!(exprs_structurally_equal(
        binding_map.get("st2").unwrap(),
        &var("f_final")
    ));
}

#[test]
#[timeout(5000)]
fn match_method_call_arg_count_mismatch() {
    use super::MethodCallPattern;

    let body_recv = var("st1");
    let body_args = vec![var("st2"), var("st3")];
    let body = MethodCallPattern {
        receiver: &body_recv,
        args: &body_args,
    };

    let ground_recv = var("f");
    let ground_args = vec![var("f_final")];
    let ground = MethodCallPattern {
        receiver: &ground_recv,
        args: &ground_args,
    };

    let result = try_match_method_call(
        &body,
        &ground,
        &["st1".to_string(), "st2".to_string()],
        &HashMap::new(),
    );
    assert!(result.is_none());
}

#[test]
#[timeout(5000)]
fn match_resolve_call_binds_var() {
    let bound_vars = &["st1".to_string()];
    let existing = HashMap::new();

    let result = try_match_resolve_call(&var("st1"), &var("f_final"), bound_vars, &existing);
    assert!(result.is_some());
    let bindings = result.unwrap();
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "st1");
    assert!(exprs_structurally_equal(&bindings[0].1, &var("f_final")));
}

#[test]
#[timeout(5000)]
fn match_resolve_call_no_match() {
    let bound_vars: &[String] = &[];
    let existing = HashMap::new();

    // Free var "x" vs "y" — no match
    let result = try_match_resolve_call(&var("x"), &var("y"), bound_vars, &existing);
    assert!(result.is_none());
}

#[test]
#[timeout(5000)]
fn flatten_single_exists() {
    let expr = exists("st1", gt(var("st1"), int(0)));
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, body) = result.unwrap();
    assert_eq!(vars, vec!["st1".to_string()]);
    assert!(exprs_structurally_equal(body, &gt(var("st1"), int(0))));
}

#[test]
#[timeout(5000)]
fn flatten_nested_exists() {
    let expr = exists("st1", exists("st2", and(var("st1"), var("st2"))));
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, body) = result.unwrap();
    assert_eq!(vars, vec!["st1".to_string(), "st2".to_string()]);
    assert!(exprs_structurally_equal(body, &and(var("st1"), var("st2"))));
}

#[test]
#[timeout(5000)]
fn flatten_triple_nested_exists() {
    let expr = exists(
        "st1",
        exists(
            "st2",
            exists("r", and(var("st1"), and(var("st2"), var("r")))),
        ),
    );
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, _body) = result.unwrap();
    assert_eq!(
        vars,
        vec!["st1".to_string(), "st2".to_string(), "r".to_string()]
    );
}

#[test]
#[timeout(5000)]
fn flatten_stops_at_triggered_exists() {
    // Exists with triggers should NOT be flattened — E-matching handles it
    let expr = exists_with_triggers("st1", exists("st2", var("st2")), vec![vec![var("st1")]]);
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_none()); // First exists has triggers, stops immediately
}

#[test]
#[timeout(5000)]
fn flatten_non_exists_returns_none() {
    let expr = forall("x", var("x"));
    assert!(flatten_nested_existentials(&expr).is_none());

    let expr2 = var("x");
    assert!(flatten_nested_existentials(&expr2).is_none());
}

#[test]
#[timeout(5000)]
fn flatten_stops_at_inner_triggered_exists() {
    // Outer exists has no triggers (collected), inner has triggers (stops)
    let inner = exists_with_triggers("st2", var("st2"), vec![vec![var("st2")]]);
    let expr = exists("st1", inner);
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, body) = result.unwrap();
    assert_eq!(vars, vec!["st1".to_string()]);
    // Body should be the triggered inner exists (not flattened further)
    match body {
        PureExpr::Exists { var, triggers, .. } => {
            assert_eq!(var, "st2");
            assert!(!triggers.is_empty());
        }
        _ => panic!("expected inner Exists, got {body:?}"),
    }
}

#[test]
#[timeout(5000)]
fn collect_body_postcondition_mut_recurses_into_matching_children() {
    let nested_receiver = method_call(var("f"), "postcondition_mut", vec![var("f_final")]);
    let nested_arg = method_call(var("g"), "postcondition_mut", vec![var("g_final")]);
    let body = method_call(
        nested_receiver.clone(),
        "postcondition_mut",
        vec![nested_arg.clone()],
    );

    let calls = collect_body_postcondition_mut_calls(
        &body,
        &[
            "f".to_string(),
            "f_final".to_string(),
            "g".to_string(),
            "g_final".to_string(),
        ],
    );

    assert_eq!(calls.len(), 3);
    assert!(exprs_structurally_equal(
        calls[0].receiver,
        &nested_receiver
    ));
    assert!(exprs_structurally_equal(calls[1].receiver, &var("f")));
    assert!(exprs_structurally_equal(calls[2].receiver, &var("g")));
}

#[test]
#[timeout(5000)]
fn collect_body_postcondition_mut_skips_shadowed_forall_binding() {
    let body = forall(
        "st",
        method_call(var("f"), "postcondition_mut", vec![var("st")]),
    );

    let calls = collect_body_postcondition_mut_calls(&body, &["st".to_string()]);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_body_postcondition_mut_collects_let_value_before_shadowing_body() {
    let visible = method_call(var("f"), "postcondition_mut", vec![var("st")]);
    let shadowed = method_call(var("g"), "postcondition_mut", vec![var("st")]);
    let body = PureExpr::Let {
        var: "st".to_string(),
        value: Arc::new(visible.clone()),
        body: Arc::new(shadowed),
    };

    let calls = collect_body_postcondition_mut_calls(&body, &["st".to_string()]);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0].receiver, &var("f")));
}

#[test]
#[timeout(5000)]
fn collect_body_postcondition_mut_skips_shadowed_match_arm_binding() {
    let body = match_expr(
        var("opt"),
        vec![(
            Pattern::Binding("st".to_string()),
            method_call(var("f"), "postcondition_mut", vec![var("st")]),
        )],
    );

    let calls = collect_body_postcondition_mut_calls(&body, &["st".to_string()]);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_body_postcondition_mut_skips_shadowed_closure_param() {
    let body = PureExpr::Closure {
        params: vec![("st".to_string(), None)],
        body: Arc::new(method_call(var("f"), "postcondition_mut", vec![var("st")])),
    };

    let calls = collect_body_postcondition_mut_calls(&body, &["st".to_string()]);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_from_requires() {
    // requires: f.postcondition_mut(f_final)
    let reqs = [method_call(
        var("f"),
        "postcondition_mut",
        vec![var("f_final")],
    )];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0].receiver, &var("f")));
    assert_eq!(calls[0].args.len(), 1);
    assert!(exprs_structurally_equal(&calls[0].args[0], &var("f_final")));
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_skips_quantified() {
    // requires: forall x. x.postcondition_mut(x_final) — NOT ground
    let reqs = [forall(
        "x",
        method_call(var("x"), "postcondition_mut", vec![var("x_final")]),
    )];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_multiple_requires() {
    let reqs = [
        method_call(var("f"), "postcondition_mut", vec![var("f_final")]),
        method_call(var("g"), "postcondition_mut", vec![var("g_final")]),
    ];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert_eq!(calls.len(), 2);
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_ignores_other_methods() {
    let reqs = [method_call(var("v"), "len", vec![])];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_nested_in_binop() {
    // requires: f.postcondition_mut(f_final) && g > 0
    let reqs = [and(
        method_call(var("f"), "postcondition_mut", vec![var("f_final")]),
        gt(var("g"), int(0)),
    )];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert_eq!(calls.len(), 1);
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_skips_match_arm_binding() {
    let reqs = [match_expr(
        var("opt"),
        vec![(
            Pattern::Binding("st".to_string()),
            method_call(var("f"), "postcondition_mut", vec![var("st")]),
        )],
    )];

    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_skips_let_binding() {
    let reqs = [let_bind(
        "st",
        var("input"),
        method_call(var("f"), "postcondition_mut", vec![var("st")]),
    )];

    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_skips_closure_param() {
    let reqs = [PureExpr::Closure {
        params: vec![("st".to_string(), None)],
        body: Arc::new(method_call(var("f"), "postcondition_mut", vec![var("st")])),
    }];

    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_body_resolve_skips_shadowed_match_arm_binding() {
    let body = match_expr(
        var("opt"),
        vec![(Pattern::Binding("st".to_string()), resolve_call(var("st")))],
    );

    let calls = collect_body_resolve_calls(&body, &["st".to_string()]);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_body_resolve_collects_non_shadowed_match_arm_reference() {
    let body = match_expr(
        var("opt"),
        vec![(
            Pattern::Binding("local".to_string()),
            resolve_call(var("st")),
        )],
    );

    let calls = collect_body_resolve_calls(&body, &["st".to_string()]);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0], &var("st")));
}

#[test]
#[timeout(5000)]
fn collect_body_resolve_does_not_recurse_into_nested_resolve_arg() {
    let body = resolve_call(resolve_call(var("st")));

    let calls = collect_body_resolve_calls(&body, &["st".to_string()]);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0], &resolve_call(var("st"))));
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_from_requires() {
    let reqs = [resolve_call(var("f_final"))];
    let calls = collect_ground_resolve_calls(&reqs);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0], &var("f_final")));
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_skips_quantified() {
    let reqs = [forall("x", resolve_call(var("x")))];
    let calls = collect_ground_resolve_calls(&reqs);
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_nested_in_and() {
    let reqs = [and(resolve_call(var("f")), gt(var("x"), int(0)))];
    let calls = collect_ground_resolve_calls(&reqs);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0], &var("f")));
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_multiple() {
    let reqs = [resolve_call(var("f_final")), resolve_call(var("g_final"))];
    let calls = collect_ground_resolve_calls(&reqs);
    assert_eq!(calls.len(), 2);
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_does_not_recurse_into_nested_resolve_arg() {
    let reqs = [resolve_call(resolve_call(var("f_final")))];

    let calls = collect_ground_resolve_calls(&reqs);
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(
        calls[0],
        &resolve_call(var("f_final"))
    ));
}

// ── _from_refs variants (#970): body-local LetAssume assumptions ─────────
// Body-local assumptions arrive as `&[&PureExpr]` (slice of references)
// rather than `&[PureExpr]`, because the solver tail collects them by
// reference from the return-expression tree. The `_from_refs` collectors
// share the same binder-aware walker as the precondition collectors.

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_from_refs_finds_call() {
    let req = method_call(var("f"), "postcondition_mut", vec![var("f_final")]);
    let refs: Vec<&PureExpr> = vec![&req];
    let calls = crate::verify::eager_instantiation::collectors::collect_ground_postcondition_mut_calls_from_refs(
        &refs,
    );
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0].receiver, &var("f")));
    assert_eq!(calls[0].args.len(), 1);
    assert!(exprs_structurally_equal(&calls[0].args[0], &var("f_final")));
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_from_refs_skips_quantified() {
    let req = forall(
        "x",
        method_call(var("x"), "postcondition_mut", vec![var("x_final")]),
    );
    let refs: Vec<&PureExpr> = vec![&req];
    let calls = crate::verify::eager_instantiation::collectors::collect_ground_postcondition_mut_calls_from_refs(
        &refs,
    );
    assert!(calls.is_empty());
}

#[test]
#[timeout(5000)]
fn collect_ground_postcondition_mut_from_refs_aggregates_multiple_assumptions() {
    let a = method_call(var("f"), "postcondition_mut", vec![var("f_final")]);
    let b = method_call(var("g"), "postcondition_mut", vec![var("g_final")]);
    let refs: Vec<&PureExpr> = vec![&a, &b];
    let calls = crate::verify::eager_instantiation::collectors::collect_ground_postcondition_mut_calls_from_refs(
        &refs,
    );
    assert_eq!(calls.len(), 2);
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_from_refs_finds_call() {
    let req = resolve_call(var("f_final"));
    let refs: Vec<&PureExpr> = vec![&req];
    let calls =
        crate::verify::eager_instantiation::collectors::collect_ground_resolve_calls_from_refs(
            &refs,
        );
    assert_eq!(calls.len(), 1);
    assert!(exprs_structurally_equal(calls[0], &var("f_final")));
}

#[test]
#[timeout(5000)]
fn collect_ground_resolve_from_refs_skips_quantified() {
    let req = forall("x", resolve_call(var("x")));
    let refs: Vec<&PureExpr> = vec![&req];
    let calls =
        crate::verify::eager_instantiation::collectors::collect_ground_resolve_calls_from_refs(
            &refs,
        );
    assert!(calls.is_empty());
}
