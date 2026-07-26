// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `PureExpr::substitute*` methods in `substitute.rs` (1137 LOC).
//!
//! Coverage gap: the 4 pub substitute methods (`substitute`, `substitute_no_tuple_beta`,
//! `substitute_capture_avoiding`, `substitute_filtered`) have only 2 external test
//! references (in `substitute_nullary_logic_call.rs`). These tests cover:
//! - Simple variable substitution
//! - Binding-aware shadowing (Forall, Exists, Let, Match, Closure)
//! - Deref key substitution (`*x` → replacement)
//! - Tuple beta-reduction vs no-beta-reduction
//! - Capture-avoiding alpha-renaming
//! - Filtered substitution
//! - Nullary logic function substitution

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{
    BinOp, CaptureAvoidingSubstOptions, FloatBits, MatchArm, Pattern, PureExpr, UnOp,
};

fn mk_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

fn subs(pairs: &[(&str, PureExpr)]) -> HashMap<String, PureExpr> {
    pairs
        .iter()
        .map(|(k, v)| (k.to_string(), v.clone()))
        .collect()
}

// === substitute: simple cases ===

#[test]
fn substitute_var_replaced() {
    let expr = mk_var("x");
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, int(42));
}

#[test]
fn substitute_var_not_in_map_unchanged() {
    let expr = mk_var("y");
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, mk_var("y"));
}

#[test]
fn substitute_literal_unchanged() {
    let expr = int(7);
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, int(7));
}

#[test]
fn substitute_bool_unchanged() {
    let expr = PureExpr::Bool(true);
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, PureExpr::Bool(true));
}

#[test]
fn substitute_binop_both_sides() {
    let expr = PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("y")));
    let result = expr.substitute(&subs(&[("x", int(1)), ("y", int(2))]));
    assert_eq!(
        result,
        PureExpr::BinOp(Arc::new(int(1)), BinOp::Add, Arc::new(int(2)))
    );
}

#[test]
fn substitute_empty_map_unchanged() {
    let expr = mk_var("x");
    let result = expr.substitute(&HashMap::new());
    assert_eq!(result, mk_var("x"));
}

// === substitute: wrapper types ===

#[test]
fn substitute_in_deref() {
    let expr = PureExpr::Deref(Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", mk_var("y"))]));
    assert_eq!(result, PureExpr::Deref(Arc::new(mk_var("y"))));
}

#[test]
fn substitute_in_final() {
    let expr = PureExpr::Final(Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", mk_var("y"))]));
    assert_eq!(result, PureExpr::Final(Arc::new(mk_var("y"))));
}

#[test]
fn substitute_in_view() {
    let expr = PureExpr::View(Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", mk_var("y"))]));
    assert_eq!(result, PureExpr::View(Arc::new(mk_var("y"))));
}

#[test]
fn substitute_in_old() {
    let expr = PureExpr::Old(Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", mk_var("y"))]));
    assert_eq!(result, PureExpr::Old(Arc::new(mk_var("y"))));
}

// === substitute: deref key shortcut ===

#[test]
fn substitute_deref_key_replaces_deref_var() {
    // *x with substitution key "*x" → replacement
    let expr = PureExpr::Deref(Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("*x", int(99))]));
    assert_eq!(result, int(99));
}

#[test]
fn substitute_deref_key_non_var_inner_skips() {
    // *(x + 1) does NOT trigger deref key shortcut
    let inner = PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(1)));
    let expr = PureExpr::Deref(Arc::new(inner.clone()));
    let result = expr.substitute(&subs(&[("*x", int(99))]));
    assert_eq!(result, PureExpr::Deref(Arc::new(inner)));
}

// === substitute: binding-aware shadowing ===

#[test]
fn substitute_forall_shadows_bound_var() {
    // forall<x> x+y with subs {x→1, y→2}: x is shadowed, y is replaced
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![mk_var("x"), mk_var("y")],
        }]],
    };
    let result = expr.substitute(&subs(&[("x", int(1)), ("y", int(2))]));
    match &result {
        PureExpr::Forall { body, triggers, .. } => {
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(2)))
            );
            assert_eq!(
                triggers,
                &vec![vec![PureExpr::LogicFnCall {
                    name: "f".to_string(),
                    args: vec![mk_var("x"), int(2)],
                }]]
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn substitute_exists_shadows_bound_var() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(mk_var("x")),
        triggers: vec![],
    };
    let result = expr.substitute(&subs(&[("x", int(1))]));
    match &result {
        PureExpr::Exists { body, .. } => {
            assert_eq!(body.as_ref(), &mk_var("x"));
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn substitute_let_shadows_bound_var() {
    // let x = y; x+z with subs {x→99, y→1, z→2}: x shadowed in body, y replaced in value
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(mk_var("y")),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("z")),
        )),
    };
    let result = expr.substitute(&subs(&[("x", int(99)), ("y", int(1)), ("z", int(2))]));
    match &result {
        PureExpr::Let { value, body, .. } => {
            assert_eq!(value.as_ref(), &int(1));
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(2)))
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn substitute_match_shadows_pattern_bindings() {
    // match s { Some(x) => x+y } with subs {s→t, x→1, y→2}
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("s")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("x".to_string()))),
            },
            body: PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("y"))),
        }],
    };
    let result = expr.substitute(&subs(&[("s", mk_var("t")), ("x", int(1)), ("y", int(2))]));
    match &result {
        PureExpr::Match { scrutinee, arms } => {
            assert_eq!(scrutinee.as_ref(), &mk_var("t"));
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(2)))
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn substitute_closure_shadows_params() {
    // |x| x+y with subs {x→1, y→2}
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
    };
    let result = expr.substitute(&subs(&[("x", int(1)), ("y", int(2))]));
    match &result {
        PureExpr::Closure { body, .. } => {
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(2)))
            );
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

// === substitute: method calls, logic fns ===

#[test]
fn substitute_in_method_call() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(mk_var("v")),
        method: "len".to_string(),
        args: vec![mk_var("x")],
    };
    let result = expr.substitute(&subs(&[("v", mk_var("w")), ("x", int(1))]));
    match &result {
        PureExpr::MethodCall { receiver, args, .. } => {
            assert_eq!(receiver.as_ref(), &mk_var("w"));
            assert_eq!(args, &[int(1)]);
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

#[test]
fn substitute_nullary_logic_fn_as_variable() {
    // LogicFnCall{name:"x", args:[]} acts like a variable when substituted
    let expr = PureExpr::LogicFnCall {
        name: "x".to_string(),
        args: vec![],
    };
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, int(42));
}

#[test]
fn substitute_nonary_logic_fn_not_substituted() {
    // LogicFnCall with args does NOT get variable-like substitution
    let expr = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![mk_var("x")],
    };
    let result = expr.substitute(&subs(&[("f", int(99)), ("x", int(1))]));
    // f is NOT replaced (has args), but x in args IS replaced
    match &result {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "f");
            assert_eq!(args, &[int(1)]);
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

// === substitute: tuple beta-reduction ===

#[test]
fn substitute_tuple_beta_reduces() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };
    // tuple_get_0(tuple2(a, b)) → a
    let tuple_ctor = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![int(10), int(20)],
    };
    let get_0 = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![mk_var("t")],
    };
    let result = get_0.substitute(&subs(&[("t", tuple_ctor)]));
    assert_eq!(result, int(10));
}

// === substitute_no_tuple_beta ===

#[test]
fn substitute_no_tuple_beta_skips_reduction() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };
    let tuple_ctor = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![int(10), int(20)],
    };
    let get_0 = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![mk_var("t")],
    };
    let result = get_0.substitute_no_tuple_beta(&subs(&[("t", tuple_ctor.clone())]));
    // Should NOT beta-reduce — remains tuple_get_0(tuple2(10, 20))
    match &result {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(*name, tuple_field_logic_fn_name(0));
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], tuple_ctor);
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

// === substitute_filtered ===

#[test]
fn substitute_filtered_only_replaces_allowed_vars() {
    let expr = PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("y")));
    let filter: HashSet<&str> = ["x"].into_iter().collect();
    let result = expr.substitute_filtered(&filter, &subs(&[("x", int(1)), ("y", int(2))]));
    // x is in filter → replaced. y is NOT in filter → unchanged.
    assert_eq!(
        result,
        PureExpr::BinOp(Arc::new(int(1)), BinOp::Add, Arc::new(mk_var("y")))
    );
}

#[test]
fn substitute_filtered_empty_filter_no_replacements() {
    let expr = mk_var("x");
    let filter: HashSet<&str> = HashSet::new();
    let result = expr.substitute_filtered(&filter, &subs(&[("x", int(1))]));
    assert_eq!(result, mk_var("x"));
}

#[test]
fn substitute_filtered_deref_key_respects_filter() {
    // *x with filter not containing "x" → deref key NOT applied
    let expr = PureExpr::Deref(Arc::new(mk_var("x")));
    let filter: HashSet<&str> = HashSet::new();
    let result = expr.substitute_filtered(&filter, &subs(&[("*x", int(99))]));
    assert_eq!(result, PureExpr::Deref(Arc::new(mk_var("x"))));
}

// === substitute_capture_avoiding ===

#[test]
fn capture_avoiding_simple_substitution() {
    let expr = mk_var("x");
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("x", int(42))]), &opts);
    assert_eq!(result, int(42));
}

#[test]
fn capture_avoiding_renames_to_avoid_capture() {
    // forall<x> (x + y) with triggers [p(x, y)] and subs {y → x}
    // Without capture avoidance: forall<x> (x + x) — WRONG (captures y→x)
    // With capture avoidance: forall<x_α0> (x_α0 + x) with trigger [p(x_α0, x)]
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "p".to_string(),
            args: vec![mk_var("x"), mk_var("y")],
        }]],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts);
    match &result {
        PureExpr::Forall {
            var,
            body,
            triggers,
            ..
        } => {
            // Bound var should be renamed (not "x")
            assert_ne!(var, "x", "binder should be alpha-renamed to avoid capture");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var(var)), BinOp::Add, Arc::new(mk_var("x")))
            );
            assert_eq!(
                triggers,
                &vec![vec![PureExpr::LogicFnCall {
                    name: "p".to_string(),
                    args: vec![mk_var(var), mk_var("x")],
                }]]
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_no_capture_no_rename() {
    // forall<x> (x + y) with subs {y → z} — no capture risk
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts);
    match &result {
        PureExpr::Forall { var, body, .. } => {
            assert_eq!(var, "x", "no rename needed — no capture risk");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("z")))
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_depth_limit_stops_recursion() {
    // depth_limit_exceeded checks depth > limit, so depth_limit=2 allows depths 0,1,2
    // but stops at depth 3. With 3 levels of nesting, the innermost x at depth 3 is NOT reached.
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(mk_var("x")),
                BinOp::Add,
                Arc::new(int(1)),
            )),
            BinOp::Add,
            Arc::new(int(2)),
        )),
        BinOp::Add,
        Arc::new(mk_var("x")),
    );
    let opts_deep = CaptureAvoidingSubstOptions { depth_limit: None };
    let result_deep = expr.substitute_capture_avoiding(&subs(&[("x", int(99))]), &opts_deep);
    // Without limit, both x's are replaced
    let expected_deep = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(int(99)),
                BinOp::Add,
                Arc::new(int(1)),
            )),
            BinOp::Add,
            Arc::new(int(2)),
        )),
        BinOp::Add,
        Arc::new(int(99)),
    );
    assert_eq!(result_deep, expected_deep);

    // With depth_limit=2, depth 3 (innermost x) is not reached
    let opts_shallow = CaptureAvoidingSubstOptions {
        depth_limit: Some(2),
    };
    let result_shallow = expr.substitute_capture_avoiding(&subs(&[("x", int(99))]), &opts_shallow);
    // Outer x (depth 1) IS replaced, inner x (depth 3) is NOT
    assert_ne!(
        result_shallow, result_deep,
        "depth limit should prevent some replacements"
    );
    // But the outer x should still be replaced
    assert_ne!(result_shallow, expr, "outer x should still be replaced");
}

// === substitute: LetAssume/LetObligation ===

#[test]
fn substitute_in_let_assume() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(mk_var("x")),
        body: Arc::new(mk_var("y")),
    };
    let result = expr.substitute(&subs(&[("x", int(1)), ("y", int(2))]));
    assert_eq!(
        result,
        PureExpr::LetAssume {
            assumption: Arc::new(int(1)),
            body: Arc::new(int(2)),
        }
    );
}

#[test]
fn substitute_in_let_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(mk_var("x")),
        body: Arc::new(mk_var("y")),
    };
    let result = expr.substitute(&subs(&[("x", int(1)), ("y", int(2))]));
    assert_eq!(
        result,
        PureExpr::LetObligation {
            obligation: Arc::new(int(1)),
            body: Arc::new(int(2)),
        }
    );
}

// === substitute: UnOp ===

#[test]
fn substitute_in_unop_not() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", PureExpr::Bool(true))]));
    assert_eq!(
        result,
        PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Bool(true)))
    );
}

#[test]
fn substitute_in_unop_neg() {
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", int(5))]));
    assert_eq!(result, PureExpr::UnOp(UnOp::Neg, Arc::new(int(5))));
}

#[test]
fn substitute_unop_no_match_unchanged() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(mk_var("z")));
    let result = expr.substitute(&subs(&[("x", int(1))]));
    assert_eq!(result, expr);
}

// === substitute: Float literal ===

#[test]
fn substitute_float_unchanged() {
    let expr = PureExpr::Float(FloatBits(314_159));
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, PureExpr::Float(FloatBits(314_159)));
}

// === substitute: Ite ===

#[test]
fn substitute_in_ite_all_branches() {
    let expr = PureExpr::Ite(
        Arc::new(mk_var("c")),
        Arc::new(mk_var("x")),
        Arc::new(mk_var("y")),
    );
    let result = expr.substitute(&subs(&[
        ("c", PureExpr::Bool(true)),
        ("x", int(1)),
        ("y", int(2)),
    ]));
    assert_eq!(
        result,
        PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(int(1)),
            Arc::new(int(2)),
        )
    );
}

#[test]
fn substitute_in_ite_partial_replacement() {
    let expr = PureExpr::Ite(
        Arc::new(mk_var("c")),
        Arc::new(mk_var("x")),
        Arc::new(int(0)),
    );
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(
        result,
        PureExpr::Ite(Arc::new(mk_var("c")), Arc::new(int(42)), Arc::new(int(0)),)
    );
}

// === substitute_capture_avoiding: Exists ===

#[test]
fn capture_avoiding_exists_renames_to_avoid_capture() {
    // exists<x> (x > y) with subs {y → x}
    // Without capture avoidance: exists<x> (x > x) — captures y→x
    // With capture avoidance: exists<x_α0> (x_α0 > x)
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Gt,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts);
    match &result {
        PureExpr::Exists {
            var: bound_var,
            body,
            ..
        } => {
            assert_ne!(bound_var.as_str(), "x", "binder should be alpha-renamed");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(
                    Arc::new(mk_var(bound_var)),
                    BinOp::Gt,
                    Arc::new(mk_var("x"))
                )
            );
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

// === substitute_capture_avoiding: Match ===

#[test]
fn capture_avoiding_match_shadows_pattern_binding() {
    // match s { Some(x) => x+y } with subs {y → z}
    // No capture risk (z doesn't collide with x), so no alpha-rename needed.
    // y is substituted in the body, x stays bound.
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("s")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("x".to_string()))),
            },
            body: PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("y"))),
        }],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts);
    match &result {
        PureExpr::Match { arms, .. } => {
            // Body: x is shadowed (stays x), y is substituted to z
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("z")))
            );
            // Pattern unchanged — no capture risk
            assert_eq!(
                arms[0].pattern,
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                }
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_match_alpha_renames_pattern_binding() {
    // match x { Some(z) => z + y } with subs {y → z + 1}
    // Pattern binding "z" would capture the free "z" in the substitution value.
    // Capture-avoiding substitution must alpha-rename the pattern binding.
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("z".to_string()))),
            },
            body: PureExpr::BinOp(Arc::new(mk_var("z")), BinOp::Add, Arc::new(mk_var("y"))),
        }],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(
        &subs(&[(
            "y",
            PureExpr::BinOp(Arc::new(mk_var("z")), BinOp::Add, Arc::new(int(1))),
        )]),
        &opts,
    );
    match &result {
        PureExpr::Match { arms, .. } => {
            // The pattern binding should be renamed from "z" to a fresh name
            let bound = arms[0].pattern.bound_names();
            assert_eq!(bound.len(), 1);
            let fresh_name = bound[0];
            assert_ne!(
                fresh_name, "z",
                "pattern binding must be alpha-renamed to avoid capture"
            );
            // Body should use the fresh name (from pattern) and substituted y → z+1
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(
                    Arc::new(mk_var(fresh_name)),
                    BinOp::Add,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(mk_var("z")),
                        BinOp::Add,
                        Arc::new(int(1)),
                    )),
                )
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_match_scrutinee_substituted() {
    // match x { None => 0 } with subs {x → y}
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            body: int(0),
        }],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("x", mk_var("y"))]), &opts);
    match &result {
        PureExpr::Match { scrutinee, .. } => {
            assert_eq!(scrutinee.as_ref(), &mk_var("y"));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_match_tuple_pattern_renames() {
    // match x { (a, b) => a + b + y } with subs {y → a}
    // Pattern binding "a" would capture the free "a" in the substitution value.
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Tuple(vec![
                Pattern::Binding("a".to_string()),
                Pattern::Binding("b".to_string()),
            ]),
            body: PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(mk_var("a")),
                    BinOp::Add,
                    Arc::new(mk_var("b")),
                )),
                BinOp::Add,
                Arc::new(mk_var("y")),
            ),
        }],
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("a"))]), &opts);
    match &result {
        PureExpr::Match { arms, .. } => {
            let bound = arms[0].pattern.bound_names();
            assert_eq!(bound.len(), 2);
            // "a" should be renamed; "b" should stay
            assert_ne!(
                bound[0], "a",
                "pattern binding 'a' must be alpha-renamed to avoid capture"
            );
            assert_eq!(bound[1], "b", "pattern binding 'b' should be unchanged");
            let fresh_a = bound[0];
            // Body: fresh_a + b + a (where a is the substituted value from y→a)
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(mk_var(fresh_a)),
                        BinOp::Add,
                        Arc::new(mk_var("b")),
                    )),
                    BinOp::Add,
                    Arc::new(mk_var("a")),
                )
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

// === substitute_capture_avoiding: Let ===

#[test]
fn capture_avoiding_let_renames_to_avoid_capture() {
    // let x = 1 in x+y with subs {y → x}
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(int(1)),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts);
    match &result {
        PureExpr::Let {
            var: bound_var,
            body,
            ..
        } => {
            assert_ne!(
                bound_var.as_str(),
                "x",
                "let binding should be alpha-renamed"
            );
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(
                    Arc::new(mk_var(bound_var)),
                    BinOp::Add,
                    Arc::new(mk_var("x"))
                )
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

// === substitute_capture_avoiding: Closure ===

#[test]
fn capture_avoiding_closure_renames_param() {
    // |x| x+y with subs {y → x}
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
    };
    let opts = CaptureAvoidingSubstOptions { depth_limit: None };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts);
    match &result {
        PureExpr::Closure { params, body } => {
            let param_name = &params[0].0;
            assert_ne!(
                param_name.as_str(),
                "x",
                "closure param should be alpha-renamed"
            );
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(
                    Arc::new(mk_var(param_name)),
                    BinOp::Add,
                    Arc::new(mk_var("x"))
                )
            );
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

// === tuple beta-reduction edge cases ===

#[test]
fn substitute_tuple_beta_out_of_bounds_field_no_reduction() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };
    // tuple_get_5(tuple2(10, 20)) — field 5 is out of bounds for arity-2 tuple
    let tuple_ctor = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![int(10), int(20)],
    };
    let get_5 = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(5),
        args: vec![mk_var("t")],
    };
    let result = get_5.substitute(&subs(&[("t", tuple_ctor.clone())]));
    // Should NOT beta-reduce — field index out of bounds
    match &result {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(*name, tuple_field_logic_fn_name(5));
            assert_eq!(args[0], tuple_ctor);
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

#[test]
fn substitute_tuple_beta_non_ctor_arg_no_reduction() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;
    // tuple_get_0(x) where x is a plain variable, not a tuple constructor
    let get_0 = PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![mk_var("x")],
    };
    let result = get_0.substitute(&subs(&[("x", int(99))]));
    // x→99 is substituted but tuple_get_0(99) can't beta-reduce (Int is not a tuple ctor)
    match &result {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(*name, tuple_field_logic_fn_name(0));
            assert_eq!(args[0], int(99));
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

// === plain substitute: Forall/Exists trigger substitution ===

#[test]
fn substitute_forall_triggers_substituted() {
    // forall<x> [trigger: p(x, y)] (x > y) with {y → 5}
    // The trigger should have y substituted to 5.
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Gt,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![vec![PureExpr::MethodCall {
            receiver: Arc::new(mk_var("x")),
            method: "p".to_string(),
            args: vec![mk_var("y")],
        }]],
    };
    let result = expr.substitute(&subs(&[("y", int(5))]));
    match &result {
        PureExpr::Forall {
            var,
            body,
            triggers,
            ..
        } => {
            assert_eq!(var, "x");
            // Body: x > 5
            match body.as_ref() {
                PureExpr::BinOp(_, BinOp::Gt, right) => {
                    assert_eq!(right.as_ref(), &int(5));
                }
                other => panic!("expected BinOp in body, got {other:?}"),
            }
            // Trigger: p(x, 5)
            assert_eq!(triggers.len(), 1);
            assert_eq!(triggers[0].len(), 1);
            match &triggers[0][0] {
                PureExpr::MethodCall { args, .. } => {
                    assert_eq!(args[0], int(5), "trigger arg y should be substituted to 5");
                }
                other => panic!("expected MethodCall in trigger, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn substitute_exists_triggers_substituted() {
    // exists<x> [trigger: f(x, y)] (x == y) with {y → z}
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Eq,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![mk_var("x"), mk_var("y")],
        }]],
    };
    let result = expr.substitute(&subs(&[("y", mk_var("z"))]));
    match &result {
        PureExpr::Exists { triggers, body, .. } => {
            // Body: x == z
            match body.as_ref() {
                PureExpr::BinOp(_, BinOp::Eq, right) => {
                    assert_eq!(right.as_ref(), &mk_var("z"));
                }
                other => panic!("expected BinOp in body, got {other:?}"),
            }
            // Trigger: f(x, z) — x is shadowed, y→z
            match &triggers[0][0] {
                PureExpr::LogicFnCall { args, .. } => {
                    assert_eq!(args[0], mk_var("x"), "x is bound, not substituted");
                    assert_eq!(args[1], mk_var("z"), "y substituted to z in trigger");
                }
                other => panic!("expected LogicFnCall in trigger, got {other:?}"),
            }
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

// === plain substitute: Closure body + Let value ===

#[test]
fn substitute_closure_body_substituted() {
    // |x| y with {y → 42} — y is free in body, should be substituted
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(mk_var("y")),
    };
    let result = expr.substitute(&subs(&[("y", int(42))]));
    match &result {
        PureExpr::Closure { body, .. } => {
            assert_eq!(body.as_ref(), &int(42));
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

#[test]
fn substitute_let_value_and_body() {
    // let x = y in (x + z) with {y → 1, z → 2}
    // value: y → 1; body: x shadowed, z → 2
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(mk_var("y")),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("z")),
        )),
    };
    let result = expr.substitute(&subs(&[("y", int(1)), ("z", int(2))]));
    match &result {
        PureExpr::Let {
            var, value, body, ..
        } => {
            assert_eq!(var, "x");
            assert_eq!(value.as_ref(), &int(1), "value y→1 substituted");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(2))),
                "body: x shadowed, z→2"
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}
