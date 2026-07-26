// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(clippy::approx_constant)]

//! Tests for capture-avoiding substitution coverage gaps.
//!
//! Targets identified by proof_coverage audit:
//! - `substitute_let_capture_avoiding` (Let with capture risk)
//! - `substitute_capture_avoiding` on Exists (only Forall was tested)
//! - Multi-param closure capture avoidance
//! - UnOp in all three substitute engines
//! - Float literal passthrough
//! - LetAssume/LetObligation in capture-avoiding path
//! - Nested same-name binder shadowing (multi-level shadow/unshadow)

use std::{collections::HashMap, sync::Arc};

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

fn opts() -> CaptureAvoidingSubstOptions {
    CaptureAvoidingSubstOptions { depth_limit: None }
}

// === Let capture-avoidance ===

#[test]
fn capture_avoiding_let_renames_to_avoid_capture() {
    // let x = a in (x + y) with {y → x}
    // Without capture avoidance: let x = a in (x + x) — WRONG
    // With capture avoidance: let x_α0 = a in (x_α0 + x)
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(mk_var("a")),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts());
    match &result {
        PureExpr::Let { var, value, body } => {
            assert_ne!(
                var, "x",
                "let binding should be alpha-renamed to avoid capture"
            );
            assert_eq!(value.as_ref(), &mk_var("a"), "value should still be 'a'");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var(var)), BinOp::Add, Arc::new(mk_var("x"))),
                "body should use renamed var and substituted y→x"
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_let_no_capture_no_rename() {
    // let x = a in (x + y) with {y → z} — no capture risk
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(mk_var("a")),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts());
    match &result {
        PureExpr::Let { var, value, body } => {
            assert_eq!(var, "x", "no rename needed — no capture risk");
            assert_eq!(value.as_ref(), &mk_var("a"));
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("z")))
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_let_value_is_substituted() {
    // let x = y in x with {y → 42}
    // Value gets substituted, body has x shadowed so it stays.
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(mk_var("y")),
        body: Arc::new(mk_var("x")),
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", int(42))]), &opts());
    match &result {
        PureExpr::Let { var, value, body } => {
            assert_eq!(var, "x");
            assert_eq!(value.as_ref(), &int(42), "value should be substituted");
            assert_eq!(body.as_ref(), &mk_var("x"), "body x is shadowed, unchanged");
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

// === Exists capture-avoidance ===

#[test]
fn capture_avoiding_exists_renames_to_avoid_capture() {
    // exists<x> (x + y) with {y → x}
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts());
    match &result {
        PureExpr::Exists { var, body, .. } => {
            assert_ne!(var, "x", "exists binding should be alpha-renamed");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var(var)), BinOp::Add, Arc::new(mk_var("x")))
            );
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_exists_no_capture_no_rename() {
    // exists<x> (x + y) with {y → z} — no capture risk
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts());
    match &result {
        PureExpr::Exists { var, body, .. } => {
            assert_eq!(var, "x", "no rename needed");
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("z")))
            );
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

// === Multi-param closure capture-avoidance ===

#[test]
fn capture_avoiding_closure_multi_param_renames() {
    // |x, y| x + y + z with {z → x}
    // Param x should be renamed because z → x would be captured.
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None), ("y".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(mk_var("x")),
                BinOp::Add,
                Arc::new(mk_var("y")),
            )),
            BinOp::Add,
            Arc::new(mk_var("z")),
        )),
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("z", mk_var("x"))]), &opts());
    match &result {
        PureExpr::Closure { params, body } => {
            assert_eq!(params.len(), 2);
            // At least the "x" param should be renamed to avoid capture from z→x
            let first_param = &params[0].0;
            assert_ne!(
                first_param, "x",
                "param 'x' should be renamed to avoid capture of z→x"
            );
            // z in body should be substituted to x (the original x, not renamed)
            let body_str = format!("{body:?}");
            assert!(
                body_str.contains("\"x\""),
                "body should contain substituted x from z→x"
            );
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

// === UnOp coverage ===

#[test]
fn substitute_unop_negation() {
    // -(x) with {x → 42}
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("x")));
    let result = expr.substitute(&subs(&[("x", int(42))]));
    assert_eq!(result, PureExpr::UnOp(UnOp::Neg, Arc::new(int(42))));
}

#[test]
fn substitute_unop_not() {
    // !(flag) with {flag → true}
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(mk_var("flag")));
    let result = expr.substitute(&subs(&[("flag", PureExpr::Bool(true))]));
    assert_eq!(
        result,
        PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Bool(true)))
    );
}

#[test]
fn capture_avoiding_unop() {
    // -(y) with {y → x} in capture-avoiding mode
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("y")));
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts());
    assert_eq!(result, PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("x"))));
}

#[test]
fn rename_free_var_unop() {
    use trust_wp_core::formula::rename_free_var;
    // -(x) rename x → y
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("y"))));
}

// === Float literal coverage ===

#[test]
fn substitute_float_unchanged() {
    let expr = PureExpr::Float(FloatBits::from_f64(3.14));
    let result = expr.substitute(&subs(&[("x", int(1))]));
    assert_eq!(result, PureExpr::Float(FloatBits::from_f64(3.14)));
}

#[test]
fn capture_avoiding_float_unchanged() {
    let expr = PureExpr::Float(FloatBits::from_f64(2.71));
    let result = expr.substitute_capture_avoiding(&subs(&[("x", int(1))]), &opts());
    assert_eq!(result, PureExpr::Float(FloatBits::from_f64(2.71)));
}

// === LetAssume/LetObligation in capture-avoiding path ===

#[test]
fn capture_avoiding_let_assume() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(mk_var("x")),
        body: Arc::new(mk_var("y")),
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("x", int(1)), ("y", int(2))]), &opts());
    assert_eq!(
        result,
        PureExpr::LetAssume {
            assumption: Arc::new(int(1)),
            body: Arc::new(int(2)),
        }
    );
}

#[test]
fn capture_avoiding_let_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(mk_var("x")),
        body: Arc::new(mk_var("y")),
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("x", int(1)), ("y", int(2))]), &opts());
    assert_eq!(
        result,
        PureExpr::LetObligation {
            obligation: Arc::new(int(1)),
            body: Arc::new(int(2)),
        }
    );
}

// === Nested same-name binder (multi-level shadow/unshadow) ===

#[test]
fn substitute_nested_same_name_forall_shadowing() {
    // forall<x> forall<x> (x + y) with {y → 99}
    // Both forall bindings shadow x. The inner x should NOT be substituted.
    let inner = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![],
    };
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(inner),
        triggers: vec![],
    };
    let result = expr.substitute(&subs(&[("y", int(99)), ("x", int(77))]));
    // x should NOT be substituted (double-shadowed by both foralls)
    // y should be substituted to 99
    match &result {
        PureExpr::Forall {
            body: outer_body, ..
        } => match outer_body.as_ref() {
            PureExpr::Forall {
                body: inner_body, ..
            } => match inner_body.as_ref() {
                PureExpr::BinOp(left, _, right) => {
                    assert_eq!(
                        left.as_ref(),
                        &mk_var("x"),
                        "x is shadowed, should NOT be substituted"
                    );
                    assert_eq!(right.as_ref(), &int(99), "y should be substituted");
                }
                other => panic!("expected BinOp, got {other:?}"),
            },
            other => panic!("expected inner Forall, got {other:?}"),
        },
        other => panic!("expected outer Forall, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_nested_same_name_forall() {
    // forall<x> forall<x> (x + y) with {y → x}
    // The capture check must correctly handle double-shadowed x.
    let inner = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Add,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![],
    };
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(inner),
        triggers: vec![],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts());
    // Both foralls should be alpha-renamed since y→x could be captured.
    // The final body should have the substituted x in place of y.
    match &result {
        PureExpr::Forall {
            var: outer_var,
            body: outer_body,
            ..
        } => {
            match outer_body.as_ref() {
                PureExpr::Forall {
                    var: inner_var,
                    body: inner_body,
                    ..
                } => {
                    match inner_body.as_ref() {
                        PureExpr::BinOp(left, _, right) => {
                            // The inner body should reference the renamed inner var
                            assert_eq!(
                                left.as_ref(),
                                &mk_var(inner_var),
                                "bound var in body should match inner forall var"
                            );
                            // y should be substituted to "x" (original x)
                            assert_eq!(
                                right.as_ref(),
                                &mk_var("x"),
                                "y should become x from substitution"
                            );
                        }
                        other => panic!("expected BinOp, got {other:?}"),
                    }
                    // At least one var should be renamed
                    assert!(
                        outer_var != "x" || inner_var != "x",
                        "at least one forall var should be renamed to avoid capture"
                    );
                }
                other => panic!("expected inner Forall, got {other:?}"),
            }
        }
        other => panic!("expected outer Forall, got {other:?}"),
    }
}

// === Ite coverage in substitute ===

#[test]
fn substitute_ite() {
    // if cond then x else y with {x → 1, y → 2, cond → true}
    let expr = PureExpr::Ite(
        Arc::new(mk_var("cond")),
        Arc::new(mk_var("x")),
        Arc::new(mk_var("y")),
    );
    let result = expr.substitute(&subs(&[
        ("cond", PureExpr::Bool(true)),
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

// === expr_has_free_occurrence ===

#[test]
fn expr_has_free_occurrence_in_unop() {
    use trust_wp_core::formula::expr_has_free_occurrence;
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(mk_var("x")));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
    assert!(!expr_has_free_occurrence(&expr, "y", &opts()));
}

#[test]
fn expr_has_free_occurrence_in_closure_shadowed() {
    use trust_wp_core::formula::expr_has_free_occurrence;
    // |x| x — x is bound, not free
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(mk_var("x")),
    };
    assert!(!expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn expr_has_free_occurrence_in_closure_free() {
    use trust_wp_core::formula::expr_has_free_occurrence;
    // |x| y — y is free
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(mk_var("y")),
    };
    assert!(expr_has_free_occurrence(&expr, "y", &opts()));
}

// === Quantifier triggers in capture-avoiding substitution ===

#[test]
fn capture_avoiding_forall_renames_triggers_when_binder_renamed() {
    // forall<x> [trigger: x + 1] (x > y) with {y → x}
    // When x is renamed to x_α0 to avoid capture, the trigger must also
    // have its free x occurrences renamed to x_α0.
    let trigger = PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(int(1)));
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Gt,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![vec![trigger]],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("x"))]), &opts());
    match &result {
        PureExpr::Forall {
            var: new_var,
            body,
            triggers,
            ..
        } => {
            assert_ne!(new_var, "x", "binder should be renamed to avoid capture");
            // Trigger should reference the renamed variable, not original "x"
            assert_eq!(triggers.len(), 1);
            assert_eq!(triggers[0].len(), 1);
            match &triggers[0][0] {
                PureExpr::BinOp(left, BinOp::Add, _) => {
                    assert_eq!(
                        left.as_ref(),
                        &mk_var(new_var),
                        "trigger should use renamed var"
                    );
                }
                other => panic!("expected BinOp(Add) in trigger, got {other:?}"),
            }
            // Body should use renamed var on left, substituted x on right
            match body.as_ref() {
                PureExpr::BinOp(left, BinOp::Gt, right) => {
                    assert_eq!(left.as_ref(), &mk_var(new_var));
                    assert_eq!(right.as_ref(), &mk_var("x"));
                }
                other => panic!("expected BinOp(Gt) in body, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_forall_no_capture_leaves_triggers_intact() {
    // forall<x> [trigger: x + 1] (x > y) with {y → z}
    // No capture risk, so triggers should be substituted but binder not renamed.
    let trigger = PureExpr::BinOp(Arc::new(mk_var("x")), BinOp::Add, Arc::new(mk_var("y")));
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(mk_var("x")),
            BinOp::Gt,
            Arc::new(mk_var("y")),
        )),
        triggers: vec![vec![trigger]],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts());
    match &result {
        PureExpr::Forall {
            var,
            triggers,
            body,
            ..
        } => {
            assert_eq!(var, "x", "no rename needed");
            // Trigger y should be substituted to z
            match &triggers[0][0] {
                PureExpr::BinOp(left, BinOp::Add, right) => {
                    assert_eq!(left.as_ref(), &mk_var("x"));
                    assert_eq!(
                        right.as_ref(),
                        &mk_var("z"),
                        "y in trigger substituted to z"
                    );
                }
                other => panic!("expected BinOp in trigger, got {other:?}"),
            }
            // Body y substituted to z
            match body.as_ref() {
                PureExpr::BinOp(_, _, right) => {
                    assert_eq!(right.as_ref(), &mk_var("z"));
                }
                other => panic!("expected BinOp in body, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

// === LogicFnCall in capture-avoiding ===

#[test]
fn capture_avoiding_logic_fn_call_substitutes_args() {
    let expr = PureExpr::LogicFnCall {
        name: "resolve".to_string(),
        args: vec![mk_var("x"), mk_var("y")],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("x", int(1)), ("y", int(2))]), &opts());
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "resolve".to_string(),
            args: vec![int(1), int(2)],
        }
    );
}

// === Deref/Final/View/Old wrappers in capture-avoiding ===

#[test]
fn capture_avoiding_deref_substitutes_inner() {
    let expr = PureExpr::Deref(Arc::new(mk_var("p")));
    let result = expr.substitute_capture_avoiding(&subs(&[("p", mk_var("q"))]), &opts());
    assert_eq!(result, PureExpr::Deref(Arc::new(mk_var("q"))));
}

#[test]
fn capture_avoiding_final_substitutes_inner() {
    let expr = PureExpr::Final(Arc::new(mk_var("p")));
    let result = expr.substitute_capture_avoiding(&subs(&[("p", mk_var("q"))]), &opts());
    assert_eq!(result, PureExpr::Final(Arc::new(mk_var("q"))));
}

#[test]
fn capture_avoiding_view_substitutes_inner() {
    let expr = PureExpr::View(Arc::new(mk_var("v")));
    let result = expr.substitute_capture_avoiding(&subs(&[("v", mk_var("w"))]), &opts());
    assert_eq!(result, PureExpr::View(Arc::new(mk_var("w"))));
}

#[test]
fn capture_avoiding_old_substitutes_inner() {
    let expr = PureExpr::Old(Arc::new(mk_var("x")));
    let result = expr.substitute_capture_avoiding(&subs(&[("x", int(5))]), &opts());
    assert_eq!(result, PureExpr::Old(Arc::new(int(5))));
}

// === Ite in capture-avoiding ===

#[test]
fn capture_avoiding_ite_substitutes_all_branches() {
    let expr = PureExpr::Ite(
        Arc::new(mk_var("c")),
        Arc::new(mk_var("t")),
        Arc::new(mk_var("e")),
    );
    let result = expr.substitute_capture_avoiding(
        &subs(&[("c", PureExpr::Bool(true)), ("t", int(1)), ("e", int(2))]),
        &opts(),
    );
    assert_eq!(
        result,
        PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(int(1)),
            Arc::new(int(2)),
        )
    );
}

// === MethodCall in capture-avoiding ===

#[test]
fn capture_avoiding_method_call_substitutes_receiver_and_args() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(mk_var("v")),
        method: "len".to_string(),
        args: vec![mk_var("a")],
    };
    let result =
        expr.substitute_capture_avoiding(&subs(&[("v", mk_var("w")), ("a", int(1))]), &opts());
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(mk_var("w")),
            method: "len".to_string(),
            args: vec![int(1)],
        }
    );
}

// === Match arm capture avoidance: multi-binding boundary ===

#[test]
fn capture_avoiding_match_tuple_both_bindings_collide() {
    // match x { (a, b) => a + b + y } with subs {y → a + b}
    // Both "a" and "b" in the pattern collide with free vars in the
    // substitution value for y. Both must be alpha-renamed.
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
    let result = expr.substitute_capture_avoiding(
        &subs(&[(
            "y",
            PureExpr::BinOp(Arc::new(mk_var("a")), BinOp::Add, Arc::new(mk_var("b"))),
        )]),
        &opts(),
    );
    match &result {
        PureExpr::Match { arms, .. } => {
            let bound = arms[0].pattern.bound_names();
            assert_eq!(bound.len(), 2);
            // Both "a" and "b" should be renamed to fresh names
            assert_ne!(bound[0], "a", "binding 'a' must be renamed");
            assert_ne!(bound[1], "b", "binding 'b' must be renamed");
            // The two fresh names must be distinct from each other
            assert_ne!(bound[0], bound[1], "fresh names must differ");
            let fresh_a = bound[0];
            let fresh_b = bound[1];
            // Body should use fresh names for bound vars and original a+b for substituted y
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(mk_var(fresh_a)),
                        BinOp::Add,
                        Arc::new(mk_var(fresh_b)),
                    )),
                    BinOp::Add,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(mk_var("a")),
                        BinOp::Add,
                        Arc::new(mk_var("b")),
                    )),
                )
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_match_multiple_arms_partial_capture() {
    // match x { Some(z) => z + y, None => y } with subs {y → z}
    // First arm: "z" in pattern collides with substitution value.
    // Second arm: no bindings, straight substitution.
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("x")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("z".to_string()))),
                },
                body: PureExpr::BinOp(Arc::new(mk_var("z")), BinOp::Add, Arc::new(mk_var("y"))),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: mk_var("y"),
            },
        ],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts());
    match &result {
        PureExpr::Match { arms, .. } => {
            // First arm: "z" renamed to fresh
            let bound0 = arms[0].pattern.bound_names();
            assert_eq!(bound0.len(), 1);
            let fresh = bound0[0];
            assert_ne!(fresh, "z", "pattern 'z' must be renamed in first arm");
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(Arc::new(mk_var(fresh)), BinOp::Add, Arc::new(mk_var("z")))
            );

            // Second arm: no bindings, y → z directly
            assert_eq!(arms[1].body, mk_var("z"));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_match_wildcard_arm_no_bindings() {
    // match x { _ => y } with subs {y → z}
    // Wildcard has no bindings. y should be substituted directly.
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: mk_var("y"),
        }],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts());
    match &result {
        PureExpr::Match { arms, .. } => {
            assert_eq!(arms[0].body, mk_var("z"));
            assert_eq!(arms[0].pattern, Pattern::Wildcard);
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn capture_avoiding_match_nested_constructor_pattern() {
    // match x { Some(Some(z)) => z + y } with subs {y → z}
    // The binding "z" is inside a nested constructor. Alpha-renaming
    // must reach into the nested pattern to rename it.
    let expr = PureExpr::Match {
        scrutinee: Arc::new(mk_var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("z".to_string()))),
                })),
            },
            body: PureExpr::BinOp(Arc::new(mk_var("z")), BinOp::Add, Arc::new(mk_var("y"))),
        }],
    };
    let result = expr.substitute_capture_avoiding(&subs(&[("y", mk_var("z"))]), &opts());
    match &result {
        PureExpr::Match { arms, .. } => {
            let bound = arms[0].pattern.bound_names();
            assert_eq!(bound.len(), 1);
            let fresh = bound[0];
            assert_ne!(fresh, "z", "nested pattern binding must be renamed");
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(Arc::new(mk_var(fresh)), BinOp::Add, Arc::new(mk_var("z")))
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}
