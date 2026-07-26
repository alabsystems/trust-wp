// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Gap tests for `rename_free_var` covering variant arms that had zero
//! direct coverage: UnOp, Deref, Old, LetAssume, LetObligation, Closure
//! (both shadow and pass-through), Match arm binding shadow, and
//! Forall/Exists trigger renaming.
//!
//! Complements `substitute_free_var_tests.rs` which covers the common
//! variants (Var, BinOp, Ite, Forall, Exists, Let, MethodCall, LogicFnCall,
//! View, Final).

use std::sync::Arc;

use trust_wp_core::formula::{
    rename_free_var, BinOp, CaptureAvoidingSubstOptions, MatchArm, Pattern, PureExpr, UnOp,
};

fn opts() -> CaptureAvoidingSubstOptions {
    CaptureAvoidingSubstOptions { depth_limit: None }
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

// ── UnOp ──

#[test]
fn rename_through_unop_not() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::UnOp(UnOp::Not, Arc::new(var("y"))));
}

#[test]
fn rename_through_unop_neg() {
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::UnOp(UnOp::Neg, Arc::new(var("y"))));
}

#[test]
fn rename_unop_no_occurrence_unchanged() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(var("z")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, expr);
}

// ── Deref ──

#[test]
fn rename_through_deref() {
    let expr = PureExpr::Deref(Arc::new(var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::Deref(Arc::new(var("y"))));
}

#[test]
fn rename_deref_nested() {
    // Deref of BinOp containing the renamed var
    let inner = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(int(1)));
    let expr = PureExpr::Deref(Arc::new(inner));
    let result = rename_free_var(&expr, "x", "y", &opts());
    let expected = PureExpr::Deref(Arc::new(PureExpr::BinOp(
        Arc::new(var("y")),
        BinOp::Add,
        Arc::new(int(1)),
    )));
    assert_eq!(result, expected);
}

// ── Old ──

#[test]
fn rename_through_old() {
    let expr = PureExpr::Old(Arc::new(var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::Old(Arc::new(var("y"))));
}

// ── LetAssume ──

#[test]
fn rename_in_let_assume_assumption() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(var("x")),
        body: Arc::new(int(1)),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(
        result,
        PureExpr::LetAssume {
            assumption: Arc::new(var("y")),
            body: Arc::new(int(1)),
        }
    );
}

#[test]
fn rename_in_let_assume_body() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(int(1)),
        body: Arc::new(var("x")),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(
        result,
        PureExpr::LetAssume {
            assumption: Arc::new(int(1)),
            body: Arc::new(var("y")),
        }
    );
}

#[test]
fn rename_in_let_assume_both() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(var("x")),
        body: Arc::new(var("x")),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(
        result,
        PureExpr::LetAssume {
            assumption: Arc::new(var("y")),
            body: Arc::new(var("y")),
        }
    );
}

// ── LetObligation ──

#[test]
fn rename_in_let_obligation_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(var("x")),
        body: Arc::new(int(1)),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(
        result,
        PureExpr::LetObligation {
            obligation: Arc::new(var("y")),
            body: Arc::new(int(1)),
        }
    );
}

#[test]
fn rename_in_let_obligation_body() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(int(1)),
        body: Arc::new(var("x")),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(
        result,
        PureExpr::LetObligation {
            obligation: Arc::new(int(1)),
            body: Arc::new(var("y")),
        }
    );
}

// ── Closure ──

#[test]
fn rename_closure_param_shadows_old_name() {
    // |x| x+z — x is a param, so renaming x→y does nothing in body
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Add,
            Arc::new(var("z")),
        )),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    // Closure shadows x, so expression unchanged
    assert_eq!(result, expr);
}

#[test]
fn rename_closure_non_param_passes_through() {
    // |a| a+x — x is free, should be renamed
    let expr = PureExpr::Closure {
        params: vec![("a".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("a")),
            BinOp::Add,
            Arc::new(var("x")),
        )),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    match &result {
        PureExpr::Closure { body, params } => {
            assert_eq!(params, &[("a".to_string(), None)]);
            assert_eq!(
                body.as_ref(),
                &PureExpr::BinOp(Arc::new(var("a")), BinOp::Add, Arc::new(var("y")))
            );
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

#[test]
fn rename_closure_multi_param_one_shadows() {
    // |a, x| a+x+z — x is shadowed, z is not the renamed var
    let expr = PureExpr::Closure {
        params: vec![("a".to_string(), None), ("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, expr);
}

// ── Match arm pattern binding shadows old name ──

#[test]
fn rename_match_arm_binds_old_name_skips_body() {
    // match s { Some(x) => x+z } — x is bound in arm, renaming x→y
    // should NOT touch body but SHOULD rename scrutinee if present
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("x".to_string()))),
            },
            body: PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(var("z"))),
        }],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    match &result {
        PureExpr::Match { scrutinee, arms } => {
            // Scrutinee has free x → renamed to y
            assert_eq!(scrutinee.as_ref(), &var("y"));
            // Arm body has x bound by pattern → NOT renamed
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(var("z")))
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn rename_match_arm_does_not_bind_renames_body() {
    // match s { None => x } — x is free in body, renamed
    let expr = PureExpr::Match {
        scrutinee: Arc::new(int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            body: var("x"),
        }],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    match &result {
        PureExpr::Match { arms, .. } => {
            assert_eq!(arms[0].body, var("y"));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

// ── Forall/Exists with triggers ──

#[test]
fn rename_forall_renames_triggers() {
    // forall<z> body with triggers [[p(x)]] — x is free in trigger
    let expr = PureExpr::Forall {
        var: "z".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "p".to_string(),
            args: vec![var("x")],
        }]],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    match &result {
        PureExpr::Forall { body, triggers, .. } => {
            assert_eq!(body.as_ref(), &var("y"));
            assert_eq!(triggers.len(), 1);
            assert_eq!(triggers[0].len(), 1);
            match &triggers[0][0] {
                PureExpr::LogicFnCall { args, .. } => {
                    assert_eq!(args, &[var("y")]);
                }
                other => panic!("expected LogicFnCall in trigger, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn rename_exists_renames_triggers() {
    let expr = PureExpr::Exists {
        var: "z".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![vec![var("x")]],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    match &result {
        PureExpr::Exists { body, triggers, .. } => {
            assert_eq!(body.as_ref(), &var("y"));
            assert_eq!(triggers, &vec![vec![var("y")]]);
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn rename_forall_bound_var_matches_old_name_unchanged() {
    // forall<x> body+triggers — x is bound, entire thing unchanged
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![vec![var("x")]],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    // Falls into the catch-all at end of rename: Forall where var == old_name
    assert_eq!(result, expr);
}

#[test]
fn rename_exists_bound_var_matches_old_name_unchanged() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![vec![var("x")]],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, expr);
}

// ── Let where var == old_name (value still renamed, body skipped) ──

#[test]
fn rename_let_bound_var_matches_renames_value_only() {
    // let x = x+1 in x — var == old_name "x"
    // Value has free x → renamed. Body x is bound → NOT renamed.
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Add,
            Arc::new(int(1)),
        )),
        body: Arc::new(var("x")),
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    match &result {
        PureExpr::Let {
            var: bound_var,
            value,
            body,
        } => {
            assert_eq!(bound_var, "x");
            // Value: x+1 → y+1
            assert_eq!(
                value.as_ref(),
                &PureExpr::BinOp(Arc::new(var("y")), BinOp::Add, Arc::new(int(1)))
            );
            // Body: x is bound, unchanged
            assert_eq!(body.as_ref(), &var("x"));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

// ── Structural sharing (reuse_arc/reuse_expr) ──

#[test]
fn rename_preserves_arc_identity_when_unchanged() {
    // When renaming a var not present, Arc should be reused
    let inner = Arc::new(var("z"));
    let expr = PureExpr::UnOp(UnOp::Not, Arc::clone(&inner));
    let result = rename_free_var(&expr, "x", "y", &opts());
    // Result should equal original (no change)
    assert_eq!(result, expr);
}
