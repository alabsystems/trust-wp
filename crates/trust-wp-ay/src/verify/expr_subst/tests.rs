// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for capture-avoiding substitution — extracted from inline tests (#1669).

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{expr_has_free_occurrence, rename_free_var, substitute_vars_in_expr};
use crate::tests::helpers::{
    add, eq, exists, forall, forall_with_triggers, gt, int, let_bind, match_expr, var,
};

// --- substitute_vars_in_expr capture-avoiding substitution (#1247) ---

/// Capture-avoiding substitution alpha-renames let binders to prevent
/// free variables in substitution values from being captured.
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_renames_let_to_avoid_capture() {
    // let x = 1 in y   with binding { y -> Var("x") }
    // Naive result: let x = 1 in x  (WRONG — free "x" captured by let)
    // Correct: let x$α0 = 1 in x  (alpha-renamed binder, free "x" preserved)
    let expr = let_bind("x", int(1), var("y"));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    // After fix: let binder is alpha-renamed, body references free "x".
    match &result {
        PureExpr::Let { var: v, body, .. } => {
            assert_ne!(
                v, "x",
                "let binder should be alpha-renamed to avoid capture"
            );
            assert_eq!(
                **body,
                var("x"),
                "body should reference the free variable x (from substitution)"
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

/// Capture-avoiding substitution also works for quantifier binders.
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_renames_forall_to_avoid_capture() {
    // forall x. y > x   with binding { y -> Var("x") }
    // Naive: forall x. x > x  (WRONG — free "x" captured by forall)
    // Correct: forall x$α0. x > x$α0
    let expr = forall("x", gt(var("y"), var("x")));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Forall { var: v, body, .. } => {
            assert_ne!(
                v, "x",
                "forall binder should be alpha-renamed to avoid capture"
            );
            // The body should reference free "x" (from substitution) and
            // the renamed bound variable
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                    assert_eq!(**lhs, var("x"), "lhs should be free x (from substitution)");
                    assert_eq!(
                        **rhs,
                        PureExpr::Var(v.clone(), None),
                        "rhs should reference the renamed bound variable"
                    );
                }
                other => panic!("expected BinOp(Gt), got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// When no capture conflict exists, substitution does not rename.
#[test]
#[timeout(30000)]
fn substitute_vars_no_rename_when_no_capture() {
    // let x = 1 in y   with binding { y -> Var("z") }
    // No capture: "z" doesn't conflict with let-bound "x"
    let expr = let_bind("x", int(1), var("y"));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("z"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Let { var: v, body, .. } => {
            assert_eq!(v, "x", "no rename needed — binder stays as x");
            assert_eq!(**body, var("z"), "body should have y substituted to z");
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

// --- Exists capture-avoiding substitution (#901 proof_coverage) ---

/// Capture-avoiding substitution alpha-renames Exists binders.
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_renames_exists_to_avoid_capture() {
    // exists x. y > x   with binding { y -> Var("x") }
    // Naive: exists x. x > x  (WRONG — free "x" captured by exists)
    // Correct: exists x$α0. x > x$α0
    let expr = exists("x", gt(var("y"), var("x")));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Exists { var: v, body, .. } => {
            assert_ne!(
                v, "x",
                "exists binder should be alpha-renamed to avoid capture"
            );
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                    assert_eq!(**lhs, var("x"), "lhs should be free x (from substitution)");
                    assert_eq!(
                        **rhs,
                        PureExpr::Var(v.clone(), None),
                        "rhs should reference the renamed bound variable"
                    );
                }
                other => panic!("expected BinOp(Gt), got {other:?}"),
            }
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

/// Exists with no capture conflict does not rename.
#[test]
#[timeout(30000)]
fn substitute_vars_exists_no_rename_when_no_capture() {
    let expr = exists("x", gt(var("y"), var("x")));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("z"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Exists { var: v, body, .. } => {
            assert_eq!(v, "x", "no rename needed — binder stays as x");
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                    assert_eq!(**lhs, var("z"), "y should be substituted to z");
                    assert_eq!(**rhs, var("x"), "bound var x unchanged");
                }
                other => panic!("expected BinOp(Gt), got {other:?}"),
            }
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

/// Exists binder shadows the substitution: body references stay bound.
#[test]
#[timeout(30000)]
fn substitute_vars_exists_binder_shadows_binding() {
    let expr = exists("x", gt(var("x"), int(0)));
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(42));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Exists { var: v, body, .. } => {
            assert_eq!(v, "x", "binder should remain x");
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                    assert_eq!(**lhs, var("x"), "body x is bound, not substituted");
                    assert_eq!(**rhs, int(0));
                }
                other => panic!("expected BinOp(Gt), got {other:?}"),
            }
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

// --- Closure capture-avoiding substitution (#901 proof_coverage) ---

/// Closure params shadow the substitution binding.
#[test]
#[timeout(30000)]
fn substitute_vars_closure_param_shadows_binding() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(add(var("x"), var("y"))),
    };
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(99));
    binding.insert("y".to_string(), int(1));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Closure { params, body } => {
            assert_eq!(params[0].0, "x", "param should remain x");
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                    assert_eq!(**lhs, var("x"), "x is shadowed by param");
                    assert_eq!(**rhs, int(1), "y should be substituted to 1");
                }
                other => panic!("expected BinOp(Add), got {other:?}"),
            }
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

/// Closure capture-avoiding substitution alpha-renames params.
#[test]
#[timeout(30000)]
fn substitute_vars_closure_alpha_renames_to_avoid_capture() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(add(var("y"), var("x"))),
    };
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Closure { params, body } => {
            assert_ne!(
                params[0].0, "x",
                "closure param should be alpha-renamed to avoid capture"
            );
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                    assert_eq!(**lhs, var("x"), "y substituted to free x");
                    assert_eq!(
                        **rhs,
                        PureExpr::Var(params[0].0.clone(), None),
                        "body should use renamed param"
                    );
                }
                other => panic!("expected BinOp(Add), got {other:?}"),
            }
        }
        other => panic!("expected Closure, got {other:?}"),
    }
}

// --- Match capture-avoiding substitution (#901 proof_coverage) ---

/// Match arm pattern bindings shadow the substitution.
#[test]
#[timeout(30000)]
fn substitute_vars_match_arm_binding_shadows_substitution() {
    use trust_wp_core::formula::Pattern;
    let expr = match_expr(
        var("x"),
        vec![(Pattern::Binding("a".to_string()), add(var("a"), var("y")))],
    );
    let mut binding = HashMap::new();
    binding.insert("a".to_string(), int(42));
    binding.insert("y".to_string(), int(1));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Match { arms, .. } => match &arms[0].body {
            PureExpr::BinOp(_, BinOp::Add, rhs) => {
                assert_eq!(**rhs, int(1), "y should be substituted to 1");
            }
            other => panic!("expected BinOp(Add), got {other:?}"),
        },
        other => panic!("expected Match, got {other:?}"),
    }
}

/// Match scrutinee receives substitution regardless of arm bindings.
#[test]
#[timeout(30000)]
fn substitute_vars_match_scrutinee_receives_substitution() {
    use trust_wp_core::formula::Pattern;
    let expr = match_expr(var("y"), vec![(Pattern::Wildcard, int(0))]);
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), int(42));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Match { scrutinee, .. } => {
            assert_eq!(**scrutinee, int(42), "scrutinee should be substituted");
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

// --- LetAssume/LetObligation substitution (#901 proof_coverage) ---

#[test]
#[timeout(30000)]
fn substitute_vars_let_assume_substitutes_both() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(gt(var("x"), int(0))),
        body: Arc::new(add(var("y"), int(1))),
    };
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(5));
    binding.insert("y".to_string(), int(10));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::LetAssume { assumption, body } => {
            assert!(
                matches!(assumption.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == int(5)),
                "x in assumption substituted to 5"
            );
            assert!(
                matches!(body.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == int(10)),
                "y in body substituted to 10"
            );
        }
        other => panic!("expected LetAssume, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn substitute_vars_let_obligation_substitutes_both() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(gt(var("x"), int(0))),
        body: Arc::new(add(var("y"), int(1))),
    };
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(5));
    binding.insert("y".to_string(), int(10));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::LetObligation { obligation, body } => {
            assert!(
                matches!(obligation.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == int(5)),
                "x in obligation substituted to 5"
            );
            assert!(
                matches!(body.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == int(10)),
                "y in body substituted to 10"
            );
        }
        other => panic!("expected LetObligation, got {other:?}"),
    }
}

// --- expr_has_free_occurrence: binder shadowing (#901 proof_coverage) ---

#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_forall_shadows() {
    let expr = forall("x", gt(var("x"), int(0)));
    assert!(
        !expr_has_free_occurrence(&expr, "x"),
        "x is bound by forall, not a free occurrence"
    );
}

#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_exists_shadows() {
    let expr = exists("x", gt(var("x"), int(0)));
    assert!(
        !expr_has_free_occurrence(&expr, "x"),
        "x is bound by exists, not a free occurrence"
    );
}

#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_closure_shadows() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(add(var("x"), int(1))),
    };
    assert!(
        !expr_has_free_occurrence(&expr, "x"),
        "x is bound by closure param, not free"
    );
}

#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_match_binding_shadows() {
    use trust_wp_core::formula::Pattern;
    let expr = match_expr(
        var("y"),
        vec![(Pattern::Binding("x".to_string()), add(var("x"), int(1)))],
    );
    assert!(
        !expr_has_free_occurrence(&expr, "x"),
        "x is bound by match pattern, not free"
    );
}

#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_in_let_value() {
    let expr = let_bind("x", add(var("x"), int(1)), int(0));
    assert!(
        expr_has_free_occurrence(&expr, "x"),
        "x in let value position is free"
    );
}

// --- rename_free_var: binder forms (#901 proof_coverage) ---

#[test]
#[timeout(30000)]
fn rename_free_var_through_exists() {
    let expr = exists("y", gt(var("x"), var("y")));
    let result = rename_free_var(&expr, "x", "z");
    match &result {
        PureExpr::Exists { body, .. } => match body.as_ref() {
            PureExpr::BinOp(lhs, BinOp::Gt, _) => {
                assert_eq!(**lhs, var("z"), "x should be renamed to z");
            }
            other => panic!("expected BinOp(Gt), got {other:?}"),
        },
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn rename_free_var_exists_shadowed() {
    let expr = exists("x", gt(var("x"), int(0)));
    let result = rename_free_var(&expr, "x", "z");
    assert_eq!(result, expr, "exists-bound x should not be renamed");
}

#[test]
#[timeout(30000)]
fn rename_free_var_through_match() {
    use trust_wp_core::formula::Pattern;
    let expr = match_expr(var("y"), vec![(Pattern::Wildcard, add(var("x"), int(1)))]);
    let result = rename_free_var(&expr, "x", "z");
    match &result {
        PureExpr::Match { arms, .. } => match &arms[0].body {
            PureExpr::BinOp(lhs, BinOp::Add, _) => {
                assert_eq!(**lhs, var("z"), "x should be renamed to z in arm body");
            }
            other => panic!("expected BinOp(Add), got {other:?}"),
        },
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn rename_free_var_match_shadowed() {
    use trust_wp_core::formula::Pattern;
    let expr = match_expr(
        var("y"),
        vec![(Pattern::Binding("x".to_string()), add(var("x"), int(1)))],
    );
    let result = rename_free_var(&expr, "x", "z");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert_eq!(
                arms[0].body,
                add(var("x"), int(1)),
                "match arm body should not be renamed (x is bound by pattern)"
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn rename_free_var_through_closure() {
    let expr = PureExpr::Closure {
        params: vec![("y".to_string(), None)],
        body: Arc::new(add(var("x"), var("y"))),
    };
    let result = rename_free_var(&expr, "x", "z");
    match &result {
        PureExpr::Closure { body, .. } => match body.as_ref() {
            PureExpr::BinOp(lhs, BinOp::Add, _) => {
                assert_eq!(**lhs, var("z"), "x should be renamed to z in closure body");
            }
            other => panic!("expected BinOp(Add), got {other:?}"),
        },
        other => panic!("expected Closure, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn rename_free_var_closure_shadowed() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(add(var("x"), int(1))),
    };
    let result = rename_free_var(&expr, "x", "z");
    assert_eq!(result, expr, "closure-param x should not be renamed");
}

#[test]
#[timeout(30000)]
fn rename_free_var_through_let_assume() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(eq(var("x"), int(0))),
        body: Arc::new(add(var("x"), int(1))),
    };
    let result = rename_free_var(&expr, "x", "z");
    match &result {
        PureExpr::LetAssume { assumption, body } => {
            assert!(
                matches!(assumption.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == var("z")),
                "x in assumption should be renamed"
            );
            assert!(
                matches!(body.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == var("z")),
                "x in body should be renamed"
            );
        }
        other => panic!("expected LetAssume, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn rename_free_var_through_let_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(eq(var("x"), int(0))),
        body: Arc::new(add(var("x"), int(1))),
    };
    let result = rename_free_var(&expr, "x", "z");
    match &result {
        PureExpr::LetObligation { obligation, body } => {
            assert!(
                matches!(obligation.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == var("z")),
                "x in obligation should be renamed"
            );
            assert!(
                matches!(body.as_ref(), PureExpr::BinOp(lhs, ..) if **lhs == var("z")),
                "x in body should be renamed"
            );
        }
        other => panic!("expected LetObligation, got {other:?}"),
    }
}

// --- fresh_var_name body/trigger collision avoidance (#2347) ---

/// When the quantifier body already contains a free `x$α0` from a prior
/// alpha-rename pass, `fresh_var_name` must skip `x$α0` and choose a
/// non-colliding name. (#2347)
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_rename_skips_preexisting_alpha0_in_body() {
    // forall x. (x$α0 > x)   with binding { z -> Var("x") }
    //
    // The body already has a free `x$α0`. The binding forces rename of the
    // bound `x` (because `z -> x` contains free "x"). Without #2347 fix,
    // fresh_var_name picks `x$α0`, capturing the pre-existing free variable.
    // Correct: pick `x$α1` (or higher) to avoid the collision.
    let body = gt(var("x$α0"), var("x"));
    let expr = forall("x", body);
    let mut binding = HashMap::new();
    binding.insert("z".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Forall { var: v, body, .. } => {
            assert_ne!(
                v, "x",
                "binder must be alpha-renamed (binding contains free x)"
            );
            assert_ne!(
                v, "x$α0",
                "binder must NOT become x$α0 — body already has free x$α0"
            );
            // The pre-existing free x$α0 must survive unchanged
            assert!(
                expr_has_free_occurrence(body, "x$α0"),
                "pre-existing free x$α0 must remain free in the body"
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// When a quantifier trigger already contains a free `x$α0`,
/// `fresh_var_name` must skip that name. (#2347)
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_rename_skips_preexisting_alpha0_in_trigger() {
    // forall x [trigger: x$α0 > 0]. (x > 0)   with binding { z -> Var("x") }
    //
    // The trigger has a free `x$α0`. Binding forces rename of bound `x`.
    // Without #2347 fix, fresh_var_name picks `x$α0`, capturing the
    // pre-existing free variable in the trigger.
    let body = gt(var("x"), int(0));
    let triggers = vec![vec![gt(var("x$α0"), int(0))]];
    let expr = forall_with_triggers("x", body, triggers);
    let mut binding = HashMap::new();
    binding.insert("z".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Forall {
            var: v, triggers, ..
        } => {
            assert_ne!(
                v, "x",
                "binder must be alpha-renamed (binding contains free x)"
            );
            assert_ne!(
                v, "x$α0",
                "binder must NOT become x$α0 — trigger already has free x$α0"
            );
            // The trigger's pre-existing free x$α0 must survive
            let trigger_expr = &triggers[0][0];
            assert!(
                expr_has_free_occurrence(trigger_expr, "x$α0"),
                "pre-existing free x$α0 must remain in the trigger"
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

// --- substitute_vars_in_expr: identity, simple, and wrapper cases ---

/// Empty binding map is the identity transformation.
#[test]
#[timeout(30000)]
fn substitute_vars_empty_binding_is_identity() {
    let expr = add(var("x"), int(1));
    let binding = HashMap::new();

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(
        result, expr,
        "empty binding should return the same expression"
    );
}

/// Simple variable replacement: { x -> 42 } applied to Var("x") yields Int(42).
#[test]
#[timeout(30000)]
fn substitute_vars_simple_var_replacement() {
    let expr = var("x");
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(42));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, int(42), "x should be replaced by 42");
}

/// Variables not in the binding are unchanged.
#[test]
#[timeout(30000)]
fn substitute_vars_unbound_var_unchanged() {
    let expr = var("y");
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(42));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, var("y"), "unbound variable y should be unchanged");
}

/// Substitution recurses into BinOp children.
#[test]
#[timeout(30000)]
fn substitute_vars_recurses_into_binop() {
    let expr = add(var("x"), var("y"));
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(1));
    binding.insert("y".to_string(), int(2));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, add(int(1), int(2)));
}

/// Substitution recurses through Ite (if-then-else).
#[test]
#[timeout(30000)]
fn substitute_vars_recurses_into_ite() {
    use crate::tests::helpers::ite;

    let expr = ite(var("c"), var("x"), var("y"));
    let mut binding = HashMap::new();
    binding.insert("c".to_string(), PureExpr::Bool(true));
    binding.insert("x".to_string(), int(1));
    binding.insert("y".to_string(), int(2));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, ite(PureExpr::Bool(true), int(1), int(2)));
}

/// Substitution recurses into View wrapper.
#[test]
#[timeout(30000)]
fn substitute_vars_recurses_into_view() {
    use crate::tests::helpers::view;

    let expr = view(var("x"));
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), var("y"));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, view(var("y")));
}

/// Substitution recurses into Old wrapper.
#[test]
#[timeout(30000)]
fn substitute_vars_recurses_into_old() {
    use crate::tests::helpers::old;

    let expr = old(var("x"));
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(5));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, old(int(5)));
}

/// Substitution recurses into nested let bindings correctly.
#[test]
#[timeout(30000)]
fn substitute_vars_nested_let_bindings() {
    // let a = x in (let b = y in a + b)
    let expr = let_bind(
        "a",
        var("x"),
        let_bind("b", var("y"), add(var("a"), var("b"))),
    );
    let mut binding = HashMap::new();
    binding.insert("x".to_string(), int(1));
    binding.insert("y".to_string(), int(2));

    let result = substitute_vars_in_expr(&expr, &binding);

    // The outer let: a = 1, body = let b = 2 in a + b
    match &result {
        PureExpr::Let {
            var: v,
            value,
            body,
        } => {
            assert_eq!(v, "a");
            assert_eq!(**value, int(1), "x should be substituted to 1");
            match body.as_ref() {
                PureExpr::Let {
                    var: v2,
                    value: val2,
                    body: body2,
                } => {
                    assert_eq!(v2, "b");
                    assert_eq!(**val2, int(2), "y should be substituted to 2");
                    assert_eq!(
                        **body2,
                        add(var("a"), var("b")),
                        "inner references are to bound variables, not substituted"
                    );
                }
                other => panic!("expected inner Let, got {other:?}"),
            }
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

/// Multiple simultaneous bindings are all applied.
#[test]
#[timeout(30000)]
fn substitute_vars_multiple_bindings_applied_simultaneously() {
    let expr = add(var("a"), add(var("b"), var("c")));
    let mut binding = HashMap::new();
    binding.insert("a".to_string(), int(10));
    binding.insert("b".to_string(), int(20));
    binding.insert("c".to_string(), int(30));

    let result = substitute_vars_in_expr(&expr, &binding);
    assert_eq!(result, add(int(10), add(int(20), int(30))));
}

// --- expr_has_free_occurrence: leaf and basic cases ---

/// A simple variable occurrence is free.
#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_simple_var_true() {
    assert!(
        expr_has_free_occurrence(&var("x"), "x"),
        "Var('x') has a free occurrence of 'x'"
    );
}

/// An integer literal has no free variables.
#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_int_literal_false() {
    assert!(
        !expr_has_free_occurrence(&int(42), "x"),
        "Int(42) has no free occurrence of 'x'"
    );
}

/// A different variable name is not a free occurrence.
#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_different_var_false() {
    assert!(
        !expr_has_free_occurrence(&var("y"), "x"),
        "Var('y') has no free occurrence of 'x'"
    );
}

/// Free occurrence check recurses into BinOp.
#[test]
#[timeout(30000)]
fn expr_has_free_occurrence_in_binop_rhs() {
    let expr = add(int(0), var("x"));
    assert!(
        expr_has_free_occurrence(&expr, "x"),
        "x in the rhs of BinOp is a free occurrence"
    );
}

// --- rename_free_var: basic cases ---

/// rename_free_var replaces a simple free variable.
#[test]
#[timeout(30000)]
fn rename_free_var_simple_replacement() {
    let expr = var("x");
    let result = rename_free_var(&expr, "x", "z");
    assert_eq!(result, var("z"), "free x should be renamed to z");
}

/// rename_free_var does not modify unrelated variables.
#[test]
#[timeout(30000)]
fn rename_free_var_unrelated_var_unchanged() {
    let expr = var("y");
    let result = rename_free_var(&expr, "x", "z");
    assert_eq!(result, var("y"), "unrelated variable y should be unchanged");
}

/// rename_free_var recurses into both sides of BinOp.
#[test]
#[timeout(30000)]
fn rename_free_var_recurses_through_binop() {
    let expr = add(var("x"), var("x"));
    let result = rename_free_var(&expr, "x", "z");
    assert_eq!(result, add(var("z"), var("z")));
}
