// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{MatchArm, Pattern};

use super::*;

fn int_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn logic_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

#[test]
fn inject_forall_triggers_preserves_explicit_triggers() {
    let explicit_trigger = logic_call("outer_pred", vec![int_var("x")]);
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(logic_call("body_pred", vec![int_var("x")])),
        triggers: vec![vec![explicit_trigger.clone()]],
    };

    assert_eq!(inject_forall_triggers(&expr), expr);
}

#[test]
fn relax_single_var_multitriggers_retargets_explicit_multi_pattern() {
    let lhs = logic_call("contains_pred", vec![int_var("k")]);
    let rhs = logic_call("lookup_pred", vec![int_var("k")]);
    let expr = PureExpr::Forall {
        var: "k".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(lhs.clone()),
            BinOp::Implies,
            Arc::new(rhs.clone()),
        )),
        triggers: vec![vec![lhs.clone(), rhs.clone()]],
    };

    let rewritten = relax_single_var_multitriggers(&expr);
    match rewritten {
        PureExpr::Forall { triggers, .. } => {
            assert!(
                !triggers.is_empty(),
                "rewritten quantifier should keep triggers"
            );
            assert!(
                triggers.iter().all(|pattern| pattern.len() == 1),
                "single-variable multitrigger should be retargeted to singleton patterns, got {triggers:?}"
            );
            assert_ne!(
                triggers,
                vec![vec![lhs, rhs]],
                "rewriter should replace the original multi-pattern trigger"
            );
        }
        other => panic!("expected forall, got {other:?}"),
    }
}

#[test]
fn relax_single_var_multitriggers_retargets_fmap_frame_to_current_contains() {
    let other_key = int_var("__fmap_iter_other_key");
    let entry_key = int_var("entry_key");
    let current_iter = PureExpr::View(Arc::new(fmap_var("iter_state")));
    let next_iter = PureExpr::View(Arc::new(fmap_var("iter_state_next")));
    let current_contains = method_call(current_iter.clone(), "contains", vec![other_key.clone()]);
    let current_lookup = method_call(current_iter, "lookup", vec![other_key.clone()]);
    let next_contains = method_call(next_iter.clone(), "contains", vec![other_key.clone()]);
    let next_lookup = method_call(next_iter, "lookup", vec![other_key.clone()]);
    let fact = PureExpr::Forall {
        var: "__fmap_iter_other_key".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(other_key.clone()),
                    BinOp::Ne,
                    Arc::new(entry_key.clone()),
                )),
                BinOp::And,
                Arc::new(current_contains.clone()),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(next_contains),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(next_lookup),
                    BinOp::Eq,
                    Arc::new(current_lookup.clone()),
                )),
            )),
        )),
        triggers: vec![vec![current_contains.clone(), current_lookup]],
    };

    let rewritten = relax_single_var_multitriggers(&fact);
    match rewritten {
        PureExpr::Forall { triggers, .. } => {
            // All alternative patterns should be singletons (len == 1).
            assert!(
                triggers.iter().all(|p| p.len() == 1),
                "all retargeted patterns should be singletons: {triggers:?}"
            );
            // With implication-aware scoring (#2696), consequent-side triggers
            // are preferred. The consequent is `next_contains && (next_lookup == current_lookup)`,
            // so `next_contains` (consequent side) ranks higher than `current_contains`
            // (guard side). Both should appear as alternative patterns.
            let next_contains_expected = method_call(
                PureExpr::View(Arc::new(fmap_var("iter_state_next"))),
                "contains",
                vec![int_var("__fmap_iter_other_key")],
            );
            let current_contains_expected = method_call(
                PureExpr::View(Arc::new(fmap_var("iter_state"))),
                "contains",
                vec![int_var("__fmap_iter_other_key")],
            );
            let has_next = triggers
                .iter()
                .any(|p| p == &[next_contains_expected.clone()]);
            let has_current = triggers
                .iter()
                .any(|p| p == &[current_contains_expected.clone()]);
            assert!(
                has_next,
                "next_contains (consequent side) should appear as an alternative: {triggers:?}"
            );
            assert!(
                has_current,
                "current_contains (guard side) should appear as an alternative: {triggers:?}"
            );
            assert!(
                triggers.len() >= 2,
                "should have at least two alternative patterns: {triggers:?}"
            );
        }
        other => panic!("expected forall, got {other:?}"),
    }
}

#[test]
fn relax_single_var_multitriggers_retargets_fmap_reverse_to_next_contains() {
    let other_key = int_var("__fmap_iter_other_key");
    let entry_key = int_var("entry_key");
    let current_iter = PureExpr::View(Arc::new(fmap_var("iter_state")));
    let next_iter = PureExpr::View(Arc::new(fmap_var("iter_state_next")));
    let current_contains = method_call(current_iter.clone(), "contains", vec![other_key.clone()]);
    let current_lookup = method_call(current_iter, "lookup", vec![other_key.clone()]);
    let next_contains = method_call(next_iter.clone(), "contains", vec![other_key.clone()]);
    let next_lookup = method_call(next_iter, "lookup", vec![other_key.clone()]);
    let fact = PureExpr::Forall {
        var: "__fmap_iter_other_key".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(next_contains.clone()),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(other_key),
                    BinOp::Ne,
                    Arc::new(entry_key),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(current_contains.clone()),
                    BinOp::And,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(current_lookup),
                        BinOp::Eq,
                        Arc::new(next_lookup.clone()),
                    )),
                )),
            )),
        )),
        triggers: vec![vec![next_contains.clone(), next_lookup]],
    };

    let rewritten = relax_single_var_multitriggers(&fact);
    match rewritten {
        PureExpr::Forall { triggers, .. } => {
            // All alternative patterns should be singletons (len == 1).
            assert!(
                triggers.iter().all(|p| p.len() == 1),
                "all retargeted patterns should be singletons: {triggers:?}"
            );
            // With implication-aware scoring (#2696), consequent-side triggers
            // are preferred. The consequent is `(other_key != entry_key) && current_contains && (current_lookup == next_lookup)`,
            // so `current_contains` (consequent side) ranks higher than `next_contains`
            // (guard side). Both should appear as alternative patterns.
            let current_contains_expected = method_call(
                PureExpr::View(Arc::new(fmap_var("iter_state"))),
                "contains",
                vec![int_var("__fmap_iter_other_key")],
            );
            let next_contains_expected = method_call(
                PureExpr::View(Arc::new(fmap_var("iter_state_next"))),
                "contains",
                vec![int_var("__fmap_iter_other_key")],
            );
            let has_current = triggers
                .iter()
                .any(|p| p == &[current_contains_expected.clone()]);
            let has_next = triggers
                .iter()
                .any(|p| p == &[next_contains_expected.clone()]);
            assert!(
                has_current,
                "current_contains (consequent side) should appear as an alternative: {triggers:?}"
            );
            assert!(
                has_next,
                "next_contains (guard side) should appear as an alternative: {triggers:?}"
            );
            assert!(
                triggers.len() >= 2,
                "should have at least two alternative patterns: {triggers:?}"
            );
        }
        other => panic!("expected forall, got {other:?}"),
    }
}

#[test]
fn inject_forall_triggers_rewrites_quantifiers_inside_let_body() {
    let inner_trigger = logic_call("inner_pred", vec![int_var("y")]);
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(PureExpr::Int(0)),
        body: Arc::new(PureExpr::Forall {
            var: "y".to_string(),
            var_sort: None,
            body: Arc::new(inner_trigger.clone()),
            triggers: vec![],
        }),
    };

    let injected = inject_forall_triggers(&expr);
    match injected {
        PureExpr::Let { body, .. } => match body.as_ref() {
            PureExpr::Forall { triggers, .. } => {
                assert_eq!(triggers, &vec![vec![inner_trigger]]);
            }
            other => panic!("expected let body to stay forall, got {other:?}"),
        },
        other => panic!("expected let expression, got {other:?}"),
    }
}

#[test]
fn inject_forall_triggers_rewrites_quantifiers_inside_match_arms() {
    let arm_trigger = logic_call("arm_pred", vec![int_var("z")]);
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Bool(true)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::Exists {
                var: "z".to_string(),
                var_sort: None,
                body: Arc::new(arm_trigger.clone()),
                triggers: vec![],
            },
        }],
    };

    let injected = inject_forall_triggers(&expr);
    match injected {
        PureExpr::Match { arms, .. } => match &arms[0].body {
            PureExpr::Exists { triggers, .. } => {
                assert_eq!(triggers, &vec![vec![arm_trigger]]);
            }
            other => panic!("expected match arm body to stay exists, got {other:?}"),
        },
        other => panic!("expected match expression, got {other:?}"),
    }
}

// =============================================================================
// normalize_fmap_get_biconditional tests (#2116)
// =============================================================================

fn fmap_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn fmap_get(receiver: PureExpr, key: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "get".to_string(),
        args: vec![key],
    }
}

fn some_ctor(value: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: "std::option::Option::Some".to_string(),
        args: vec![value],
    }
}

fn get_eq_some(receiver: PureExpr, key: PureExpr, value: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(fmap_get(receiver, key)),
        BinOp::Eq,
        Arc::new(some_ctor(value)),
    )
}

#[test]
#[allow(clippy::many_single_char_names)] // short names (k, v, a, b, c) conventional for quantifier test vars
fn normalize_fmap_biconditional_rewrites_doubly_quantified() {
    let k = int_var("k");
    let v = int_var("v");
    let a = fmap_var("m_snap");
    let b = fmap_var("result");
    let c = fmap_var("iter_view");

    let expr = PureExpr::Forall {
        var: "k".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(get_eq_some(a.clone(), k.clone(), v.clone())),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(get_eq_some(b.clone(), k.clone(), v.clone())),
                    BinOp::Or,
                    Arc::new(get_eq_some(c.clone(), k.clone(), v.clone())),
                )),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    let normalized = normalize_fmap_get_biconditional(&expr);

    // Should be a single Forall (inner v eliminated).
    let PureExpr::Forall {
        var,
        body,
        triggers,
        ..
    } = &normalized
    else {
        panic!("expected Forall, got {normalized:?}");
    };
    assert_eq!(var, "k");
    assert!(
        triggers.is_empty(),
        "triggers should be empty for later synthesis"
    );

    // Body should NOT contain an inner Forall.
    assert!(
        !body.any_recursive(|e| matches!(e, PureExpr::Forall { .. })),
        "inner Forall should be eliminated"
    );

    // Body should contain contains and lookup method calls.
    let mut has_contains = false;
    let mut has_lookup = false;
    body.for_each_recursive(|e| {
        if let PureExpr::MethodCall { method, .. } = e {
            if method == "contains" {
                has_contains = true;
            }
            if method == "lookup" {
                has_lookup = true;
            }
        }
    });
    assert!(has_contains, "normalized body should use contains");
    assert!(has_lookup, "normalized body should use lookup");
}

#[test]
fn normalize_fmap_biconditional_preserves_singly_quantified() {
    // Singly-quantified invariant — should pass through unchanged.
    let k = int_var("k");
    let contains_a = PureExpr::MethodCall {
        receiver: Arc::new(fmap_var("m")),
        method: "contains".to_string(),
        args: vec![k.clone()],
    };
    let contains_b = PureExpr::MethodCall {
        receiver: Arc::new(fmap_var("r")),
        method: "contains".to_string(),
        args: vec![k],
    };
    let expr = PureExpr::Forall {
        var: "k".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(contains_a),
            BinOp::Eq,
            Arc::new(contains_b),
        )),
        triggers: vec![],
    };

    let normalized = normalize_fmap_get_biconditional(&expr);
    assert_eq!(normalized, expr, "singly-quantified should be unchanged");
}

#[test]
#[allow(clippy::many_single_char_names)] // short names (k, v, a, b, c) conventional for quantifier test vars
fn normalize_fmap_biconditional_preserves_with_explicit_triggers() {
    let k = int_var("k");
    let v = int_var("v");
    let a = fmap_var("m");
    let b = fmap_var("r");
    let c = fmap_var("it");

    // Same pattern but with explicit triggers — should NOT be normalized.
    let trigger = fmap_get(a.clone(), k.clone());
    let expr = PureExpr::Forall {
        var: "k".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(get_eq_some(a, k.clone(), v.clone())),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(get_eq_some(b, k.clone(), v.clone())),
                    BinOp::Or,
                    Arc::new(get_eq_some(c, k, v)),
                )),
            )),
            triggers: vec![],
        }),
        triggers: vec![vec![trigger]],
    };

    let normalized = normalize_fmap_get_biconditional(&expr);
    // Outer triggers present → skip normalization.
    assert!(
        normalized.any_recursive(|e| matches!(e, PureExpr::Forall { var, .. } if var == "v")),
        "should preserve inner Forall when outer has explicit triggers"
    );
}
