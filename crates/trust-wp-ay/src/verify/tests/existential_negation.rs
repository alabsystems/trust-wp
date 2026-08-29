// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;

use crate::{
    encoder::AYEncoder,
    tests::helpers::{and, binop, exists_with_sort, not, var},
    verify::negate_existential_postcondition,
    BinOp, ExprSort, PureExpr, UnOp,
};

// --- negate_existential_postcondition ---

#[test]
#[timeout(30000)]
fn negate_non_existential_returns_none() {
    assert!(
        negate_existential_postcondition(&var("x")).is_none(),
        "non-existential expression should return None"
    );
}

#[test]
#[timeout(30000)]
fn negate_nested_existentials_rewrites_to_nested_foralls() {
    let outer_triggers = vec![vec![var("a")]];
    let inner_triggers = vec![vec![var("b")]];
    let predicate = binop(var("a"), BinOp::Lt, var("b"));
    let expr = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Exists {
            var: "b".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(predicate.clone()),
            triggers: inner_triggers.clone(),
        }),
        triggers: outer_triggers.clone(),
    };

    let negated =
        negate_existential_postcondition(&expr).expect("top-level existential should be rewritten");

    match negated {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            assert_eq!(var, "a");
            assert_eq!(var_sort, Some(ExprSort::Int));
            assert_eq!(triggers, outer_triggers);
            match body.as_ref() {
                PureExpr::Forall {
                    var,
                    var_sort,
                    body,
                    triggers,
                } => {
                    assert_eq!(var, "b");
                    assert_eq!(*var_sort, Some(ExprSort::Int));
                    assert_eq!(*triggers, inner_triggers);
                    match body.as_ref() {
                        PureExpr::UnOp(UnOp::Not, inner) => {
                            assert_eq!(inner.as_ref(), &predicate);
                        }
                        other => panic!("expected inner negation, got {other:?}"),
                    }
                }
                other => panic!("expected nested forall, got {other:?}"),
            }
        }
        other => panic!("expected forall rewrite, got {other:?}"),
    }
}

/// The `expect()` in `negate_existential_postcondition` relies on the
/// `if matches!(body, Exists{..})` guard ensuring the recursive call
/// always returns `Some(...)`. This test documents that guarantee by
/// verifying the recursive call on nested exists never returns `None`.
#[test]
#[timeout(30000)]
fn negate_nested_exists_recursive_call_always_returns_some() {
    // Inner exists: the recursive call target
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(var("b")),
        triggers: vec![],
    };
    // Verify: negate_existential_postcondition on an Exists always returns Some
    assert!(
        negate_existential_postcondition(&inner).is_some(),
        "negate_existential_postcondition on Exists must return Some"
    );

    // Triple nesting: each level returns Some
    let triple = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Exists {
            var: "b".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Exists {
                var: "c".to_string(),
                var_sort: None,
                body: Arc::new(var("c")),
                triggers: vec![],
            }),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    let result = negate_existential_postcondition(&triple);
    assert!(result.is_some(), "triple-nested exists must return Some");
    // Verify structure: forall<a> forall<b> forall<c> NOT c
    match result.unwrap() {
        PureExpr::Forall { var, body, .. } => {
            assert_eq!(var, "a");
            match body.as_ref() {
                PureExpr::Forall { var, body, .. } => {
                    assert_eq!(var, "b");
                    match body.as_ref() {
                        PureExpr::Forall { var, body, .. } => {
                            assert_eq!(var, "c");
                            assert!(
                                matches!(body.as_ref(), PureExpr::UnOp(UnOp::Not, _)),
                                "innermost forall body should be negated predicate, got {body:?}"
                            );
                        }
                        other => panic!("expected forall<c>, got {other:?}"),
                    }
                }
                other => panic!("expected forall<b>, got {other:?}"),
            }
        }
        other => panic!("expected forall<a>, got {other:?}"),
    }
}

/// Non-consecutive exists (exists under AND/OR) is NOT recursed into.
/// The De Morgan transform wraps the body in NOT, preserving the inner
/// exists structure.
#[test]
#[timeout(30000)]
fn negate_non_consecutive_exists_preserves_inner_structure() {
    // exists<a> (a AND exists<b> b) — inner exists is under AND, not direct child
    let inner_exists = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(var("b")),
        triggers: vec![],
    };
    let conjunction = binop(var("a"), BinOp::And, inner_exists.clone());
    let outer = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(conjunction),
        triggers: vec![],
    };

    let negated =
        negate_existential_postcondition(&outer).expect("outer exists should be rewritten");

    // Result: forall<a> NOT(a AND exists<b> b)
    match negated {
        PureExpr::Forall { var, body, .. } => {
            assert_eq!(var, "a");
            // Body should be NOT(a AND exists<b> b), NOT forall<b> ...
            match body.as_ref() {
                PureExpr::UnOp(UnOp::Not, inner) => {
                    // inner should be (a AND exists<b> b) — with exists preserved
                    match inner.as_ref() {
                        PureExpr::BinOp(_, BinOp::And, rhs) => {
                            assert!(
                                matches!(rhs.as_ref(), PureExpr::Exists { .. }),
                                "inner exists should be preserved, got {rhs:?}"
                            );
                        }
                        other => panic!("expected AND, got {other:?}"),
                    }
                }
                other => panic!("expected NOT wrapper, got {other:?}"),
            }
        }
        other => panic!("expected forall, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn negate_nested_existentials_matches_direct_negation_semantics() {
    // Bool-sorted quantifiers are expanded into finite case splits (#1027),
    // making this equivalence check solver-decidable and stable.
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort("b", ExprSort::Bool, and(var("a"), var("b"))),
    );
    let rewritten = negate_existential_postcondition(&original)
        .expect("top-level existential should be rewritten");

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let equivalent = binop(direct_negation, BinOp::Eq, rewritten);
    let violates_equivalence = not(equivalent);
    let violation_term = encoder
        .encode_pure(&violates_equivalence)
        .expect("equivalence check should encode");
    encoder.assert_term(violation_term);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "rewritten nested existential negation must match direct negation"
    );
}
