// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof coverage tests for `skolemize_negated_universal`.
//!
//! Validates Skolemization of negated universal quantifiers — the mechanism
//! that converts `forall x. P(x)` into `NOT P(sk_x)` for SMT ground-pool
//! instantiation. Tests cover: non-universal rejection, exists rejection,
//! single/nested/triple forall Skolemization, sort preservation, and
//! literal/binop rejection.
//!
//! Part of #2202, #2106

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

use crate::verify::function::axiom_detection::skolemize_negated_universal;

#[test]
#[timeout(30000)]
fn non_universal_returns_none() {
    let expr = PureExpr::Var("x".to_string(), None);
    assert!(
        skolemize_negated_universal(&expr).is_none(),
        "non-universal expr should return None"
    );
}

#[test]
#[timeout(30000)]
fn exists_returns_none() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    assert!(
        skolemize_negated_universal(&expr).is_none(),
        "exists should NOT be Skolemized"
    );
}

#[test]
#[timeout(30000)]
fn single_forall_skolemizes() {
    // forall x. x > 0  →  NOT (sk_x > 0)
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![],
    };
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");
    match &result {
        PureExpr::UnOp(UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::BinOp(lhs, BinOp::Gt, _) => {
                assert!(
                    matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "sk$x"),
                    "Skolem constant should be sk_x, got {lhs:?}"
                );
            }
            _ => panic!("expected BinOp body, got {inner:?}"),
        },
        _ => panic!("expected Not(...), got {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn nested_forall_skolemizes_both() {
    // forall x. forall y. x == y  →  NOT (sk_x == sk_y)
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "y".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");
    match &result {
        PureExpr::UnOp(UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
                assert!(
                    matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "sk$x"),
                    "first Skolem should be sk_x, got {lhs:?}"
                );
                assert!(
                    matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "sk$y"),
                    "second Skolem should be sk_y, got {rhs:?}"
                );
            }
            _ => panic!("expected BinOp(Eq), got {inner:?}"),
        },
        _ => panic!("expected Not(...), got {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn sort_annotations_preserved() {
    // forall x: Bool. x  →  NOT sk_x (Bool-sorted)
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Bool))),
        triggers: vec![],
    };
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");
    match &result {
        PureExpr::UnOp(UnOp::Not, inner) => {
            assert!(
                matches!(inner.as_ref(), PureExpr::Var(name, Some(ExprSort::Bool)) if name == "sk$x"),
                "Skolem should preserve Bool sort, got {inner:?}"
            );
        }
        _ => panic!("expected Not(...), got {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn triple_nested_forall() {
    // forall x. forall y. forall z. x + y == z  →  NOT (sk_x + sk_y == sk_z)
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "y".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Forall {
                var: "z".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                        BinOp::Add,
                        Arc::new(PureExpr::Var("y".to_string(), None)),
                    )),
                    BinOp::Eq,
                    Arc::new(PureExpr::Var("z".to_string(), None)),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");
    match &result {
        PureExpr::UnOp(UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
                match lhs.as_ref() {
                    PureExpr::BinOp(a, BinOp::Add, b) => {
                        assert!(matches!(a.as_ref(), PureExpr::Var(n, _) if n == "sk$x"));
                        assert!(matches!(b.as_ref(), PureExpr::Var(n, _) if n == "sk$y"));
                    }
                    _ => panic!("expected Add, got {lhs:?}"),
                }
                assert!(matches!(rhs.as_ref(), PureExpr::Var(n, _) if n == "sk$z"));
            }
            _ => panic!("expected BinOp(Eq), got {inner:?}"),
        },
        _ => panic!("expected Not(...), got {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn binop_returns_none() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(1)),
        BinOp::Add,
        Arc::new(PureExpr::Int(2)),
    );
    assert!(skolemize_negated_universal(&expr).is_none());
}

#[test]
#[timeout(30000)]
fn bool_literal_returns_none() {
    assert!(skolemize_negated_universal(&PureExpr::Bool(true)).is_none());
}
