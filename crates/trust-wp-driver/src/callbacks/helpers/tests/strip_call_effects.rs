// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[test]
fn strip_call_effects_top_level_let_assume() {
    // LetAssume at top-level should be stripped
    let body = PureExpr::Int(0);
    let assumption = PureExpr::Var("postcond".into(), None);
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(assumption.clone()),
        body: Arc::new(body.clone()),
    };
    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    let stripped = strip_call_effects(&expr, &mut assumptions, &mut obligations);
    assert_eq!(assumptions.len(), 1, "should strip one assumption");
    assert_eq!(stripped, body);
}

#[test]
fn strip_call_effects_top_level_let_obligation() {
    // LetObligation at top-level should be stripped
    let body = PureExpr::Int(0);
    let obligation = PureExpr::Var("precond".into(), None);
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(obligation.clone()),
        body: Arc::new(body.clone()),
    };
    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    let stripped = strip_call_effects(&expr, &mut assumptions, &mut obligations);
    assert_eq!(obligations.len(), 1, "should strip one obligation");
    assert_eq!(stripped, body);
}

/// Regression test for #927:
/// Ite-nested call assumptions must be extracted with path guards so
/// branch-local effects do not leak globally.
#[test]
fn strip_call_effects_extracts_ite_nested_let_assume_with_branch_guards() {
    let marker = PureExpr::Int(0);
    let cond = PureExpr::Var("cond".into(), None);
    let assume_then = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Var("postcond_then".into(), None)),
        body: Arc::new(marker.clone()),
    };
    let assume_else = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Var("postcond_else".into(), None)),
        body: Arc::new(marker.clone()),
    };
    let ite = PureExpr::Ite(
        Arc::new(cond.clone()),
        Arc::new(assume_then),
        Arc::new(assume_else),
    );
    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    let stripped = strip_call_effects(&ite, &mut assumptions, &mut obligations);

    assert_eq!(
        assumptions,
        vec![
            PureExpr::BinOp(
                Arc::new(cond.clone()),
                BinOp::Implies,
                Arc::new(PureExpr::Var("postcond_then".into(), None))
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(cond.clone()))),
                BinOp::Implies,
                Arc::new(PureExpr::Var("postcond_else".into(), None))
            ),
        ],
        "branch assumptions must be extracted with path guards"
    );
    assert!(obligations.is_empty(), "no obligations in this expression");
    assert_eq!(
        stripped,
        PureExpr::Ite(Arc::new(cond), Arc::new(marker.clone()), Arc::new(marker),)
    );
}

#[test]
fn strip_call_effects_chained_let_assume_and_obligation() {
    let marker = PureExpr::Int(0);
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Var("precond".into(), None)),
        body: Arc::new(PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::Var("postcond".into(), None)),
            body: Arc::new(marker.clone()),
        }),
    };
    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    let stripped = strip_call_effects(&expr, &mut assumptions, &mut obligations);
    assert_eq!(obligations.len(), 1);
    assert_eq!(assumptions.len(), 1);
    assert_eq!(stripped, marker);
}

#[test]
fn strip_call_effects_extracts_nested_ite_obligations_with_conjoined_path() {
    let marker = PureExpr::Int(0);
    let cond_outer = PureExpr::Var("outer".into(), None);
    let cond_inner = PureExpr::Var("inner".into(), None);
    let expr = PureExpr::Ite(
        Arc::new(cond_outer.clone()),
        Arc::new(PureExpr::Ite(
            Arc::new(cond_inner.clone()),
            Arc::new(PureExpr::LetObligation {
                obligation: Arc::new(PureExpr::Var("pre_then_then".into(), None)),
                body: Arc::new(marker.clone()),
            }),
            Arc::new(PureExpr::LetObligation {
                obligation: Arc::new(PureExpr::Var("pre_then_else".into(), None)),
                body: Arc::new(marker.clone()),
            }),
        )),
        Arc::new(PureExpr::LetObligation {
            obligation: Arc::new(PureExpr::Var("pre_else".into(), None)),
            body: Arc::new(marker.clone()),
        }),
    );

    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    let stripped = strip_call_effects(&expr, &mut assumptions, &mut obligations);

    assert!(assumptions.is_empty(), "no assumptions in this expression");
    assert_eq!(
        obligations,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(cond_outer.clone()),
                    BinOp::And,
                    Arc::new(cond_inner.clone())
                )),
                BinOp::Implies,
                Arc::new(PureExpr::Var("pre_then_then".into(), None))
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(cond_outer.clone()),
                    BinOp::And,
                    Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(cond_inner.clone())))
                )),
                BinOp::Implies,
                Arc::new(PureExpr::Var("pre_then_else".into(), None))
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(cond_outer.clone()))),
                BinOp::Implies,
                Arc::new(PureExpr::Var("pre_else".into(), None))
            ),
        ],
        "obligations must preserve nested branch scope"
    );
    assert_eq!(
        stripped,
        PureExpr::Ite(
            Arc::new(cond_outer),
            Arc::new(PureExpr::Ite(
                Arc::new(cond_inner),
                Arc::new(marker.clone()),
                Arc::new(marker.clone()),
            )),
            Arc::new(marker),
        )
    );
}
