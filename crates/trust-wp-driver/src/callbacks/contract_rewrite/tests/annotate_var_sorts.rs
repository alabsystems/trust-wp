// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn annotate_var_sorts_updates_triggers_and_match_bodies() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("bound".to_string()),
                body: PureExpr::Var("result".to_string(), None),
            }],
        }),
        triggers: vec![vec![PureExpr::Var("x".to_string(), None)]],
    };
    let sort_map = HashMap::from([
        ("x".to_string(), ExprSort::Seq),
        ("result".to_string(), ExprSort::Bool),
    ]);

    let rewritten = annotate_var_sorts(&expr, &sort_map);

    match rewritten {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            assert_eq!(var, "i");
            assert_eq!(var_sort, Some(ExprSort::Int));
            assert_eq!(
                triggers,
                vec![vec![PureExpr::Var("x".to_string(), Some(ExprSort::Seq))]]
            );
            match body.as_ref() {
                PureExpr::Match { scrutinee, arms } => {
                    assert_eq!(
                        scrutinee.as_ref(),
                        &PureExpr::Var("x".to_string(), Some(ExprSort::Seq))
                    );
                    assert_eq!(arms.len(), 1);
                    assert_eq!(arms[0].pattern, Pattern::Binding("bound".to_string()));
                    assert_eq!(
                        arms[0].body,
                        PureExpr::Var("result".to_string(), Some(ExprSort::Bool))
                    );
                }
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

// --- Closure capture sort annotation tests (#2668) ---
// When closures are verified, captures get substituted to self.N names.
// The sort annotation pass must handle both original and self.N names.

#[test]
fn test_annotate_var_sorts_closure_self_field_names() {
    // Sort map with both original and self.N forms, as produced by
    // propagate_closure_capture_sort_annotations.
    let sort_map = HashMap::from([
        ("bx".to_string(), ExprSort::MutRef(Box::new(ExprSort::Int))),
        (
            "self.0".to_string(),
            ExprSort::MutRef(Box::new(ExprSort::Int)),
        ),
        ("by".to_string(), ExprSort::MutRef(Box::new(ExprSort::Int))),
        (
            "self.1".to_string(),
            ExprSort::MutRef(Box::new(ExprSort::Int)),
        ),
    ]);

    // After capture substitution, contract has self.0 and self.1
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self.0".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("self.1".to_string(), None)),
    );

    let result = annotate_var_sorts(&expr, &sort_map);

    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                "self.0".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )),
            BinOp::Add,
            Arc::new(PureExpr::Var(
                "self.1".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )),
        )
    );
}

#[test]
fn test_annotate_var_sorts_closure_old_wrapped() {
    // Old(Var("self.0")) should get annotated
    let sort_map = HashMap::from([(
        "self.0".to_string(),
        ExprSort::MutRef(Box::new(ExprSort::Int)),
    )]);

    let expr = PureExpr::Old(Arc::new(PureExpr::Var("self.0".to_string(), None)));

    let result = annotate_var_sorts(&expr, &sort_map);

    assert_eq!(
        result,
        PureExpr::Old(Arc::new(PureExpr::Var(
            "self.0".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
        )))
    );
}
