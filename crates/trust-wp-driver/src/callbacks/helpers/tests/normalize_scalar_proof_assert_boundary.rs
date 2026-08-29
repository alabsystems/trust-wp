// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[test]
fn normalize_scalar_proof_assert_boundary_materializes_view_of_deref_current_var() {
    let rc_sort = ExprSort::Datatype(intern_sort_name("alloc::rc::Rc"));
    let mut preconditions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "call_1".to_string(),
            Some(rc_sort.clone()),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    )];
    let mut ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("call_1".to_string(), Some(rc_sort)),
        ))))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    )];
    let mut return_expr = None;

    normalize_scalar_proof_assert_boundary(&mut preconditions, &mut ensures, &mut return_expr);

    assert_eq!(
        ensures,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                "call_1_current".to_string(),
                Some(ExprSort::Int),
            )),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        )],
        "View(Deref(call_1)) should collapse to an Int-sorted current var once the proof_assert boundary learns the scalar pointee sort"
    );
}

#[test]
fn normalize_scalar_proof_assert_boundary_reuses_current_sorts_in_ptr_eq_biconditional() {
    let rc_sort = ExprSort::Datatype(intern_sort_name("alloc::rc::Rc"));
    let deref_call_1 = PureExpr::Deref(Arc::new(PureExpr::Var(
        "call_1".to_string(),
        Some(rc_sort.clone()),
    )));
    let deref_call_2 = PureExpr::Deref(Arc::new(PureExpr::Var(
        "call_2".to_string(),
        Some(rc_sort.clone()),
    )));
    let mut preconditions = vec![
        PureExpr::BinOp(
            Arc::new(deref_call_1.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        ),
        PureExpr::BinOp(
            Arc::new(deref_call_2.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("call_3".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(deref_call_1),
                BinOp::Eq,
                Arc::new(deref_call_2),
            )),
        ),
    ];
    let mut ensures = vec![PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::Var("call_3".to_string(), Some(ExprSort::Bool))),
    )];
    let mut return_expr = None;

    normalize_scalar_proof_assert_boundary(&mut preconditions, &mut ensures, &mut return_expr);

    assert_eq!(
        preconditions[2],
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("call_3".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var(
                    "call_1_current".to_string(),
                    Some(ExprSort::Int),
                )),
                BinOp::Eq,
                Arc::new(PureExpr::Var(
                    "call_2_current".to_string(),
                    Some(ExprSort::Int),
                )),
            )),
        ),
        "ptr_eq's inner-value biconditional should compare Int-sorted current vars, not Rc handle vars"
    );
}
