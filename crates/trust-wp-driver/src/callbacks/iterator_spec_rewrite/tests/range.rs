// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

use super::{
    datatype_var, flattened_and_clauses, make_completed, make_produces, range_var, rewrite_expr,
    seq_var, wrapped_receiver,
};

fn assert_range_end_clause(clause: &PureExpr) {
    let PureExpr::BinOp(end_l, eq_op, end_r) = clause else {
        panic!("expected end_log Eq, got {clause:?}");
    };
    assert_eq!(*eq_op, BinOp::Eq);
    assert!(
        matches!(end_l.as_ref(), PureExpr::MethodCall { method, receiver, args }
        if method == "end_log"
        && args.is_empty()
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "r"))
    );
    assert!(
        matches!(end_r.as_ref(), PureExpr::MethodCall { method, receiver, args }
        if method == "end_log"
        && args.is_empty()
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next"))
    );
}

fn assert_range_start_clause(clause: &PureExpr) {
    let PureExpr::BinOp(start_l, le_op, start_r) = clause else {
        panic!("expected start_log Le, got {clause:?}");
    };
    assert_eq!(*le_op, BinOp::Le);
    assert!(
        matches!(start_l.as_ref(), PureExpr::MethodCall { method, receiver, args }
        if method == "start_log"
        && args.is_empty()
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "r"))
    );
    assert!(
        matches!(start_r.as_ref(), PureExpr::MethodCall { method, receiver, args }
        if method == "start_log"
        && args.is_empty()
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next"))
    );
}

fn assert_range_nonempty_clause(clause: &PureExpr) {
    let PureExpr::BinOp(premise, implies_op, consequence) = clause else {
        panic!("expected implication clause, got {clause:?}");
    };
    assert_eq!(*implies_op, BinOp::Implies);
    assert!(
        matches!(premise.as_ref(), PureExpr::BinOp(lhs, BinOp::Gt, rhs)
        if matches!(rhs.as_ref(), PureExpr::Int(0))
        && matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "len"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")))
    );
    assert!(
        matches!(consequence.as_ref(), PureExpr::BinOp(lhs, BinOp::Le, rhs)
        if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "start_log"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next"))
        && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "end_log"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );
}

fn assert_range_len_clause(clause: &PureExpr) {
    let PureExpr::BinOp(lhs, eq_op, rhs) = clause else {
        panic!("expected length equation clause, got {clause:?}");
    };
    assert_eq!(*eq_op, BinOp::Eq);
    assert!(
        matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
        if method == "len"
        && args.is_empty()
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))
    );
    assert!(
        matches!(rhs.as_ref(), PureExpr::BinOp(sub_lhs, BinOp::Sub, sub_rhs)
        if matches!(sub_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "start_log"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next"))
        && matches!(sub_rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "start_log"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "r")))
    );
}

fn assert_range_forall_clause(clause: &PureExpr) {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = clause
    else {
        panic!("expected forall clause, got {clause:?}");
    };
    assert_eq!(var, "__range_i");
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, receiver, args }
        if method == "index_logic"
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
        && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__range_i"))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(bounds, BinOp::Implies, eq)
        if matches!(bounds.as_ref(), PureExpr::BinOp(lower, BinOp::And, upper)
            if matches!(lower.as_ref(), PureExpr::BinOp(lhs, BinOp::Le, rhs)
                if matches!(lhs.as_ref(), PureExpr::Int(0))
                && matches!(rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__range_i"))
            && matches!(upper.as_ref(), PureExpr::BinOp(lhs, BinOp::Lt, rhs)
                if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__range_i")
                && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "len"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))))
        && matches!(eq.as_ref(), PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "index_logic"
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
                && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__range_i"))
            && matches!(rhs.as_ref(), PureExpr::BinOp(sum_lhs, BinOp::Add, sum_rhs)
                if matches!(sum_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "start_log"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "r"))
                && matches!(sum_rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__range_i"))))
    );
}

#[test]
fn test_range_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        range_var("r"),
        seq_var("visited"),
        range_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [c1, c2, c3, c4, c5] = clauses.as_slice() else {
        panic!("expected 5 conjunction clauses, got {clauses:?}");
    };

    assert_range_end_clause(c1);
    assert_range_start_clause(c2);
    assert_range_nonempty_clause(c3);
    assert_range_len_clause(c4);
    assert_range_forall_clause(c5);
}

#[test]
fn test_range_alias_sorts_rewrite() {
    for sort_name in ["std::ops::Range", "core::ops::Range"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("r", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let clauses = flattened_and_clauses(&rewritten);
        assert_eq!(
            clauses.len(),
            5,
            "{sort_name} should rewrite to five conjunction clauses"
        );
    }
}

#[test]
fn test_range_produces_rewrite_for_mutref_receiver() {
    let range_id = intern_sort_name("core::ops::range::Range");
    let range_ref = |name: &str| {
        PureExpr::Var(
            name.to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(range_id)))),
        )
    };

    let rewritten = rewrite_expr(&make_produces(
        range_ref("r"),
        seq_var("visited"),
        range_ref("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [c1, c2, c3, c4, c5] = clauses.as_slice() else {
        panic!("expected 5 conjunction clauses, got {clauses:?}");
    };

    assert_range_end_clause(c1);
    assert_range_start_clause(c2);
    assert_range_nonempty_clause(c3);
    assert_range_len_clause(c4);
    assert_range_forall_clause(c5);
}

#[test]
fn test_range_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(range_var("r")));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Ge);
    assert!(matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "start_log"));
    assert!(matches!(rhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "end_log"));
}

#[test]
fn test_range_completed_rewrite_through_old_final_view() {
    let rewritten = rewrite_expr(&make_completed(wrapped_receiver(range_var("r"))));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Ge);
    assert!(
        matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "start_log"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::View(inner)
                    if matches!(inner.as_ref(), PureExpr::Old(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "r")))))
    );
    assert!(
        matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "end_log"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::View(inner)
                    if matches!(inner.as_ref(), PureExpr::Old(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "r")))))
    );
}

#[test]
fn test_range_completed_rewrite_for_mutref_receiver() {
    let range_id = intern_sort_name("core::ops::range::Range");
    let rewritten = rewrite_expr(&make_completed(PureExpr::Var(
        "r".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(range_id)))),
    )));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Ge);
    assert!(matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "start_log"));
    assert!(matches!(rhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "end_log"));
}

#[test]
fn test_range_non_produces_unchanged() {
    let rewritten = rewrite_expr(&PureExpr::MethodCall {
        receiver: Arc::new(range_var("r")),
        method: "len".to_string(),
        args: vec![],
    });
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "len");
}
