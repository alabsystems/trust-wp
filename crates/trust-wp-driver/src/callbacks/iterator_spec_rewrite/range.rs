// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Range iterator `produces`/`completed` rewriting.
//!
//! Rewrites:
//! - `range.produces(visited, next)` → content-aware arithmetic formula
//! - `range.completed()` → `range.start_log() >= range.end_log()`
//!
//! Reference: `reference/creusot/creusot-std/src/std/iter/range.rs:7-34`

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    helpers::{receiver_datatype_id, sort_matches_any, RANGE_SORT_NAMES},
    rewrite_expr,
};

/// Returns `true` if the receiver's Datatype sort matches `Range<T>`.
fn is_range_receiver(receiver: &PureExpr) -> bool {
    receiver_datatype_id(receiver).is_some_and(|id| sort_matches_any(id, RANGE_SORT_NAMES))
}

/// Build `receiver.start_log()` accessor call.
fn start_log(receiver: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: "start_log".to_string(),
        args: vec![],
    }
}

/// Build `receiver.end_log()` accessor call.
fn end_log(receiver: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: "end_log".to_string(),
        args: vec![],
    }
}

/// Build `seq.len()`.
fn seq_len(seq: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(seq.clone()),
        method: "len".to_string(),
        args: vec![],
    }
}

/// Build `seq.index_logic(idx)`.
fn seq_index(seq: &PureExpr, idx: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(seq.clone()),
        method: "index_logic".to_string(),
        args: vec![idx.clone()],
    }
}

/// Build `a && b`.
fn and(a: PureExpr, b: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(a), BinOp::And, Arc::new(b))
}

/// Build `a ==> b`.
fn implies(a: PureExpr, b: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(a), BinOp::Implies, Arc::new(b))
}

/// `forall<i: Int> 0 <= i && i < visited.len() ==> visited[i] == recv.start_log() + i`
fn element_identity_forall(visited: &PureExpr, recv: &PureExpr) -> PureExpr {
    let i_var = PureExpr::Var("__range_i".to_string(), Some(ExprSort::Int));
    let trigger = seq_index(visited, &i_var);
    let body = implies(
        and(
            PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Le,
                Arc::new(i_var.clone()),
            ),
            PureExpr::BinOp(
                Arc::new(i_var.clone()),
                BinOp::Lt,
                Arc::new(seq_len(visited)),
            ),
        ),
        PureExpr::BinOp(
            Arc::new(seq_index(visited, &i_var)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(start_log(recv)),
                BinOp::Add,
                Arc::new(i_var),
            )),
        ),
    );
    PureExpr::Forall {
        var: "__range_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![vec![trigger]],
    }
}

/// Rewrite `range.produces(visited, next)` to the content-aware arithmetic
/// formula from the Creusot spec.
///
/// ```text
/// range.end_log() == next.end_log()
/// && range.start_log() <= next.start_log()
/// && (visited.len() > 0 ==> next.start_log() <= next.end_log())
/// && visited.len() == next.start_log() - range.start_log()
/// && forall<i: Int> 0 <= i && i < visited.len() ==>
///     visited.index_logic(i) == range.start_log() + i
/// ```
fn rewrite_range_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);
    let recv = rewrite_expr(receiver);

    // clause 1: range.end_log() == next.end_log()
    let c1 = PureExpr::BinOp(
        Arc::new(end_log(&recv)),
        BinOp::Eq,
        Arc::new(end_log(&next)),
    );

    // clause 2: range.start_log() <= next.start_log()
    let c2 = PureExpr::BinOp(
        Arc::new(start_log(&recv)),
        BinOp::Le,
        Arc::new(start_log(&next)),
    );

    // clause 3: visited.len() > 0 ==> next.start_log() <= next.end_log()
    let c3 = implies(
        PureExpr::BinOp(
            Arc::new(seq_len(&visited)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(start_log(&next)),
            BinOp::Le,
            Arc::new(end_log(&next)),
        ),
    );

    // clause 4: visited.len() == next.start_log() - range.start_log()
    let c4 = PureExpr::BinOp(
        Arc::new(seq_len(&visited)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(start_log(&next)),
            BinOp::Sub,
            Arc::new(start_log(&recv)),
        )),
    );

    let c5 = element_identity_forall(&visited, &recv);

    Some(and(c1, and(c2, and(c3, and(c4, c5)))))
}

/// Rewrite `range.completed()` → `range.start_log() >= range.end_log()`.
fn rewrite_range_completed(receiver: &PureExpr) -> PureExpr {
    let recv = rewrite_expr(receiver);
    PureExpr::BinOp(
        Arc::new(start_log(&recv)),
        BinOp::Ge,
        Arc::new(end_log(&recv)),
    )
}

/// Try to rewrite a `produces` or `completed` method call on a Range receiver.
pub(super) fn try_rewrite_range_method(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
) -> Option<PureExpr> {
    if !is_range_receiver(receiver) {
        return None;
    }
    match method {
        "produces" => rewrite_range_produces(receiver, args),
        "completed" => Some(rewrite_range_completed(receiver)),
        _ => None,
    }
}
