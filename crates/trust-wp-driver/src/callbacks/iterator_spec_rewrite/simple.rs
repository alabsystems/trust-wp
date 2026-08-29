// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple iterator method rewrites: Vec::IntoIter + trivial adapters.
//!
//! For `Vec::IntoIter`, rewrites:
//! - `receiver.produces(visited, next)` → `receiver@.ext_eq(visited.concat(next@))`
//! - `receiver.completed()` → `receiver@.len() == 0`
//!
//! For `Empty<T>`:
//! - `empty.produces(visited, next)` → `visited.len() == 0`
//! - `empty.completed()` → `true`
//!
//! For `Once<T>`:
//! - `once.produces(visited, next)` → length-based disjunction (see below)
//! - `once.completed()` → `once@ == None`
//!
//! For `Repeat<T>`:
//! - `repeat.produces(visited, next)` → identity element forall (see below)
//! - `repeat.completed()` → `false`
//!
//! For `Fuse<I>`:
//! - `fuse.produces(visited, next)` → `fuse.iter().produces(visited, next.iter())`
//! - `fuse.completed()` → `fuse.iter().completed()`
//!
//! For `Cloned<I>` / `Copied<I>`:
//! - `*.produces(visited, next)` → existential inner-step sequence plus element
//!   dereference relation
//! - `*.completed()` → `*.iter().completed()`
//!
//! For `slice::IterMut`:
//! - `it.produces(visited, next)` → snapshot-aware length+content formula
//!   where `*visited[i]` gives the pre-mutation value (#2238)
//! - `it.completed()` → `it@.len() == 0`
//!
//! For `Map<I, F>`, `Filter<I, P>`, `FilterMap<I, F>`, `MapInv<I, F>`:
//! - `*.completed()` → `*.iter().completed()` (delegated inner completion)
//! - `*.produces(...)` → not rewritten (falls through to abstract UF)
//!   Full closure postcondition encoding deferred to Slice 3 (#2170).

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    helpers::{
        is_into_iter_receiver, receiver_datatype_id, sort_matches_any, CLONED_SORT_NAMES,
        COPIED_SORT_NAMES, EMPTY_SORT_NAMES, FILTER_MAP_SORT_NAMES, FILTER_SORT_NAMES,
        FUSE_SORT_NAMES, MAP_INV_SORT_NAMES, MAP_SORT_NAMES, ONCE_SORT_NAMES, REPEAT_SORT_NAMES,
        SEQ_ITER_SORT_NAMES, SLICE_ITER_MUT_SORT_NAMES, SLICE_ITER_SORT_NAMES,
    },
    rewrite_expr,
};

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn zero_arg_method(receiver: PureExpr, method: &str) -> PureExpr {
    method_call(receiver, method, vec![])
}

fn seq_len(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "len")
}

fn seq_index(receiver: PureExpr, index: PureExpr) -> PureExpr {
    method_call(receiver, "index_logic", vec![index])
}

fn make_iter_accessor(receiver: &PureExpr) -> PureExpr {
    zero_arg_method(rewrite_expr(receiver), "iter")
}

// ---------------------------------------------------------------------------
// Vec::IntoIter
// ---------------------------------------------------------------------------

fn rewrite_into_iter_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let receiver_view = PureExpr::View(Arc::new(rewrite_expr(receiver)));
    let visited = rewrite_expr(&args[0]);
    let next_view = PureExpr::View(Arc::new(rewrite_expr(&args[1])));

    let concat = PureExpr::MethodCall {
        receiver: Arc::new(visited),
        method: "concat".to_string(),
        args: vec![next_view],
    };
    Some(PureExpr::MethodCall {
        receiver: Arc::new(receiver_view),
        method: "ext_eq".to_string(),
        args: vec![concat],
    })
}

fn rewrite_into_iter_completed(receiver: &PureExpr) -> PureExpr {
    let receiver_view = PureExpr::View(Arc::new(rewrite_expr(receiver)));
    let len_call = PureExpr::MethodCall {
        receiver: Arc::new(receiver_view),
        method: "len".to_string(),
        args: vec![],
    };
    PureExpr::BinOp(Arc::new(len_call), BinOp::Eq, Arc::new(PureExpr::Int(0)))
}

/// Rewrites `receiver.produces_back(visited, next)` for `Vec::IntoIter` to:
/// `receiver@.ext_eq(next@.concat(visited.reverse()))`
///
/// This is the reverse analogue of the forward `produces` rewrite:
/// - forward: `receiver@.ext_eq(visited.concat(next@))`
/// - reverse: `receiver@.ext_eq(next@.concat(visited.reverse()))`
fn rewrite_into_iter_produces_back(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let receiver_view = PureExpr::View(Arc::new(rewrite_expr(receiver)));
    let visited = rewrite_expr(&args[0]);
    let next_view = PureExpr::View(Arc::new(rewrite_expr(&args[1])));

    // visited.reverse()
    let visited_rev = PureExpr::MethodCall {
        receiver: Arc::new(visited),
        method: "reverse".to_string(),
        args: vec![],
    };
    // next@.concat(visited.reverse())
    let concat = PureExpr::MethodCall {
        receiver: Arc::new(next_view),
        method: "concat".to_string(),
        args: vec![visited_rev],
    };
    Some(PureExpr::MethodCall {
        receiver: Arc::new(receiver_view),
        method: "ext_eq".to_string(),
        args: vec![concat],
    })
}

// ---------------------------------------------------------------------------
// Empty<T>
// ---------------------------------------------------------------------------

fn rewrite_empty_produces(args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let visited = rewrite_expr(&args[0]);
    // visited.len() == 0
    Some(PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(visited),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    ))
}

fn rewrite_empty_completed() -> PureExpr {
    PureExpr::Bool(true)
}

// ---------------------------------------------------------------------------
// Once<T>
// ---------------------------------------------------------------------------

/// Rewrites `once.produces(visited, next)` to:
/// ```text
/// (visited.len() == 0 && once@ == next@)
/// || (once@ != None && visited.len() == 1 && next@ == None)
/// ```
fn rewrite_once_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);

    let recv_view = PureExpr::View(Arc::new(recv));
    let next_view = PureExpr::View(Arc::new(next));
    let visited_len = PureExpr::MethodCall {
        receiver: Arc::new(visited),
        method: "len".to_string(),
        args: vec![],
    };

    // Branch 1: visited.len() == 0 && once@ == next@
    let branch1 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(visited_len.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(recv_view.clone()),
            BinOp::Eq,
            Arc::new(next_view.clone()),
        )),
    );

    // Branch 2: once@ != None && visited.len() == 1 && next@ == None
    let none_expr = PureExpr::Var("None".to_string(), None);
    let branch2 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(recv_view),
            BinOp::Ne,
            Arc::new(none_expr.clone()),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(visited_len),
                BinOp::Eq,
                Arc::new(PureExpr::Int(1)),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(next_view),
                BinOp::Eq,
                Arc::new(none_expr),
            )),
        )),
    );

    Some(PureExpr::BinOp(
        Arc::new(branch1),
        BinOp::Or,
        Arc::new(branch2),
    ))
}

/// Rewrites `once.completed()` → `once@ == None`.
fn rewrite_once_completed(receiver: &PureExpr) -> PureExpr {
    let recv_view = PureExpr::View(Arc::new(rewrite_expr(receiver)));
    PureExpr::BinOp(
        Arc::new(recv_view),
        BinOp::Eq,
        Arc::new(PureExpr::Var("None".to_string(), None)),
    )
}

// ---------------------------------------------------------------------------
// Repeat<T>
// ---------------------------------------------------------------------------

/// Rewrites `repeat.produces(visited, next)` to:
/// ```text
/// repeat@ == next@
/// && forall<i: Int> 0 <= i && i < visited.len() ==>
///     visited.index_logic(i) == repeat@
/// ```
fn rewrite_repeat_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);

    let recv_view = PureExpr::View(Arc::new(recv));
    let next_view = PureExpr::View(Arc::new(next));

    // clause 1: repeat@ == next@
    let c1 = PureExpr::BinOp(Arc::new(recv_view.clone()), BinOp::Eq, Arc::new(next_view));

    // clause 2: forall<i> 0 <= i && i < visited.len() ==> visited[i] == repeat@
    let i_var = PureExpr::Var("__repeat_i".to_string(), Some(ExprSort::Int));
    let visited_len = PureExpr::MethodCall {
        receiver: Arc::new(visited.clone()),
        method: "len".to_string(),
        args: vec![],
    };
    let visited_idx = PureExpr::MethodCall {
        receiver: Arc::new(visited),
        method: "index_logic".to_string(),
        args: vec![i_var.clone()],
    };

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Le,
                Arc::new(i_var.clone()),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(i_var),
                BinOp::Lt,
                Arc::new(visited_len),
            )),
        )),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(visited_idx.clone()),
            BinOp::Eq,
            Arc::new(recv_view),
        )),
    );

    let c2 = PureExpr::Forall {
        var: "__repeat_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![vec![visited_idx]],
    };

    Some(PureExpr::BinOp(Arc::new(c1), BinOp::And, Arc::new(c2)))
}

fn rewrite_repeat_completed() -> PureExpr {
    PureExpr::Bool(false)
}

// ---------------------------------------------------------------------------
// Fuse<I>
// ---------------------------------------------------------------------------

fn rewrite_fuse_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let visited = rewrite_expr(&args[0]);
    let next_iter = make_iter_accessor(&args[1]);
    Some(method_call(
        make_iter_accessor(receiver),
        "produces",
        vec![visited, next_iter],
    ))
}

fn rewrite_fuse_completed(receiver: &PureExpr) -> PureExpr {
    zero_arg_method(make_iter_accessor(receiver), "completed")
}

// ---------------------------------------------------------------------------
// Cloned<I> / Copied<I>
// ---------------------------------------------------------------------------

fn rewrite_deref_adapter_produces(
    receiver: &PureExpr,
    args: &[PureExpr],
    seq_var_name: &str,
    index_var_name: &str,
) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let visited = rewrite_expr(&args[0]);
    let inner_steps = PureExpr::Var(seq_var_name.to_string(), Some(ExprSort::Seq));
    let next_iter = make_iter_accessor(&args[1]);
    let inner_produces = method_call(
        make_iter_accessor(receiver),
        "produces",
        vec![inner_steps.clone(), next_iter],
    );
    let len_eq = PureExpr::BinOp(
        Arc::new(seq_len(visited.clone())),
        BinOp::Eq,
        Arc::new(seq_len(inner_steps.clone())),
    );

    let i_var = PureExpr::Var(index_var_name.to_string(), Some(ExprSort::Int));
    let visited_idx = seq_index(visited.clone(), i_var.clone());
    let inner_idx = seq_index(inner_steps.clone(), i_var.clone());
    let elem_relation = PureExpr::Forall {
        var: index_var_name.to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(i_var.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(i_var),
                    BinOp::Lt,
                    Arc::new(seq_len(inner_steps.clone())),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(visited_idx.clone()),
                BinOp::Eq,
                Arc::new(PureExpr::Deref(Arc::new(inner_idx.clone()))),
            )),
        )),
        triggers: vec![vec![visited_idx, inner_idx]],
    };

    Some(PureExpr::Exists {
        var: seq_var_name.to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(inner_produces),
                BinOp::And,
                Arc::new(len_eq),
            )),
            BinOp::And,
            Arc::new(elem_relation),
        )),
        triggers: vec![],
    })
}

fn rewrite_cloned_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    rewrite_deref_adapter_produces(receiver, args, "__cloned_steps", "__cloned_i")
}

fn rewrite_copied_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    rewrite_deref_adapter_produces(receiver, args, "__copied_steps", "__copied_i")
}

fn rewrite_delegated_completed(receiver: &PureExpr) -> PureExpr {
    zero_arg_method(make_iter_accessor(receiver), "completed")
}

// ---------------------------------------------------------------------------
// slice::IterMut — snapshot-aware produces (#2238)
// ---------------------------------------------------------------------------

/// Rewrites `it.produces(visited, next)` for `slice::IterMut` to a
/// snapshot-aware content-equality formula:
///
/// ```text
/// it@.len() == visited.len() + next@.len()
/// && forall<i: Int> 0 <= i && i < visited.len() ==>
///     *visited.index_logic(i) == it@.index_logic(i)
/// && forall<i: Int> 0 <= i && i < next@.len() ==>
///     next@.index_logic(i) == it@.index_logic(visited.len() + i)
/// ```
///
/// The `*visited[i]` (Deref) gives the pre-mutation snapshot of each element.
/// This is the key insight: `IterMut` yields `&mut T` references, so the
/// visited sequence contains mutable references. Dereferencing them gives the
/// value at the time the reference was created (the "current" value in
/// separation logic terms), which must match the original container content.
/// The successor's view (`next@`) tracks remaining elements directly.
fn rewrite_iter_mut_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let receiver_view = PureExpr::View(Arc::new(rewrite_expr(receiver)));
    let visited = rewrite_expr(&args[0]);
    let next_view = PureExpr::View(Arc::new(rewrite_expr(&args[1])));

    // Clause 1: length partition
    let len_clause = PureExpr::BinOp(
        Arc::new(seq_len(receiver_view.clone())),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(seq_len(visited.clone())),
            BinOp::Add,
            Arc::new(seq_len(next_view.clone())),
        )),
    );

    // Clause 2: visited snapshot content — *visited[i] == it@[i]
    let i_var = PureExpr::Var("__iter_mut_i".to_string(), Some(ExprSort::Int));
    let visited_len = seq_len(visited.clone());
    let visited_idx = seq_index(visited.clone(), i_var.clone());
    let recv_idx = seq_index(receiver_view.clone(), i_var.clone());
    let visited_clause = PureExpr::Forall {
        var: "__iter_mut_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(i_var.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(i_var.clone()),
                    BinOp::Lt,
                    Arc::new(visited_len.clone()),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Deref(Arc::new(visited_idx.clone()))),
                BinOp::Eq,
                Arc::new(recv_idx.clone()),
            )),
        )),
        triggers: vec![vec![visited_idx, recv_idx]],
    };

    // Clause 3: remainder content — next@[j] == it@[visited.len() + j]
    let j_var = PureExpr::Var("__iter_mut_j".to_string(), Some(ExprSort::Int));
    let next_len = seq_len(next_view.clone());
    let next_idx = seq_index(next_view, j_var.clone());
    let offset = PureExpr::BinOp(Arc::new(visited_len), BinOp::Add, Arc::new(j_var.clone()));
    let recv_offset_idx = seq_index(receiver_view, offset);
    let remainder_clause = PureExpr::Forall {
        var: "__iter_mut_j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(j_var.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(j_var),
                    BinOp::Lt,
                    Arc::new(next_len),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(next_idx.clone()),
                BinOp::Eq,
                Arc::new(recv_offset_idx.clone()),
            )),
        )),
        triggers: vec![vec![next_idx, recv_offset_idx]],
    };

    Some(PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(len_clause),
            BinOp::And,
            Arc::new(visited_clause),
        )),
        BinOp::And,
        Arc::new(remainder_clause),
    ))
}

fn rewrite_iter_mut_completed(receiver: &PureExpr) -> PureExpr {
    let receiver_view = PureExpr::View(Arc::new(rewrite_expr(receiver)));
    PureExpr::BinOp(
        Arc::new(seq_len(receiver_view)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )
}

// ---------------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------------

/// Try to rewrite a `produces` or `completed` method call on a supported
/// iterator type. Returns `None` if the call is not on a supported type.
pub(super) fn try_rewrite_iter_method(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
) -> Option<PureExpr> {
    // Vec::IntoIter
    if is_into_iter_receiver(receiver) {
        return match method {
            "produces" => rewrite_into_iter_produces(receiver, args),
            "produces_back" => rewrite_into_iter_produces_back(receiver, args),
            "completed" => Some(rewrite_into_iter_completed(receiver)),
            _ => None,
        };
    }

    // Trivial adapters (Empty, Once, Repeat) — identified by Datatype sort
    let dt_id = receiver_datatype_id(receiver)?;

    if sort_matches_any(dt_id, EMPTY_SORT_NAMES) {
        return match method {
            "produces" => rewrite_empty_produces(args),
            "completed" => Some(rewrite_empty_completed()),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, ONCE_SORT_NAMES) {
        return match method {
            "produces" => rewrite_once_produces(receiver, args),
            "completed" => Some(rewrite_once_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, REPEAT_SORT_NAMES) {
        return match method {
            "produces" => rewrite_repeat_produces(receiver, args),
            "completed" => Some(rewrite_repeat_completed()),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, FUSE_SORT_NAMES) {
        return match method {
            "produces" => rewrite_fuse_produces(receiver, args),
            "completed" => Some(rewrite_fuse_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, CLONED_SORT_NAMES) {
        return match method {
            "produces" => rewrite_cloned_produces(receiver, args),
            "completed" => Some(rewrite_delegated_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, COPIED_SORT_NAMES) {
        return match method {
            "produces" => rewrite_copied_produces(receiver, args),
            "completed" => Some(rewrite_delegated_completed(receiver)),
            _ => None,
        };
    }

    // Map<I, F> — completed delegates to inner iterator (#2170).
    // Produces is left to the abstract UF fallback because full closure
    // postcondition encoding is not yet available.
    if sort_matches_any(dt_id, MAP_SORT_NAMES) {
        return match method {
            "completed" => Some(rewrite_delegated_completed(receiver)),
            _ => None,
        };
    }

    // Filter<I, P> — completed delegates to inner iterator (#2170).
    if sort_matches_any(dt_id, FILTER_SORT_NAMES) {
        return match method {
            "completed" => Some(rewrite_delegated_completed(receiver)),
            _ => None,
        };
    }

    // FilterMap<I, F> — completed delegates to inner iterator (#2170).
    if sort_matches_any(dt_id, FILTER_MAP_SORT_NAMES) {
        return match method {
            "completed" => Some(rewrite_delegated_completed(receiver)),
            _ => None,
        };
    }

    // MapInv<I, F> — completed delegates to inner iterator (#2170).
    if sort_matches_any(dt_id, MAP_INV_SORT_NAMES) {
        return match method {
            "completed" => Some(rewrite_delegated_completed(receiver)),
            _ => None,
        };
    }

    // Logical SeqIter — same Seq concat formula as Vec::IntoIter
    if sort_matches_any(dt_id, SEQ_ITER_SORT_NAMES) {
        return match method {
            "produces" => rewrite_into_iter_produces(receiver, args),
            "completed" => Some(rewrite_into_iter_completed(receiver)),
            _ => None,
        };
    }

    // std::slice::Iter — intentionally fail-closed until the borrowed-element
    // / ref-seq design lands. Keep this family explicit so future patches
    // cannot silently widen the SeqIter lowering boundary. (#2116, #2172,
    // #694)
    if sort_matches_any(dt_id, SLICE_ITER_SORT_NAMES) {
        return None;
    }

    // std::slice::IterMut — snapshot-aware content-equality lowering (#2238).
    // Visited elements are `&mut T`; dereferencing gives the pre-mutation
    // snapshot value for comparison with the container's original view.
    if sort_matches_any(dt_id, SLICE_ITER_MUT_SORT_NAMES) {
        return match method {
            "produces" => rewrite_iter_mut_produces(receiver, args),
            "completed" => Some(rewrite_iter_mut_completed(receiver)),
            _ => None,
        };
    }

    None
}
