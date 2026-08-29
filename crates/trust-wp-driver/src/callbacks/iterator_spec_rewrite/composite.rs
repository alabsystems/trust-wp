// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Composite iterator adapter rewrites.
//!
//! This module is the landing zone for the heavier adapter family that should
//! not keep extending `simple.rs`. It now covers `Rev`, `Skip`, `Take`,
//! `Enumerate`, `Zip`, `Chain`, and `Peekable`, with later slices extending
//! the same rewrite boundary. (#2170, #2637, #2688)

use std::sync::Arc;

use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_name, BinOp, ExprSort, PureExpr,
};

use super::{
    helpers::{
        receiver_datatype_id, sort_matches_any, CHAIN_SORT_NAMES, ENUMERATE_SORT_NAMES,
        PEEKABLE_SORT_NAMES, REV_SORT_NAMES, SKIP_SORT_NAMES, TAKE_SORT_NAMES, ZIP_SORT_NAMES,
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

fn iter(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "iter")
}

fn deref(receiver: PureExpr) -> PureExpr {
    PureExpr::Deref(Arc::new(receiver))
}

fn iter_mut(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "iter_mut")
}

fn n(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "n")
}

fn completed(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "completed")
}

fn itera(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "itera")
}

fn iterb(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "iterb")
}

/// Chain<A, B> accessor for the first iterator.
///
/// Chain uses `a()`/`b()` accessors per the trust-wp-std `ChainExt` trait,
/// unlike Zip which uses `itera()`/`iterb()`. This distinction matters because
/// the encoder-level completed delegation also uses `a`/`b` for Chain (see
/// `completed_delegation.rs`), and the UF declarations must match.
fn chain_a(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "a")
}

/// Chain<A, B> accessor for the second iterator.
fn chain_b(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "b")
}

fn seq_len(seq: PureExpr) -> PureExpr {
    zero_arg_method(seq, "len")
}

fn seq_index(seq: PureExpr, index: PureExpr) -> PureExpr {
    method_call(seq, "index_logic", vec![index])
}

fn seq_concat(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    method_call(lhs, "concat", vec![rhs])
}

fn resolve(receiver: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: "resolve".to_string(),
        args: vec![receiver],
    }
}

fn inv(receiver: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![receiver],
    }
}

fn final_value(receiver: PureExpr) -> PureExpr {
    PureExpr::Final(Arc::new(receiver))
}

fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
}

fn or(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs))
}

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn gt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Gt, Arc::new(rhs))
}

fn add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs))
}

fn sub(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Sub, Arc::new(rhs))
}

fn lt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Lt, Arc::new(rhs))
}

fn le(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs))
}

fn implies(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
}

fn tuple2(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![lhs, rhs],
    }
}

fn rewrite_rev_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);
    Some(method_call(
        iter(recv),
        "produces_back",
        vec![visited, iter(next)],
    ))
}

fn rewrite_rev_completed(receiver: &PureExpr) -> PureExpr {
    completed(iter(rewrite_expr(receiver)))
}

fn rewrite_skip_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }

    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);
    let skipped = PureExpr::Var("__skip_prefix".to_string(), Some(ExprSort::Seq));
    let i_var = PureExpr::Var("__skip_i".to_string(), Some(ExprSort::Int));
    let skipped_len = seq_len(skipped.clone());
    let skipped_idx = seq_index(skipped.clone(), i_var.clone());

    let empty_branch = and(
        eq(seq_len(visited.clone()), PureExpr::Int(0)),
        eq(recv.clone(), next.clone()),
    );
    let progress_branch = and(
        eq(n(next.clone()), PureExpr::Int(0)),
        and(
            gt(seq_len(visited.clone()), PureExpr::Int(0)),
            PureExpr::Exists {
                var: "__skip_prefix".to_string(),
                var_sort: Some(ExprSort::Seq),
                body: Arc::new(and(
                    eq(skipped_len.clone(), n(recv.clone())),
                    and(
                        method_call(
                            iter(recv),
                            "produces",
                            vec![seq_concat(skipped.clone(), visited), iter(next)],
                        ),
                        PureExpr::Forall {
                            var: "__skip_i".to_string(),
                            var_sort: Some(ExprSort::Int),
                            body: Arc::new(implies(
                                and(
                                    le(PureExpr::Int(0), i_var.clone()),
                                    lt(i_var.clone(), skipped_len),
                                ),
                                resolve(skipped_idx.clone()),
                            )),
                            triggers: vec![vec![skipped_idx]],
                        },
                    ),
                )),
                triggers: vec![],
            },
        ),
    );

    Some(or(empty_branch, progress_branch))
}

fn rewrite_take_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }

    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);

    let counter_relation = eq(
        n(recv.clone()),
        add(n(next.clone()), seq_len(visited.clone())),
    );
    let inner_relation = method_call(iter(recv), "produces", vec![visited, iter(next)]);

    Some(and(counter_relation, inner_relation))
}

fn rewrite_enumerate_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }

    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);
    let inner_steps = PureExpr::Var("__enumerate_steps".to_string(), Some(ExprSort::Seq));
    let i_var = PureExpr::Var("__enumerate_i".to_string(), Some(ExprSort::Int));
    let visited_len = seq_len(visited.clone());
    let steps_len = seq_len(inner_steps.clone());
    let visited_idx = seq_index(visited.clone(), i_var.clone());
    let steps_idx = seq_index(inner_steps.clone(), i_var.clone());

    let counter_relation = eq(visited_len.clone(), sub(n(next.clone()), n(recv.clone())));
    let inner_relation = method_call(
        iter(recv.clone()),
        "produces",
        vec![inner_steps.clone(), iter(next)],
    );
    let len_relation = eq(visited_len.clone(), steps_len.clone());
    let element_relation = PureExpr::Forall {
        var: "__enumerate_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(
                le(PureExpr::Int(0), i_var.clone()),
                lt(i_var.clone(), steps_len),
            ),
            eq(
                visited_idx.clone(),
                tuple2(add(n(recv), i_var.clone()), steps_idx.clone()),
            ),
        )),
        triggers: vec![vec![visited_idx, steps_idx]],
    };

    Some(and(
        counter_relation,
        PureExpr::Exists {
            var: "__enumerate_steps".to_string(),
            var_sort: Some(ExprSort::Seq),
            body: Arc::new(and(inner_relation, and(len_relation, element_relation))),
            triggers: vec![],
        },
    ))
}

fn rewrite_take_completed(receiver: &PureExpr) -> PureExpr {
    let recv = rewrite_expr(receiver);

    let zero_branch = and(eq(n(recv.clone()), PureExpr::Int(0)), resolve(recv.clone()));
    let step_branch = and(
        gt(n(recv.clone()), PureExpr::Int(0)),
        and(
            eq(
                n(recv.clone()),
                add(n(final_value(recv.clone())), PureExpr::Int(1)),
            ),
            completed(iter_mut(recv)),
        ),
    );

    or(zero_branch, step_branch)
}

fn rewrite_skip_completed(receiver: &PureExpr) -> PureExpr {
    let recv = rewrite_expr(receiver);
    let recv_final = final_value(recv.clone());
    let skipped = PureExpr::Var("__skip_prefix".to_string(), Some(ExprSort::Seq));
    let done_iter = PureExpr::Var("__skip_done".to_string(), None);
    let i_var = PureExpr::Var("__skip_i".to_string(), Some(ExprSort::Int));
    let skipped_len = seq_len(skipped.clone());
    let skipped_idx = seq_index(skipped.clone(), i_var.clone());

    and(
        eq(n(recv_final.clone()), PureExpr::Int(0)),
        PureExpr::Exists {
            var: "__skip_prefix".to_string(),
            var_sort: Some(ExprSort::Seq),
            body: Arc::new(PureExpr::Exists {
                var: "__skip_done".to_string(),
                var_sort: None,
                body: Arc::new(and(
                    le(skipped_len.clone(), n(recv.clone())),
                    and(
                        method_call(
                            iter(recv.clone()),
                            "produces",
                            vec![skipped, deref(done_iter.clone())],
                        ),
                        and(
                            PureExpr::Forall {
                                var: "__skip_i".to_string(),
                                var_sort: Some(ExprSort::Int),
                                body: Arc::new(implies(
                                    and(
                                        le(PureExpr::Int(0), i_var.clone()),
                                        lt(i_var.clone(), skipped_len),
                                    ),
                                    resolve(skipped_idx.clone()),
                                )),
                                triggers: vec![vec![skipped_idx]],
                            },
                            and(
                                completed(done_iter.clone()),
                                eq(final_value(done_iter), iter(recv_final)),
                            ),
                        ),
                    ),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        },
    )
}

fn rewrite_enumerate_completed(receiver: &PureExpr) -> PureExpr {
    let recv = rewrite_expr(receiver);
    let recv_final = final_value(recv.clone());

    and(
        completed(iter(recv.clone())),
        and(
            eq(iter(recv.clone()), iter(recv_final.clone())),
            eq(n(recv), n(recv_final)),
        ),
    )
}

fn rewrite_zip_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }

    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);
    let left_steps = PureExpr::Var("__zip_left_steps".to_string(), Some(ExprSort::Seq));
    let right_steps = PureExpr::Var("__zip_right_steps".to_string(), Some(ExprSort::Seq));
    let i_var = PureExpr::Var("__zip_i".to_string(), Some(ExprSort::Int));
    let visited_len = seq_len(visited.clone());
    let left_len = seq_len(left_steps.clone());
    let right_len = seq_len(right_steps.clone());
    let visited_idx = seq_index(visited.clone(), i_var.clone());
    let left_idx = seq_index(left_steps.clone(), i_var.clone());
    let right_idx = seq_index(right_steps.clone(), i_var.clone());

    let body = and(
        eq(left_len.clone(), right_len.clone()),
        and(
            eq(right_len.clone(), visited_len.clone()),
            and(
                method_call(
                    itera(recv.clone()),
                    "produces",
                    vec![left_steps.clone(), itera(next.clone())],
                ),
                and(
                    method_call(
                        iterb(recv),
                        "produces",
                        vec![right_steps.clone(), iterb(next)],
                    ),
                    PureExpr::Forall {
                        var: "__zip_i".to_string(),
                        var_sort: Some(ExprSort::Int),
                        body: Arc::new(implies(
                            and(
                                le(PureExpr::Int(0), i_var.clone()),
                                lt(i_var.clone(), visited_len),
                            ),
                            eq(
                                visited_idx.clone(),
                                tuple2(left_idx.clone(), right_idx.clone()),
                            ),
                        )),
                        triggers: vec![vec![visited_idx, left_idx, right_idx]],
                    },
                ),
            ),
        ),
    );

    Some(PureExpr::Exists {
        var: "__zip_left_steps".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Exists {
            var: "__zip_right_steps".to_string(),
            var_sort: Some(ExprSort::Seq),
            body: Arc::new(body),
            triggers: vec![],
        }),
        triggers: vec![],
    })
}

fn rewrite_zip_completed(receiver: &PureExpr) -> PureExpr {
    let recv = rewrite_expr(receiver);
    let recv_final = final_value(recv.clone());
    let left_step = PureExpr::Var("__zip_left_step".to_string(), Some(ExprSort::Seq));
    let stepped_elem = seq_index(left_step.clone(), PureExpr::Int(0));

    let left_completed = and(
        completed(itera(recv.clone())),
        and(
            eq(itera(recv.clone()), itera(recv_final.clone())),
            eq(iterb(recv.clone()), iterb(recv_final.clone())),
        ),
    );
    let right_completed = and(
        completed(iterb(recv.clone())),
        and(
            eq(iterb(recv.clone()), iterb(recv_final.clone())),
            PureExpr::Exists {
                var: "__zip_left_step".to_string(),
                var_sort: Some(ExprSort::Seq),
                body: Arc::new(and(
                    eq(seq_len(left_step.clone()), PureExpr::Int(1)),
                    and(
                        method_call(
                            itera(recv.clone()),
                            "produces",
                            vec![left_step.clone(), itera(recv_final)],
                        ),
                        and(inv(stepped_elem.clone()), resolve(stepped_elem)),
                    ),
                )),
                triggers: vec![],
            },
        ),
    );

    or(left_completed, right_completed)
}

// ---------------------------------------------------------------------------
// Chain<A, B> — dual-source sequential concatenation (#2688)
// ---------------------------------------------------------------------------

/// Rewrites `chain.produces(visited, next)` to:
///
/// ```text
/// exists __chain_left: Seq, __chain_right: Seq.
///   chain.a().produces(__chain_left, next.a())
///   && chain.b().produces(__chain_right, next.b())
///   && visited.len() == __chain_left.len() + __chain_right.len()
///   && forall i. 0 <= i && i < __chain_left.len() ==>
///       visited[i] == __chain_left[i]
///   && forall j. 0 <= j && j < __chain_right.len() ==>
///       visited[__chain_left.len() + j] == __chain_right[j]
/// ```
///
/// Chain yields all elements from the first iterator, then all from the second.
/// The visited sequence is the concatenation of elements from both sources,
/// with the left source's elements preceding the right source's.
///
/// Note: Chain uses `a()` and `b()` accessors (not `itera()`/`iterb()`), matching
/// the trust-wp-std `ChainExt` trait spec at `crates/trust-wp-std/src/std/iter/chain.rs`.
fn rewrite_chain_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }

    let recv = rewrite_expr(receiver);
    let visited = rewrite_expr(&args[0]);
    let next = rewrite_expr(&args[1]);

    let left_steps = PureExpr::Var("__chain_left".to_string(), Some(ExprSort::Seq));
    let right_steps = PureExpr::Var("__chain_right".to_string(), Some(ExprSort::Seq));

    let visited_len = seq_len(visited.clone());
    let left_len = seq_len(left_steps.clone());
    let right_len = seq_len(right_steps.clone());

    // left produces delegation — Chain uses a()/b() accessors per trust-wp-std ChainExt
    let left_produces = method_call(
        chain_a(recv.clone()),
        "produces",
        vec![left_steps.clone(), chain_a(next.clone())],
    );
    // right produces delegation
    let right_produces = method_call(
        chain_b(recv),
        "produces",
        vec![right_steps.clone(), chain_b(next)],
    );

    // visited.len() == left.len() + right.len()
    let len_constraint = eq(visited_len, add(left_len.clone(), right_len.clone()));

    // forall i. 0 <= i < left.len() ==> visited[i] == left[i]
    let i_var = PureExpr::Var("__chain_i".to_string(), Some(ExprSort::Int));
    let visited_idx_i = seq_index(visited.clone(), i_var.clone());
    let left_idx_i = seq_index(left_steps.clone(), i_var.clone());
    let left_content = PureExpr::Forall {
        var: "__chain_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(
                le(PureExpr::Int(0), i_var.clone()),
                lt(i_var, left_len.clone()),
            ),
            eq(visited_idx_i.clone(), left_idx_i.clone()),
        )),
        triggers: vec![vec![visited_idx_i, left_idx_i]],
    };

    // forall j. 0 <= j < right.len() ==> visited[left.len() + j] == right[j]
    let j_var = PureExpr::Var("__chain_j".to_string(), Some(ExprSort::Int));
    let offset = add(left_len, j_var.clone());
    let visited_idx_j = seq_index(visited, offset);
    let right_idx_j = seq_index(right_steps.clone(), j_var.clone());
    let right_content = PureExpr::Forall {
        var: "__chain_j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            and(le(PureExpr::Int(0), j_var.clone()), lt(j_var, right_len)),
            eq(visited_idx_j.clone(), right_idx_j.clone()),
        )),
        triggers: vec![vec![visited_idx_j, right_idx_j]],
    };

    let body = and(
        left_produces,
        and(
            right_produces,
            and(len_constraint, and(left_content, right_content)),
        ),
    );

    Some(PureExpr::Exists {
        var: "__chain_left".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Exists {
            var: "__chain_right".to_string(),
            var_sort: Some(ExprSort::Seq),
            body: Arc::new(body),
            triggers: vec![],
        }),
        triggers: vec![],
    })
}

/// Rewrites `chain.completed()` to:
///
/// ```text
/// chain.a().completed() && chain.b().completed()
/// ```
///
/// Both inner iterators must be exhausted for the chain to be completed.
/// Uses `a()`/`b()` accessors per trust-wp-std `ChainExt` trait spec.
fn rewrite_chain_completed(receiver: &PureExpr) -> PureExpr {
    let recv = rewrite_expr(receiver);
    and(completed(chain_a(recv.clone())), completed(chain_b(recv)))
}

// ---------------------------------------------------------------------------
// Peekable<I> — look-ahead wrapper (#2688)
// ---------------------------------------------------------------------------

/// Rewrites `peek.produces(visited, next)` to delegation to inner iterator:
///
/// ```text
/// peek.iter().produces(visited, next.iter())
/// ```
///
/// Peekable wraps an inner iterator and provides `peek()` without consuming.
/// The produces relation delegates directly to the inner iterator since peeking
/// does not affect the sequence of yielded elements — it only buffers one
/// element ahead in the adapter state.
fn rewrite_peekable_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let visited = rewrite_expr(&args[0]);
    let next_iter = iter(rewrite_expr(&args[1]));
    Some(method_call(
        iter(rewrite_expr(receiver)),
        "produces",
        vec![visited, next_iter],
    ))
}

/// Rewrites `peek.completed()` to `peek.iter().completed()`.
fn rewrite_peekable_completed(receiver: &PureExpr) -> PureExpr {
    completed(iter(rewrite_expr(receiver)))
}

/// Try to rewrite a `produces` or `completed` method call on a composite
/// iterator adapter receiver.
pub(super) fn try_rewrite_composite_iter_method(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
) -> Option<PureExpr> {
    let dt_id = receiver_datatype_id(receiver)?;

    if sort_matches_any(dt_id, REV_SORT_NAMES) {
        return match method {
            "produces" => rewrite_rev_produces(receiver, args),
            "completed" => Some(rewrite_rev_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, SKIP_SORT_NAMES) {
        return match method {
            "produces" => rewrite_skip_produces(receiver, args),
            "completed" => Some(rewrite_skip_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, TAKE_SORT_NAMES) {
        return match method {
            "produces" => rewrite_take_produces(receiver, args),
            "completed" => Some(rewrite_take_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, ENUMERATE_SORT_NAMES) {
        return match method {
            "produces" => rewrite_enumerate_produces(receiver, args),
            "completed" => Some(rewrite_enumerate_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, ZIP_SORT_NAMES) {
        return match method {
            "produces" => rewrite_zip_produces(receiver, args),
            "completed" => Some(rewrite_zip_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, CHAIN_SORT_NAMES) {
        return match method {
            "produces" => rewrite_chain_produces(receiver, args),
            "completed" => Some(rewrite_chain_completed(receiver)),
            _ => None,
        };
    }

    if sort_matches_any(dt_id, PEEKABLE_SORT_NAMES) {
        return match method {
            "produces" => rewrite_peekable_produces(receiver, args),
            "completed" => Some(rewrite_peekable_completed(receiver)),
            _ => None,
        };
    }

    None
}
