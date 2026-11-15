// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Point facts about a written `&mut` array or slice parameter, read off the
//! final value the mut-borrow lane computed for it.
//!
//! When the MIR body contains `(*param)[idx] = val`, the mut-borrow extractor
//! advances the parameter's pointee to `(*param)@.set(idx, val)` and merges
//! the arms of a branch as `Ite(cond, then, else)`. That value is the one the
//! lane hands the solver as `^param`. For each path of it (the conjunction of
//! the `Ite` conditions leading to a leaf) whose leaf is a `set` chain over the
//! entry value, this states what the chain denotes on that path:
//!   1. each write `(^param)@[idx_k] == val_k`, unless a later write on the
//!      same path may hit the same index (`idx_k != idx_m` for every later
//!      `m` is part of the antecedent);
//!   2. `(^param)@.len() == (*param)@.len()`;
//!   3. `forall i, i != idx_0 && .. ==> (^param)@[i] == (*param)@[i]`.
//!
//! Every fact is a consequence of `^param == <final value>`, the claim the
//! lane already makes, and holds only where the path's conditions do: a write
//! on one arm says nothing about the final value of an execution that takes
//! the other (indexed_write_on_one_arm_final_value_*.rs). A parameter the lane
//! could not track exactly (mutation-continued, lent, a nested transfer slot)
//! has no final value to read, and gets no fact.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use tracing::debug;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

use super::super::mir_analysis::MutBorrowBody;

/// The deepest `Ite` nesting whose paths are enumerated; a deeper final value
/// gets no fact on the paths below it.
const MAX_PATH_DEPTH: usize = 8;

/// `forall i, 0 <= i < len(current) && i != idx_0 && .. && guards ==>
/// final[i] == current[i]`. The path guards sit inside the binder, where ay
/// instantiates the quantifier; `__iw_i` is free in none of them.
pub(super) fn build_combined_indexed_write_frame(
    current_view: &PureExpr,
    final_view: &PureExpr,
    excluded_indices: &[PureExpr],
    guards: &[PureExpr],
) -> PureExpr {
    let qvar = PureExpr::Var("__iw_i".to_string(), Some(ExprSort::Int));
    let mut antecedent = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Le,
            Arc::new(qvar.clone()),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(qvar.clone()),
            BinOp::Lt,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(current_view.clone()),
                method: "len".to_string(),
                args: vec![],
            }),
        )),
    );
    for excluded_idx in excluded_indices {
        antecedent = PureExpr::BinOp(
            Arc::new(antecedent),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(qvar.clone()),
                BinOp::Ne,
                Arc::new(excluded_idx.clone()),
            )),
        );
    }
    for guard in guards {
        antecedent = PureExpr::BinOp(Arc::new(antecedent), BinOp::And, Arc::new(guard.clone()));
    }
    PureExpr::Forall {
        var: "__iw_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(antecedent),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(final_view.clone()),
                    method: "index_logic".to_string(),
                    args: vec![qvar.clone()],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(current_view.clone()),
                    method: "index_logic".to_string(),
                    args: vec![qvar],
                }),
            )),
        )),
        triggers: vec![],
    }
}

/// `g_1 && .. && g_n ==> fact`, or `fact` on the unconditional path.
fn under_guards(guards: &[PureExpr], fact: PureExpr) -> PureExpr {
    match guards
        .iter()
        .cloned()
        .reduce(|acc, guard| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(guard)))
    {
        Some(antecedent) => PureExpr::BinOp(Arc::new(antecedent), BinOp::Implies, Arc::new(fact)),
        None => fact,
    }
}

fn strip_views(mut expr: &PureExpr) -> &PureExpr {
    while let PureExpr::View(inner) = expr {
        expr = inner;
    }
    expr
}

struct ParamViews<'a> {
    name: &'a str,
    final_view: PureExpr,
    current_view: PureExpr,
}

/// The facts one leaf of the final value's `Ite` tree denotes under `guards`.
/// A leaf that is not a `set` chain over the parameter's entry pointee
/// (`*param`) states only the writes of its chain, and a leaf that is not a
/// chain at all states nothing.
fn leaf_facts(
    leaf: &PureExpr,
    guards: &[PureExpr],
    param: &ParamViews<'_>,
    out: &mut Vec<PureExpr>,
) {
    // Outermost first: `writes[0]` is the LAST write on this path.
    let mut writes: Vec<(&PureExpr, &PureExpr)> = Vec::new();
    let mut current = strip_views(leaf);
    while let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = current
    {
        if method != "set" || args.len() != 2 {
            break;
        }
        writes.push((&args[0], &args[1]));
        current = strip_views(receiver);
    }
    let base_is_entry = matches!(
        current,
        PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == param.name)
    );
    if writes.is_empty() && !base_is_entry {
        return;
    }
    for (position, (index, value)) in writes.iter().enumerate() {
        let mut antecedent: Vec<PureExpr> = guards.to_vec();
        for (later_index, _) in &writes[..position] {
            antecedent.push(PureExpr::BinOp(
                Arc::new((*index).clone()),
                BinOp::Ne,
                Arc::new((*later_index).clone()),
            ));
        }
        let point_write = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(param.final_view.clone()),
                method: "index_logic".to_string(),
                args: vec![(*index).clone()],
            }),
            BinOp::Eq,
            Arc::new((*value).clone()),
        );
        out.push(under_guards(&antecedent, point_write));
    }
    if !base_is_entry {
        return;
    }
    let len_preservation = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(param.final_view.clone()),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(param.current_view.clone()),
            method: "len".to_string(),
            args: vec![],
        }),
    );
    out.push(under_guards(guards, len_preservation));
    let excluded: Vec<PureExpr> = writes.iter().map(|(index, _)| (*index).clone()).collect();
    out.push(build_combined_indexed_write_frame(
        &param.current_view,
        &param.final_view,
        &excluded,
        guards,
    ));
}

/// Walk the final value's `Ite` tree, collecting each path's conditions. A
/// path deeper than `MAX_PATH_DEPTH` states nothing.
fn path_facts(
    tree: &PureExpr,
    guards: &mut Vec<PureExpr>,
    param: &ParamViews<'_>,
    out: &mut Vec<PureExpr>,
) {
    match strip_views(tree) {
        PureExpr::Ite(condition, then_branch, else_branch) => {
            if guards.len() >= MAX_PATH_DEPTH {
                return;
            }
            guards.push(condition.as_ref().clone());
            path_facts(then_branch, guards, param, out);
            guards.pop();
            guards.push(PureExpr::UnOp(UnOp::Not, Arc::clone(condition)));
            path_facts(else_branch, guards, param, out);
            guards.pop();
        }
        leaf => leaf_facts(leaf, guards, param, out),
    }
}

/// Premises about the final value of every `&mut` parameter the body writes
/// by index, read off `mut_borrow.final_values` path by path.
///
/// Each fact is owed by the binding `^param == final_values[param]` the solver
/// dispatch states, so a parameter whose bound value is not that one states
/// nothing: `overridden` names the final values the dispatch replaces
/// (`synthesized_final_values`), and a mutation-continued parameter is not
/// bound to it at all.
pub(super) fn indexed_write_final_value_facts(
    mut_borrow: &MutBorrowBody,
    overridden: Option<&HashMap<String, PureExpr>>,
    verbose: bool,
) -> Vec<PureExpr> {
    let mut out = Vec::new();
    let mut seen: HashSet<&str> = HashSet::new();
    for write in &mut_borrow.indexed_writes {
        let name = write.param_name.as_str();
        if !seen.insert(name)
            || mut_borrow.mutation_continued_params.contains(name)
            || mut_borrow.nested_transfer_params.contains(name)
            || overridden.is_some_and(|values| values.contains_key(name))
        {
            continue;
        }
        let Some(final_value) = mut_borrow.final_values.get(name) else {
            continue;
        };
        let param_var = PureExpr::Var(
            name.to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Seq))),
        );
        let param = ParamViews {
            name,
            final_view: PureExpr::View(Arc::new(PureExpr::Final(Arc::new(param_var.clone())))),
            current_view: PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(param_var)))),
        };
        let before = out.len();
        path_facts(final_value, &mut Vec::new(), &param, &mut out);
        if verbose {
            debug!(
                "trust-wp:   ({} final-value fact(s) for indexed writes to {name})",
                out.len() - before
            );
        }
    }
    out
}
