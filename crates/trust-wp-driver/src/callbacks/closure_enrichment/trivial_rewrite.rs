// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trivial closure precondition detection and rewriting.
//!
//! Closures without explicit `#[requires]` annotations have vacuous preconditions.
//! This module detects such closures and rewrites their precondition obligations
//! to `true`, eliminating unnecessary solver work.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::{Body, Local, Rvalue, StatementKind};
use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_arity, PureExpr};
use trust_wp_driver::StdSpec;

use super::{super::try_get_body_with_context, closure_receiver_base_name};
use crate::mir_analysis::get_mir_body;

/// Resolve the source-level name for a MIR local, if available.
///
/// Arguments are resolved from `arg_names` first, then local debug bindings.
fn source_name_for_local<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    arg_names: &[String],
) -> Option<String> {
    let idx = local.as_u32() as usize;
    if idx >= 1 && idx <= arg_names.len() {
        return Some(arg_names[idx - 1].clone());
    }

    for info in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value {
            if place.local == local && place.projection.is_empty() {
                return Some(info.name.to_string());
            }
        }
    }
    None
}

/// Collect local closure receiver names whose precondition is trivial.
///
/// A concrete closure with no explicit `#[requires]` is treated as having a
/// vacuous precondition at call sites.
pub(in crate::callbacks) fn collect_trivial_closure_receivers(
    parent_local_def_id: LocalDefId,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
) -> HashSet<String> {
    let mut receivers = HashSet::new();
    let Some(body_with_facts) = try_get_body_with_context(parent_local_def_id) else {
        return receivers;
    };
    let mir_body: &Body<'_> = get_mir_body(body_with_facts);

    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign(box (
                place,
                Rvalue::Aggregate(box rustc_middle::mir::AggregateKind::Closure(def_id, _), _),
            )) = &stmt.kind
            else {
                continue;
            };

            // Keep explicit closure requires as obligations.
            if user_specs
                .get(def_id)
                .is_some_and(|spec| !spec.requires.is_empty())
            {
                continue;
            }

            if let Some(name) = source_name_for_local(mir_body, place.local, arg_names) {
                receivers.insert(name);
            }
        }
    }

    receivers
}

fn receiver_is_tuple_closure_expr(expr: &PureExpr) -> bool {
    let inner = match expr {
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => inner.as_ref(),
        other => other,
    };
    matches!(
        inner,
        PureExpr::LogicFnCall { name, args }
            if tuple_logic_fn_arity(name) == Some(args.len())
    )
}

pub(in crate::callbacks) fn rewrite_trivial_closure_precondition_goal(
    goal: &mut PureExpr,
    trivial_receivers: &HashSet<String>,
) -> bool {
    rewrite_trivial_closure_preconditions(goal, trivial_receivers) > 0
}

fn rewrite_trivial_closure_preconditions(
    expr: &mut PureExpr,
    trivial_receivers: &HashSet<String>,
) -> usize {
    if let PureExpr::MethodCall {
        receiver, method, ..
    } = expr
    {
        let receiver_matches = closure_receiver_base_name(receiver)
            .is_some_and(|receiver_name| trivial_receivers.contains(receiver_name))
            || (!trivial_receivers.is_empty() && receiver_is_tuple_closure_expr(receiver));
        if method == "precondition" && receiver_matches {
            *expr = PureExpr::Bool(true);
            return 1;
        }
    }

    match expr {
        PureExpr::BinOp(left, _, right) => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(left), trivial_receivers)
                + rewrite_trivial_closure_preconditions(Arc::make_mut(right), trivial_receivers)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(inner), trivial_receivers)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(cond), trivial_receivers)
                + rewrite_trivial_closure_preconditions(Arc::make_mut(then_expr), trivial_receivers)
                + rewrite_trivial_closure_preconditions(Arc::make_mut(else_expr), trivial_receivers)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            let mut rewritten =
                rewrite_trivial_closure_preconditions(Arc::make_mut(receiver), trivial_receivers);
            for arg in args {
                rewritten += rewrite_trivial_closure_preconditions(arg, trivial_receivers);
            }
            rewritten
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter_mut()
            .map(|arg| rewrite_trivial_closure_preconditions(arg, trivial_receivers))
            .sum(),
        PureExpr::LetAssume { assumption, body } => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(assumption), trivial_receivers)
                + rewrite_trivial_closure_preconditions(Arc::make_mut(body), trivial_receivers)
        }
        PureExpr::LetObligation { obligation, body } => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(obligation), trivial_receivers)
                + rewrite_trivial_closure_preconditions(Arc::make_mut(body), trivial_receivers)
        }
        PureExpr::Let { value, body, .. } => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(value), trivial_receivers)
                + rewrite_trivial_closure_preconditions(Arc::make_mut(body), trivial_receivers)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            let mut rewritten =
                rewrite_trivial_closure_preconditions(Arc::make_mut(body), trivial_receivers);
            for trigger_set in triggers {
                for trigger in trigger_set {
                    rewritten += rewrite_trivial_closure_preconditions(trigger, trivial_receivers);
                }
            }
            rewritten
        }
        PureExpr::Match { scrutinee, arms } => {
            let mut rewritten =
                rewrite_trivial_closure_preconditions(Arc::make_mut(scrutinee), trivial_receivers);
            for arm in arms {
                rewritten +=
                    rewrite_trivial_closure_preconditions(&mut arm.body, trivial_receivers);
            }
            rewritten
        }
        PureExpr::Closure { body, .. } => {
            rewrite_trivial_closure_preconditions(Arc::make_mut(body), trivial_receivers)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(..) => 0,
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => 0,
    }
}
