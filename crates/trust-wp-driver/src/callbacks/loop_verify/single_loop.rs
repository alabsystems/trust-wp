// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-loop verification engine for loop invariant checking.

use std::sync::Arc;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TyKind};
use tracing::{debug, trace};
use trust_wp_ay::{
    verify_loop_invariant_outcome, BodyEffects, EncodingError, LoopVerificationContext,
};
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, ExprSort, Pattern, PureExpr,
        UnOp,
    },
    logic::LogicFnDef,
};

use super::{
    encoder_config::encoder_config_from_req,
    expr_utils::expr_referenced_vars,
    for_loop_facts::{
        build_for_loop_completion_facts, build_for_loop_init_facts,
        build_for_loop_structural_invariant, is_for_loop_element_nonnegative_invariant,
    },
    ghost_rewrite::{
        filter_post_loop_borrow_resolution_vars, filter_post_loop_stale_deref_assumptions,
        rewrite_loop_ensures_for_ghost_return,
    },
    inference::{
        infer_iterator_produced_len_bound, infer_parameter_frame_invariants,
        infer_stable_loop_invariants, infer_stable_type_invariant_clauses,
    },
    old_rewrite::rewrite_loop_postcondition_old,
    pre_loop_store::PreLoopStoreLinks,
    reporting::{emit_loop_verification_diagnostics, loop_verification_evidence_gap_reasons},
    span_matching::{find_loop_invariants, select_loop_variant},
    transition_facts::{
        build_fmap_identity_bridge_facts, build_transition_facts_for_loop_state,
        build_tuple_position_map, include_structural_invariant_in_loop_vc,
        single_insert_into_empty_fmap,
    },
    types::{LoopWithInvariantRequest, PerLoopConditions, PreExtractedLoopBody, SingleLoopResult},
};
use crate::{
    callbacks::helpers::extract_final_vars,
    mir_analysis::{resolve_pre_loop_calls, ChangedPlaces, ChangedPlacesTree, LoopAnalysis},
};

fn annotate_seq_loop_var(expr: &PureExpr, var_name: &str) -> PureExpr {
    let mut substitutions = std::collections::HashMap::new();
    substitutions.insert(
        var_name.to_string(),
        PureExpr::Var(var_name.to_string(), Some(ExprSort::Seq)),
    );
    expr.substitute(&substitutions)
}

fn zero() -> PureExpr {
    PureExpr::Int(0)
}

fn var_with_sort(name: &str, sort: Option<ExprSort>) -> PureExpr {
    PureExpr::Var(name.to_string(), sort)
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn len_expr(receiver: PureExpr) -> PureExpr {
    method_call(receiver, "len", vec![])
}

fn view_expr(expr: PureExpr) -> PureExpr {
    PureExpr::View(Arc::new(expr))
}

fn final_expr(expr: PureExpr) -> PureExpr {
    PureExpr::Final(Arc::new(expr))
}

fn loop_is_nested(loop_analysis: &LoopAnalysis, loop_idx: usize) -> bool {
    let header = loop_analysis.loops[loop_idx].header;
    loop_analysis
        .loops
        .iter()
        .enumerate()
        .any(|(other_idx, other_loop)| {
            other_idx != loop_idx && other_loop.body_blocks.contains(&header)
        })
}

fn first_outermost_loop_index(loop_analysis: &LoopAnalysis) -> Option<usize> {
    loop_analysis
        .loops
        .iter()
        .enumerate()
        .filter(|(idx, _)| !loop_is_nested(loop_analysis, *idx))
        .min_by_key(|(_, loop_info)| loop_info.header.as_u32())
        .map(|(idx, _)| idx)
}

fn append_first_outermost_pre_loop_call_assumptions(
    init_facts: &mut Vec<PureExpr>,
    loop_analysis: &LoopAnalysis,
    loop_idx: usize,
    pre_loop_call_assumptions: &[PureExpr],
) -> usize {
    if pre_loop_call_assumptions.is_empty()
        || first_outermost_loop_index(loop_analysis) != Some(loop_idx)
    {
        return 0;
    }

    let mut added = 0usize;
    for fact in pre_loop_call_assumptions {
        if !init_facts.contains(fact) {
            init_facts.push(fact.clone());
            added += 1;
        }
    }
    added
}

fn and_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
}

fn implies_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
}

fn eq_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn le_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs))
}

fn lt_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Lt, Arc::new(rhs))
}

fn is_var_named(expr: &PureExpr, name: &str) -> bool {
    matches!(expr, PureExpr::Var(var, _) if var == name)
}

fn is_identity_deref_final_value(param: &str, expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Deref(inner) if is_var_named(inner.as_ref(), param)
    )
}

fn find_final_param_var(ensures: &[PureExpr], param: &str) -> Option<PureExpr> {
    let mut found = None;
    for ensure in ensures {
        ensure.for_each_recursive(|expr| {
            if found.is_some() {
                return;
            }
            if let PureExpr::Final(inner) = expr {
                if let PureExpr::Var(name, sort) = inner.as_ref() {
                    if name == param {
                        found = Some(PureExpr::Var(name.clone(), sort.clone()));
                    }
                }
            }
        });
        if found.is_some() {
            break;
        }
    }
    found
}

fn expr_contains_final_param(expr: &PureExpr, param: &str) -> bool {
    expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::Final(inner) if is_var_named(inner.as_ref(), param)
        )
    })
}

fn find_final_index_receiver(
    ensures: &[PureExpr],
    param: &str,
    index_method: &str,
) -> Option<PureExpr> {
    let mut found = None;
    for ensure in ensures {
        ensure.for_each_recursive(|expr| {
            if found.is_some() {
                return;
            }
            if let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = expr
            {
                if method == index_method
                    && args.len() == 1
                    && expr_contains_final_param(receiver, param)
                {
                    found = Some(receiver.as_ref().clone());
                }
            }
        });
        if found.is_some() {
            break;
        }
    }
    found
}

fn is_current_param_receiver(expr: &PureExpr, param: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == param,
        PureExpr::Deref(inner) | PureExpr::View(inner) => {
            is_current_param_receiver(inner.as_ref(), param)
        }
        _ => false,
    }
}

fn is_produced_len(expr: &PureExpr, produced_name: &str) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == produced_name)
    )
}

fn has_nonnegative_bound(expr: &PureExpr, var: &str) -> bool {
    expr.any_recursive(|node| match node {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && is_var_named(rhs.as_ref(), var)
        }
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            is_var_named(lhs.as_ref(), var) && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        _ => false,
    })
}

fn has_produced_len_bound(expr: &PureExpr, var: &str, produced_name: &str) -> bool {
    expr.any_recursive(|node| match node {
        PureExpr::BinOp(lhs, BinOp::Lt, rhs) => {
            is_var_named(lhs.as_ref(), var) && is_produced_len(rhs.as_ref(), produced_name)
        }
        PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
            is_produced_len(lhs.as_ref(), produced_name) && is_var_named(rhs.as_ref(), var)
        }
        _ => false,
    })
}

fn current_index_equality(expr: &PureExpr, var: &str, param: &str) -> Option<(String, PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };

    if let Some(method) = current_index_method(lhs, var, param) {
        return Some((method, rhs.as_ref().clone()));
    }
    current_index_method(rhs, var, param).map(|method| (method, lhs.as_ref().clone()))
}

fn current_index_method(expr: &PureExpr, var: &str, param: &str) -> Option<String> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if !matches!(method.as_str(), "index" | "index_logic") || args.len() != 1 {
        return None;
    }
    if !is_var_named(&args[0], var) || !is_current_param_receiver(receiver, param) {
        return None;
    }
    Some(method.clone())
}

fn prefix_transfer_fact_from_invariant(
    invariant: &PureExpr,
    produced_name: &str,
    param: &str,
    final_param_var: &PureExpr,
    ensures: &[PureExpr],
) -> Option<PureExpr> {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = invariant
    else {
        return None;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
        return None;
    };
    if !has_nonnegative_bound(antecedent, var)
        || !has_produced_len_bound(antecedent, var, produced_name)
    {
        return None;
    }
    let (index_method, value) = current_index_equality(consequent, var, param)?;
    let final_receiver = find_final_index_receiver(ensures, param, &index_method)
        .unwrap_or_else(|| final_expr(final_param_var.clone()));
    let bound_var = var_with_sort(var, var_sort.clone());
    let final_index = method_call(final_receiver, &index_method, vec![bound_var.clone()]);
    let final_len = len_expr(view_expr(final_expr(final_param_var.clone())));
    Some(PureExpr::Forall {
        var: var.clone(),
        var_sort: var_sort.clone(),
        body: Arc::new(implies_expr(
            and_expr(
                le_expr(zero(), bound_var.clone()),
                lt_expr(bound_var, final_len),
            ),
            eq_expr(final_index.clone(), value),
        )),
        triggers: vec![vec![final_index]],
    })
}

fn build_loop_exit_final_transfer_facts(
    invariants: &[PureExpr],
    ensures: &[PureExpr],
    final_values: &std::collections::HashMap<String, PureExpr>,
    structural_state: Option<&crate::mir_analysis::ForLoopGhostState>,
) -> Vec<PureExpr> {
    let Some(state) = structural_state else {
        return Vec::new();
    };

    let mut entries: Vec<_> = final_values.iter().collect();
    entries.sort_by_key(|(lhs, _)| *lhs);

    let mut facts = Vec::new();
    for (param, final_value) in entries {
        if !is_identity_deref_final_value(param, final_value) {
            continue;
        }
        let Some(final_param_var) = find_final_param_var(ensures, param) else {
            continue;
        };

        let current_view = view_expr(final_param_var.clone());
        let final_view = view_expr(final_expr(final_param_var.clone()));
        let view_alias = eq_expr(final_view.clone(), current_view.clone());
        if !facts.contains(&view_alias) {
            facts.push(view_alias);
        }
        let len_alias = eq_expr(len_expr(current_view), len_expr(final_view));
        if !facts.contains(&len_alias) {
            facts.push(len_alias);
        }

        for invariant in invariants {
            if let Some(fact) = prefix_transfer_fact_from_invariant(
                invariant,
                state.produced_name.as_str(),
                param,
                &final_param_var,
                ensures,
            ) {
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
        }
    }
    facts
}

fn nested_loop_exit_transition_facts(
    loop_analysis: &LoopAnalysis,
    loop_idx: usize,
    per_loop_effective_invariants: &[Vec<PureExpr>],
    per_loop_conditions: &PerLoopConditions,
    logic_fns: Option<(&[LogicFnDef], &dyn Fn(&LogicFnDef) -> Option<i64>)>,
) -> Vec<PureExpr> {
    let current_loop = &loop_analysis.loops[loop_idx];
    let mut facts = Vec::new();

    for (other_idx, other_loop) in loop_analysis.loops.iter().enumerate() {
        if other_idx == loop_idx || !current_loop.body_blocks.contains(&other_loop.header) {
            continue;
        }

        for invariant in &per_loop_effective_invariants[other_idx] {
            if !facts.contains(invariant) {
                facts.push(invariant.clone());
            }
        }
        if let Some(condition) = per_loop_conditions[other_idx].as_ref() {
            let exited = PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone()));
            if !facts.contains(&exited) {
                facts.push(exited);
            }
        }

        let Some((logic_fns, cons_discriminant)) = logic_fns else {
            continue;
        };
        for derived in synthesize_nested_match_exit_facts(
            &per_loop_effective_invariants[other_idx],
            &facts,
            logic_fns,
            cons_discriminant,
        ) {
            if !facts.contains(&derived) {
                facts.push(derived);
            }
        }
    }

    facts
}

#[derive(Clone, Copy)]
struct ForallImplicationEquality<'a> {
    var: &'a str,
    var_sort: &'a Option<ExprSort>,
    antecedent: &'a PureExpr,
    lhs: &'a PureExpr,
    rhs: &'a PureExpr,
    triggers: &'a [Vec<PureExpr>],
}

fn forall_implication_equality(expr: &PureExpr) -> Option<ForallImplicationEquality<'_>> {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = expr
    else {
        return None;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
        return None;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = consequent.as_ref() else {
        return None;
    };
    Some(ForallImplicationEquality {
        var,
        var_sort,
        antecedent,
        lhs,
        rhs,
        triggers,
    })
}

struct MatchExitNoneBranch<'a> {
    receiver: &'a PureExpr,
    method: &'a str,
    none_body: &'a PureExpr,
}

fn synthesize_nested_match_exit_facts(
    invariants: &[PureExpr],
    exit_facts: &[PureExpr],
    logic_fns: &[LogicFnDef],
    cons_discriminant: &dyn Fn(&LogicFnDef) -> Option<i64>,
) -> Vec<PureExpr> {
    let mut synthesized = Vec::new();
    for invariant in invariants {
        let Some(parsed) = forall_implication_equality(invariant) else {
            continue;
        };
        for (stable_side, match_side) in [(parsed.lhs, parsed.rhs), (parsed.rhs, parsed.lhs)] {
            let Some(match_info) = option_identity_match_none_branch(match_side, parsed.var) else {
                continue;
            };
            // The exit fact says the receiver is `Nil` only for the
            // discriminant its enum gives `Cons` (D-237).
            let Some(cons) = crate::callbacks::list_match_exit::list_exit_discriminant(
                logic_fns,
                match_info.method,
                list_get_definition_has_nil_none_cons_recursive,
                cons_discriminant,
            ) else {
                continue;
            };
            if !has_completed_list_cons_exit(exit_facts, match_info.receiver, cons) {
                continue;
            }

            let fact = PureExpr::Forall {
                var: parsed.var.to_string(),
                var_sort: parsed.var_sort.clone(),
                body: Arc::new(implies_expr(
                    parsed.antecedent.clone(),
                    eq_expr(stable_side.clone(), match_info.none_body.clone()),
                )),
                triggers: parsed.triggers.to_vec(),
            };
            if !synthesized
                .iter()
                .any(|existing| proof_expr_equiv(existing, &fact))
            {
                synthesized.push(fact);
            }
        }
    }
    synthesized
}

fn option_identity_match_none_branch<'a>(
    match_expr: &'a PureExpr,
    quantified_var: &str,
) -> Option<MatchExitNoneBranch<'a>> {
    let PureExpr::Match { scrutinee, arms } = match_expr else {
        return None;
    };
    let (receiver, method, args) = logic_or_method_call(scrutinee.as_ref())?;
    if method != "get" || args.len() != 1 || !is_var_named_loose(&args[0], quantified_var) {
        return None;
    }

    let mut none_body = None;
    let mut saw_some_identity = false;
    for arm in arms {
        match &arm.pattern {
            Pattern::Constructor { name, inner }
                if short_constructor_name(name) == "None" && inner.is_none() =>
            {
                none_body = Some(&arm.body);
            }
            Pattern::Constructor {
                name,
                inner: Some(inner),
            } if short_constructor_name(name) == "Some" => {
                let Pattern::Binding(binding) = inner.as_ref() else {
                    return None;
                };
                if !is_some_constructor_of_var(&arm.body, binding) {
                    return None;
                }
                saw_some_identity = true;
            }
            _ => return None,
        }
    }

    none_body
        .filter(|_| saw_some_identity)
        .map(|none_body| MatchExitNoneBranch {
            receiver,
            method,
            none_body,
        })
}

fn logic_or_method_call(expr: &PureExpr) -> Option<(&PureExpr, &str, &[PureExpr])> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => Some((receiver.as_ref(), method.as_str(), args.as_slice())),
        PureExpr::LogicFnCall { name, args } if args.len() >= 2 => {
            Some((&args[0], name.as_str(), &args[1..]))
        }
        _ => None,
    }
}

fn has_completed_list_cons_exit(
    preconditions: &[PureExpr],
    receiver: &PureExpr,
    cons_discriminant: i64,
) -> bool {
    preconditions
        .iter()
        .any(|pre| is_not_discriminant_value(pre, receiver, cons_discriminant))
}

fn is_not_discriminant_value(expr: &PureExpr, receiver: &PureExpr, discriminant: i64) -> bool {
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => is_discriminant_equality(inner, receiver, discriminant),
        PureExpr::BinOp(lhs, BinOp::Ne, rhs) => {
            discriminant_call_matches(lhs, receiver, discriminant, rhs)
                || discriminant_call_matches(rhs, receiver, discriminant, lhs)
        }
        _ => false,
    }
}

fn is_discriminant_equality(expr: &PureExpr, receiver: &PureExpr, discriminant: i64) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    discriminant_call_matches(lhs, receiver, discriminant, rhs)
        || discriminant_call_matches(rhs, receiver, discriminant, lhs)
}

fn discriminant_call_matches(
    maybe_call: &PureExpr,
    receiver: &PureExpr,
    discriminant: i64,
    maybe_value: &PureExpr,
) -> bool {
    matches!(maybe_value, PureExpr::Int(value) if *value == discriminant)
        && matches!(
            maybe_call,
            PureExpr::MethodCall {
                receiver: call_receiver,
                method,
                args,
            } if method == "discriminant" && args.is_empty() && proof_expr_equiv(call_receiver, receiver)
        )
}

fn list_get_definition_has_nil_none_cons_recursive(def: &LogicFnDef) -> bool {
    if !def.is_recursive() || !def.requires().is_empty() {
        return false;
    }
    let Some(self_param) = def.params().first() else {
        return false;
    };
    let PureExpr::Match { scrutinee, arms } = def.body() else {
        return false;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == self_param) {
        return false;
    }
    if arms.len() != 2 {
        return false;
    }

    let mut saw_nil_none = false;
    let mut saw_cons = false;
    for arm in arms {
        let Pattern::Constructor { name, .. } = &arm.pattern else {
            return false;
        };
        match short_constructor_name(name) {
            "Nil" => {
                if !is_none_constructor(&arm.body) {
                    return false;
                }
                saw_nil_none = true;
            }
            "Cons" => saw_cons = true,
            _ => return false,
        }
    }
    saw_nil_none && saw_cons
}

fn short_constructor_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// Recover the snapshot-captured expression `E` from a loop invariant of the
/// shape `E + acc == *snap` (any commutation), used by the loop-postcondition
/// snapshot-expression rewrite (#2702).
///
/// Returns `(E, snap_name)` when:
/// - one side of the invariant equality is `Deref(Var(snap))`,
/// - the other side is `E + acc` (or `acc + E`),
/// - every variable in `acc` is bound pre-loop to the literal integer `0`.
///
/// The pre-loop-`0` guard on `acc` is what makes the rewrite sound: it
/// guarantees the initialization VC forces `*snap == E_initial` (the invariant
/// at entry with all accumulators at `0`), so substituting an ensures `E` (which
/// denotes the parameter's initial value in Creusot) with `*snap` is meaning-
/// preserving rather than fact-inventing.
fn snapshot_captured_expr_from_invariant(
    inv: &PureExpr,
    pre_loop_assignments: &std::collections::HashMap<
        String,
        trust_wp_core::formula::NamedBindingValue,
    >,
) -> Option<(PureExpr, String)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = inv else {
        return None;
    };
    let snap_deref_name = |e: &PureExpr| -> Option<String> {
        if let PureExpr::Deref(inner) = e {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                return Some(name.clone());
            }
        }
        None
    };
    let (sum_side, snap_name) = if let Some(name) = snap_deref_name(rhs) {
        (lhs.as_ref(), name)
    } else if let Some(name) = snap_deref_name(lhs) {
        (rhs.as_ref(), name)
    } else {
        return None;
    };
    let PureExpr::BinOp(a, BinOp::Add, b) = sum_side else {
        return None;
    };
    let acc_is_pre_loop_zero = |e: &PureExpr| -> bool {
        let vars = expr_referenced_vars(e);
        !vars.is_empty()
            && vars.iter().all(|v| {
                matches!(
                    pre_loop_assignments.get(v).map(|nb| &nb.value),
                    Some(PureExpr::Int(0))
                )
            })
    };
    // `E` is the operand that is NOT a pure pre-loop-zero accumulator; the other
    // operand must be entirely pre-loop-zero accumulators.
    if acc_is_pre_loop_zero(b) {
        Some((a.as_ref().clone(), snap_name))
    } else if acc_is_pre_loop_zero(a) {
        Some((b.as_ref().clone(), snap_name))
    } else {
        None
    }
}

/// Whether `haystack` contains `needle` as a structural sub-expression.
fn expr_contains_subexpr(haystack: &PureExpr, needle: &PureExpr) -> bool {
    let mut found = false;
    haystack.for_each_recursive(|node| {
        if node == needle {
            found = true;
        }
    });
    found
}

/// Replace every occurrence of `from` with `to` inside `expr`.
fn replace_subexpr(expr: &PureExpr, from: &PureExpr, to: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| if &node == from { to.clone() } else { node })
}

fn is_none_constructor(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => short_constructor_name(name) == "None",
        PureExpr::LogicFnCall { name, args } => {
            args.is_empty() && short_constructor_name(name) == "None"
        }
        _ => false,
    }
}

fn is_some_constructor_of_var(expr: &PureExpr, var: &str) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == "Some"
                && matches!(args.as_slice(), [arg] if is_var_named_loose(arg, var))
    )
}

fn is_var_named_loose(expr: &PureExpr, expected: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == expected,
        PureExpr::View(inner) => is_var_named_loose(inner, expected),
        _ => false,
    }
}

fn proof_expr_equiv(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    if lhs == rhs {
        return true;
    }
    match (lhs, rhs) {
        (PureExpr::Var(lhs_name, _), PureExpr::Var(rhs_name, _)) => lhs_name == rhs_name,
        (PureExpr::View(inner), PureExpr::Var(name, _))
        | (PureExpr::Var(name, _), PureExpr::View(inner)) => is_var_named_loose(inner, name),
        (PureExpr::View(lhs_inner), PureExpr::View(rhs_inner))
        | (PureExpr::Old(lhs_inner), PureExpr::Old(rhs_inner))
        | (PureExpr::Deref(lhs_inner), PureExpr::Deref(rhs_inner))
        | (PureExpr::Final(lhs_inner), PureExpr::Final(rhs_inner)) => {
            proof_expr_equiv(lhs_inner, rhs_inner)
        }
        (PureExpr::BinOp(lhs_l, lhs_op, lhs_r), PureExpr::BinOp(rhs_l, rhs_op, rhs_r)) => {
            lhs_op == rhs_op && proof_expr_equiv(lhs_l, rhs_l) && proof_expr_equiv(lhs_r, rhs_r)
        }
        (PureExpr::UnOp(lhs_op, lhs_inner), PureExpr::UnOp(rhs_op, rhs_inner)) => {
            lhs_op == rhs_op && proof_expr_equiv(lhs_inner, rhs_inner)
        }
        (
            PureExpr::MethodCall {
                receiver: lhs_receiver,
                method: lhs_method,
                args: lhs_args,
            },
            PureExpr::MethodCall {
                receiver: rhs_receiver,
                method: rhs_method,
                args: rhs_args,
            },
        ) => {
            lhs_method == rhs_method
                && proof_expr_equiv(lhs_receiver, rhs_receiver)
                && expr_slices_equiv(lhs_args, rhs_args)
        }
        (
            PureExpr::LogicFnCall {
                name: lhs_name,
                args: lhs_args,
            },
            PureExpr::LogicFnCall {
                name: rhs_name,
                args: rhs_args,
            },
        ) => {
            // Two logic functions that share a last path segment are two
            // functions (D-237).
            lhs_name == rhs_name && expr_slices_equiv(lhs_args, rhs_args)
        }
        (
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            },
            PureExpr::LogicFnCall {
                name,
                args: logic_args,
            },
        )
        | (
            PureExpr::LogicFnCall {
                name,
                args: logic_args,
            },
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            },
        ) => {
            short_constructor_name(name) == method
                && logic_args
                    .split_first()
                    .is_some_and(|(logic_receiver, logic_tail)| {
                        proof_expr_equiv(receiver, logic_receiver)
                            && expr_slices_equiv(args, logic_tail)
                    })
        }
        _ => false,
    }
}

fn expr_slices_equiv(lhs: &[PureExpr], rhs: &[PureExpr]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs)
            .all(|(lhs, rhs)| proof_expr_equiv(lhs, rhs))
}

fn inherit_outer_invariant(
    effective_requires: &mut Vec<PureExpr>,
    effective_invariants: &mut Vec<PureExpr>,
    invariant: &PureExpr,
    modified_vars: &[String],
) -> usize {
    let mut added = 0usize;

    if !effective_requires.contains(invariant) {
        effective_requires.push(invariant.clone());
        added += 1;
    }

    let inv_vars = expr_referenced_vars(invariant);
    let inv_stable = inv_vars.iter().all(|var| !modified_vars.contains(var));
    if inv_stable && !effective_invariants.contains(invariant) {
        effective_invariants.push(invariant.clone());
        added += 1;
    }

    added
}

fn invariant_vars_available_at_loop_entry(
    invariant: &PureExpr,
    arg_names: &[String],
    pre_loop_assignments: &std::collections::HashMap<
        String,
        trust_wp_core::formula::NamedBindingValue,
    >,
) -> bool {
    let vars = expr_referenced_vars(invariant);
    vars.iter()
        .all(|var| arg_names.contains(var) || pre_loop_assignments.contains_key(var))
}

/// Decompose a struct-typed variant into an integer field sum for loop
/// variant verification (#2665).
///
/// When a loop `#[variant(x)]` has a struct type with all-integer fields
/// (e.g., `CustomVariant(pub u32, pub u32)` from WellFounded impls), the
/// ay encoder cannot perform integer arithmetic on the opaque struct sort.
/// This function rewrites the variant expression from `Var("x")` into
/// `__trust_wp_tuple_get_0(x) + __trust_wp_tuple_get_1(x)`, producing a valid
/// integer expression that the loop variant checking pipeline can use.
///
/// Returns `None` if the variant is already integer-typed or cannot be
/// decomposed, in which case the original variant expression should be used.
fn decompose_struct_variant_to_field_sum(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    variant: &PureExpr,
    arg_names: &[String],
) -> Option<PureExpr> {
    let PureExpr::Var(ref var_name, _) = variant else {
        return None;
    };

    let param_idx = arg_names.iter().position(|n| n == var_name)?;

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();
    if param_idx >= inputs.len() {
        return None;
    }
    let param_ty = inputs[param_idx];

    match param_ty.kind() {
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Char => None,
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
            let variant_def = adt_def.non_enum_variant();
            let mut field_getters = Vec::new();
            for (idx, field) in variant_def.fields.iter().enumerate() {
                let field_ty = field.ty(tcx, *substs).skip_norm_wip();
                match field_ty.kind() {
                    TyKind::Int(_) | TyKind::Uint(_) => {
                        let getter_name = tuple_field_logic_fn_name(idx);
                        field_getters.push(PureExpr::LogicFnCall {
                            name: getter_name,
                            args: vec![variant.clone()],
                        });
                    }
                    _ => return None, // Non-integer field, cannot decompose
                }
            }
            if field_getters.is_empty() {
                return None;
            }
            // Sum all field getters: get_0(x) + get_1(x) + ...
            let mut sum = field_getters.remove(0);
            for getter in field_getters {
                sum = PureExpr::BinOp(Arc::new(sum), BinOp::Add, Arc::new(getter));
            }
            Some(sum)
        }
        _ => None,
    }
}

/// Loop orchestration data shared across all per-loop iterations (#2657).
///
/// Bundles the cross-loop invariants, conditions, and inferred clauses that
/// are constant across all loops within a single verification pass, keeping
/// `verify_single_loop` under clippy's `too_many_arguments` threshold.
pub(super) struct LoopOrchestrationData<'a> {
    pub(super) per_loop_effective_invariants: &'a [Vec<PureExpr>],
    pub(super) per_loop_conditions: &'a PerLoopConditions,
    pub(super) per_loop_nested_active_facts: &'a [Vec<PureExpr>],
    pub(super) inferred_unsigned_invariants: &'a [PureExpr],
    pub(super) inferred_unsigned_requires: &'a [PureExpr],
    pub(super) returns_ghost: bool,
}

/// Verify a single loop and return its results for orchestrator folding. (#2337)
///
/// Encapsulates the per-loop verification logic that was previously inline
/// in the `verify_loop_with_invariant` for-loop body. The orchestrator
/// accumulates `SingleLoopResult` values across all loops.
pub(super) fn verify_single_loop(
    tcx: TyCtxt<'_>,
    req: &LoopWithInvariantRequest<'_>,
    loop_idx: usize,
    pre_extracted_body: PreExtractedLoopBody,
    orch: &LoopOrchestrationData<'_>,
    all_modified_vars: &mut std::collections::HashSet<String>,
) -> Result<SingleLoopResult, EncodingError> {
    let per_loop_effective_invariants = orch.per_loop_effective_invariants;
    let per_loop_conditions = orch.per_loop_conditions;
    let per_loop_nested_active_facts = orch.per_loop_nested_active_facts;
    let inferred_unsigned_invariants = orch.inferred_unsigned_invariants;
    let inferred_unsigned_requires = orch.inferred_unsigned_requires;
    let returns_ghost = orch.returns_ghost;
    let verbose = req.verbose;
    let parsed = req.parsed;
    let loop_analysis = req.loop_analysis;
    let loop_info = &loop_analysis.loops[loop_idx];

    if verbose {
        debug!(
            loop_idx,
            header = loop_info.header.as_u32(),
            "verifying loop"
        );
    }

    let (loop_body_expr, loop_header_byte_pos) =
        if let Some((body_expr, header_pos)) = pre_extracted_body {
            (Some(body_expr), Some(header_pos))
        } else {
            (None, None)
        };

    // Whether the walk that fills `changed_places` / `pre_loop_deref_stored_names`
    // / `post_loop_deref_final_values` ran at all. Without it those records are
    // empty for want of a walk, not for want of writes, and nothing may be
    // inferred from their emptiness.
    let loop_body_extracted = loop_body_expr.is_some();

    // prophecy-store: see `LoopBodyExpr::pre_loop_deref_stored_names`.
    let pre_loop_deref_stored_names: std::collections::HashSet<String> = loop_body_expr
        .as_ref()
        .map(|expr| expr.pre_loop_deref_stored_names.clone())
        .unwrap_or_default();
    let (
        mut loop_condition,
        condition_is_body_break,
        modified_vars,
        changed_places,
        body_effect,
        deref_body_effect,
        double_deref_body_effect,
        mut pre_loop_assignments,
        pre_loop_written_params,
        mut return_expr,
        post_loop_deref_writes,
        mut post_loop_deref_final_values,
        for_loop_state,
        pre_loop_init_facts,
        borrow_backing_names,
        call_facts,
        dropped_premises,
        condition_facts,
        condition_unstated,
    ) = if let Some(expr) = loop_body_expr {
        let resolved_calls = resolve_pre_loop_calls(
            tcx,
            &expr.unresolved_pre_loop_calls,
            req.extern_specs,
            &expr.ref_source_locals,
        );
        let mut assignments = expr.pre_loop_assignments;
        assignments.extend(resolved_calls);
        (
            expr.condition,
            expr.condition_is_body_break,
            expr.modified_vars,
            expr.changed_places,
            expr.body_effects,
            expr.deref_body_effects,
            expr.double_deref_body_effects,
            assignments,
            expr.pre_loop_written_params,
            expr.return_expr,
            expr.post_loop_deref_writes,
            expr.post_loop_deref_final_values,
            expr.for_loop_state,
            expr.pre_loop_init_facts,
            expr.borrow_backing_names,
            expr.call_facts,
            expr.dropped_premises,
            expr.condition_facts,
            expr.condition_unstated,
        )
    } else {
        (
            None,
            false,
            vec![],
            ChangedPlaces::default(),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashSet::new(),
            None,
            std::collections::HashSet::new(),
            std::collections::HashMap::new(),
            None,
            Vec::new(),
            std::collections::HashMap::new(),
            Vec::new(),
            vec![crate::mir_analysis::DroppedPremise {
                block: loop_info.header,
                what: "the loop body, which was not extracted".to_string(),
                iterator_step: false,
                only_about: None,
            }],
            Vec::new(),
            None,
        )
    };
    let filtered_postcondition_deref =
        filter_post_loop_borrow_resolution_vars(deref_body_effect.clone(), &post_loop_deref_writes);

    if std::env::var_os("TRUST_WP_LOOP_EFFECT_DUMP").is_some() {
        let def_path = req.def_path;
        eprintln!(
            "TRUST_WP_LOOP_EFFECT_DUMP def_path={def_path} modified_vars={modified_vars:?} \
             body_effects={body_effect:?} deref_body_effects={deref_body_effect:?} \
             double_deref_body_effects={double_deref_body_effect:?} \
             pre_loop_assignments={pre_loop_assignments:?}"
        );
    }

    // What the loops before this one may have changed, for the entry-value
    // check below.
    let written_by_earlier_loops: std::collections::HashSet<String> = all_modified_vars.clone();
    all_modified_vars.extend(modified_vars.iter().cloned());

    let frame_contributions = {
        let modified_set: std::collections::HashSet<&str> =
            all_modified_vars.iter().map(String::as_str).collect();
        let mut contributions = Vec::new();
        for (name, binding) in &pre_loop_assignments {
            if modified_set.contains(name.as_str()) {
                continue;
            }
            let value_vars = expr_referenced_vars(&binding.value);
            if value_vars.iter().any(|v| modified_set.contains(v.as_str())) {
                continue;
            }
            contributions.push((
                name.clone(),
                PureExpr::BinOp(
                    Arc::new(binding.lhs_var(name)),
                    trust_wp_core::formula::BinOp::Eq,
                    Arc::new(binding.value.clone()),
                ),
            ));
        }
        contributions
    };

    if verbose {
        if let Some(ref cond) = loop_condition {
            trace!("loop condition: {cond:?}");
        } else {
            trace!("loop condition: not extractable");
        }
        if !modified_vars.is_empty() {
            trace!("modified vars: {modified_vars:?}");
        }
        if !body_effect.is_empty() {
            trace!("body effects: {body_effect:?}");
        }
        if !deref_body_effect.is_empty() {
            trace!("deref body effects: {deref_body_effect:?}");
        }
        if !double_deref_body_effect.is_empty() {
            trace!("double-deref body effects: {double_deref_body_effect:?}");
        }
        if !post_loop_deref_writes.is_empty() {
            trace!("post-loop deref writes: {post_loop_deref_writes:?}");
        }
        if !pre_loop_assignments.is_empty() {
            trace!("pre-loop assignments: {pre_loop_assignments:?}");
        }
        if let Some(ref ret) = return_expr {
            trace!("return expr: {ret:?}");
        }
    }

    let mut variant = select_loop_variant(
        &parsed.loop_fields.variants,
        &parsed.loop_fields.per_loop_variants,
        &parsed.loop_fields.all_loop_spans,
        loop_analysis.loops.len(),
        loop_header_byte_pos,
    )?
    .cloned();
    // A variant names the bindings visible at its loop, as an invariant does
    // (D-237, D-238): read by its source name it would be the parameter a
    // shadowing `let` hides, or a macro's hygienic binding.
    if let Some(v) = variant.take() {
        variant = match crate::callbacks::try_get_body_with_context(tcx, req.contract.local_def_id)
        {
            Some(body_with_facts) => crate::mir_analysis::binding_identity::resolve_loop_clauses(
                crate::mir_analysis::get_mir_body(&body_with_facts),
                loop_info.header,
                vec![v],
            )
            .pop(),
            None => Some(v),
        };
    }

    // Decompose struct-typed variants into integer field sums (#2665).
    // WellFounded variant types (e.g., CustomVariant(u32, u32)) encode
    // to opaque sorts that the ay variant checking pipeline cannot handle.
    // Rewrite to `get_0(x) + get_1(x)` so variant arithmetic works.
    if let Some(ref v) = variant {
        if let Some(decomposed) =
            decompose_struct_variant_to_field_sum(tcx, req.contract.def_id, v, &parsed.arg_names)
        {
            if verbose {
                debug!("decomposed struct variant to field sum: {decomposed:?}");
            }
            variant = Some(decomposed);
        }
    }

    let mut effective_invariants = if let (false, Some(header_pos)) = (
        parsed.loop_fields.per_loop_invariants.is_empty(),
        loop_header_byte_pos,
    ) {
        let invs = find_loop_invariants(
            &parsed.loop_fields.per_loop_invariants,
            &parsed.loop_fields.all_loop_spans,
            header_pos,
        );
        // An invariant names the bindings visible at its loop (D-237).
        let invs = match crate::callbacks::try_get_body_with_context(tcx, req.contract.local_def_id)
        {
            Some(body_with_facts) => crate::mir_analysis::binding_identity::resolve_loop_clauses(
                crate::mir_analysis::get_mir_body(&body_with_facts),
                loop_info.header,
                invs,
            ),
            None => invs,
        };
        if verbose {
            debug!(
                header_pos,
                invariants = invs.len(),
                "per-loop invariant match"
            );
        }
        invs
    } else {
        match crate::callbacks::try_get_body_with_context(tcx, req.contract.local_def_id) {
            Some(body_with_facts) => crate::mir_analysis::binding_identity::resolve_loop_clauses(
                crate::mir_analysis::get_mir_body(&body_with_facts),
                loop_info.header,
                parsed.loop_fields.invariants.clone(),
            ),
            None => parsed.loop_fields.invariants.clone(),
        }
    };
    // Everything pushed below is inferred; the stated clauses stay in front.
    let stated_invariant_count = effective_invariants.len();
    let structural_state = for_loop_state.as_ref();
    for inv in inferred_unsigned_invariants {
        if is_for_loop_element_nonnegative_invariant(inv, structural_state) {
            continue;
        }
        if !invariant_vars_available_at_loop_entry(inv, &parsed.arg_names, &pre_loop_assignments) {
            continue;
        }
        if !effective_invariants.contains(inv) {
            effective_invariants.push(inv.clone());
        }
    }

    let inferred_stable = infer_stable_loop_invariants(
        req.requires,
        &pre_loop_assignments,
        &modified_vars,
        &effective_invariants,
        &parsed.arg_names,
    );
    if !inferred_stable.is_empty() {
        if verbose {
            debug!(
                count = inferred_stable.len(),
                "inferred stable loop invariants (#1816)"
            );
            for inv in &inferred_stable {
                trace!("stable invariant: {inv:?}");
            }
        }
        for inv in inferred_stable {
            effective_invariants.push(inv);
        }
    }

    let (param_frame_pre_loop, param_frame_invariants) = infer_parameter_frame_invariants(
        &parsed.arg_names,
        &parsed.mut_borrow.mut_ref_param_names,
        &changed_places,
        &pre_loop_assignments,
        &effective_invariants,
        &modified_vars,
    );
    if !param_frame_invariants.is_empty() {
        if verbose {
            debug!(
                count = param_frame_invariants.len(),
                "inferred prophecy frame invariants (#1816 Phase 2)"
            );
            for inv in &param_frame_invariants {
                trace!("prophecy frame invariant: {inv:?}");
            }
        }
        pre_loop_assignments.extend(param_frame_pre_loop);
        for inv in param_frame_invariants {
            effective_invariants.push(inv);
        }
    }

    let mut final_params_in_ensures = std::collections::HashSet::new();
    for ensure in req.transformed_ensures {
        extract_final_vars(ensure, &mut final_params_in_ensures);
    }
    let mut synthesized_post_loop_final_values = 0usize;
    for param in &parsed.mut_borrow.mut_ref_param_names {
        if !final_params_in_ensures.contains(param) {
            continue;
        }
        // What this mints is `param_final == *param_current`, and
        // `*param_current` is the pointee at FUNCTION ENTRY — so the identity
        // claims the whole function leaves the pointee alone, not merely the
        // loop. The lane may say that only where it SAW every write that could
        // contradict it, and the three places a write can hide are the three
        // guards below:
        //
        //   - inside the loop: `changed_places` records a store through `*p`
        //     as `Deref(..)` under `p`, a reassignment of `p` itself as
        //     `Changed`, and an escape into a mutating call the same way. ANY
        //     entry against `p` is a write this identity would erase, so a
        //     `Deref(..)` is a refusal exactly like a `Changed`
        //     (`annotated_loop_param_write_prophecy_lost`,
        //     `annotated_loop_mutating_call_write_lost`,
        //     `annotated_loop_slot_alias_write_lost`).
        //   - before the loop: a store through a reference reaching the header
        //     is what `pre_loop_deref_stored_names` is; the loop body this lane
        //     walked never contained it
        //     (`annotated_loop_prior_write_prophecy_erased`).
        //   - after the loop: such a write already has its own extracted entry,
        //     which the lane must not overwrite with the identity.
        //
        // With no loop-body extraction at all there is no evidence of any kind,
        // and an identity minted from an empty record is a grant made by code
        // that saw nothing.
        if !loop_body_extracted {
            continue;
        }
        if changed_places.0.contains_key(param) {
            continue;
        }
        if pre_loop_deref_stored_names.contains(param) {
            continue;
        }
        if post_loop_deref_final_values.contains_key(param) {
            continue;
        }
        post_loop_deref_final_values.insert(
            param.clone(),
            PureExpr::Deref(Arc::new(PureExpr::Var(param.clone(), None))),
        );
        synthesized_post_loop_final_values += 1;
    }
    if verbose && synthesized_post_loop_final_values > 0 {
        debug!(
            count = synthesized_post_loop_final_values,
            "synthesized loop-exit identity final_values for unchanged &mut params (#1816)",
        );
    }

    let inferred_type_inv =
        infer_stable_type_invariant_clauses(req.requires, &changed_places, &effective_invariants);
    if !inferred_type_inv.is_empty() {
        if verbose {
            debug!(
                count = inferred_type_inv.len(),
                "inferred type-invariant loop invariants (#1816)"
            );
            for inv in &inferred_type_inv {
                trace!("type-invariant invariant: {inv:?}");
            }
        }
        for inv in inferred_type_inv {
            effective_invariants.push(inv);
        }
    }

    let mut effective_requires = req.requires.to_vec();
    for inferred_req in inferred_unsigned_requires {
        if !effective_requires.contains(inferred_req) {
            effective_requires.push(inferred_req.clone());
        }
    }

    for (other_idx, other_loop) in loop_analysis.loops.iter().enumerate() {
        if other_idx != loop_idx && other_loop.body_blocks.contains(&loop_info.header) {
            let mut added = 0usize;
            for inv in &per_loop_effective_invariants[other_idx] {
                // Outer invariants remain valid initialization facts even
                // when the inner loop already lists the same formula as an
                // invariant. Without this, duplicate inner invariants suppress
                // the outer fact from `effective_requires`, making init fail
                // on nested loops like 100doors. (#2698)
                added += inherit_outer_invariant(
                    &mut effective_requires,
                    &mut effective_invariants,
                    inv,
                    &modified_vars,
                );
            }
            if let Some(outer_cond) = &per_loop_conditions[other_idx] {
                let cond_vars = expr_referenced_vars(outer_cond);
                let cond_stable = cond_vars.iter().all(|var| !modified_vars.contains(var));
                if cond_stable {
                    if !effective_requires.contains(outer_cond) {
                        effective_requires.push(outer_cond.clone());
                        added += 1;
                    }
                    if !effective_invariants.contains(outer_cond) {
                        effective_invariants.push(outer_cond.clone());
                        added += 1;
                    }
                }
            }
            for fact in &per_loop_nested_active_facts[other_idx] {
                added += inherit_outer_invariant(
                    &mut effective_requires,
                    &mut effective_invariants,
                    fact,
                    &modified_vars,
                );
            }
            if added > 0 && verbose {
                debug!(
                    added,
                    outer_loop = other_idx,
                    "inherited invariant(s) from outer loop (#2698)"
                );
            }
        }
    }

    let effective_ensures = rewrite_loop_ensures_for_ghost_return(
        req.transformed_ensures,
        returns_ghost,
        return_expr.as_ref(),
    );
    let mut effective_ensures = rewrite_loop_postcondition_old(
        &effective_ensures,
        &parsed.arg_names,
        &parsed.mut_borrow.mut_ref_param_names,
        &pre_loop_written_params,
        &modified_vars,
    )?;

    // Substitute modified by-value parameters in ensures with snapshot
    // dereferences (#2665). In Creusot semantics, postcondition parameters
    // refer to their initial (function-entry) values, but in the loop
    // postcondition VC (invariant /\ !condition => ensures), variable names
    // resolve to loop-exit values.
    //
    // For by-value parameters modified by the loop body (e.g., `mut x`
    // decremented in a while-loop), we search for an existing snapshot binding
    // in pre_loop_assignments whose value is `View(Var(param))` — this
    // corresponds to `let snap = snapshot!(param@)`. If found, we rewrite
    // `param` in ensures to `Deref(Var(snap_name))` (i.e., `*snap`).
    //
    // Example: `ensures(result == x)` with `let total = snapshot!(x@)`.
    // The driver rewrites ensures to `result == *total`. The user-written
    // invariant `*total == x@ + result@` then proves the postcondition:
    // at loop exit `x == 0`, so `*total == result`, hence `result == *total`.
    {
        let modified_set: std::collections::HashSet<&str> =
            modified_vars.iter().map(String::as_str).collect();
        let mut param_initial_subs = std::collections::HashMap::new();
        for param in &parsed.arg_names {
            // Only rewrite by-value parameters that are modified by the loop.
            if !modified_set.contains(param.as_str()) {
                continue;
            }
            // Skip &mut reference parameters — they have their own Final/Old rewrite.
            if parsed.mut_borrow.mut_ref_param_names.contains(param) {
                continue;
            }
            // Only substitute if the parameter actually appears in ensures.
            let param_in_ensures = effective_ensures
                .iter()
                .any(|e| expr_referenced_vars(e).iter().any(|v| v == param));
            if !param_in_ensures {
                continue;
            }
            // Search pre_loop_assignments for a snapshot binding that captures
            // this parameter: a binding whose value is View(Var(param)).
            let snapshot_binding = pre_loop_assignments.iter().find(|(_, binding)| {
                matches!(
                    &binding.value,
                    PureExpr::View(inner) if matches!(
                        inner.as_ref(),
                        PureExpr::Var(name, _) if name == param
                    )
                )
            });
            if let Some((snap_name, _)) = snapshot_binding {
                // Found snapshot!(param@) → substitute param with *snap_name
                param_initial_subs.insert(
                    param.clone(),
                    PureExpr::Deref(Arc::new(PureExpr::Var(snap_name.clone(), None))),
                );
                if verbose {
                    debug!(
                        param = %param,
                        snapshot = %snap_name,
                        "rewriting modified param in ensures via snapshot deref (#2665)"
                    );
                }
            }
            // If no snapshot binding found, leave the parameter as-is.
            // The user must provide invariant infrastructure (snapshot + invariant)
            // for the postcondition to be provable with modified parameters.
        }
        if !param_initial_subs.is_empty() {
            effective_ensures = effective_ensures
                .iter()
                .map(|e| e.substitute(&param_initial_subs))
                .collect();
        }

        // Generalized snapshot-expression rewrite for the loop postcondition VC
        // (#2702). The param-keyed rewrite above only handles ensures that name a
        // modified parameter directly (e.g. `result == x` with `let s =
        // snapshot!(x@)`). A postcondition over a *projection* of a modified
        // parameter (e.g. `result@ == Int::min(x.0@, x.1@)` with
        // `let res = snapshot!(Int::min(x.0@, x.1@))`) needs the captured
        // expression itself rewritten to the snapshot deref.
        //
        // We recover the captured expression from a loop INVARIANT of the shape
        // `E + acc == *snap` (any commutation), where `acc` is built only from
        // accumulator variables whose pre-loop value is the literal `0`, and `E`
        // references a modified parameter and appears verbatim in some ensures.
        //
        // SOUNDNESS: the snapshot `snap` is loop-invariant (captured pre-loop),
        // so `*snap` is constant. The initialization VC forces the invariant to
        // hold at loop entry with each accumulator at its pre-loop value; since
        // every accumulator in `acc` is pre-loop `0`, that gives
        // `*snap == E_initial`. In Creusot a postcondition over a by-value
        // parameter denotes its initial value, so the ensures' `E` is `E_initial`
        // — exactly `*snap`. Substituting `E -> *snap` therefore preserves the
        // meaning of the postcondition; it never invents a fact, and the
        // accumulator-is-pre-loop-0 guard prevents matching invariants whose
        // `*snap` is offset from `E_initial`.
        let mut expr_initial_subs: Vec<(PureExpr, PureExpr)> = Vec::new();
        for inv in &effective_invariants {
            let Some((captured, snap_name)) =
                snapshot_captured_expr_from_invariant(inv, &pre_loop_assignments)
            else {
                continue;
            };
            // The captured expression must reference a modified variable and
            // appear verbatim in the ensures; otherwise there is nothing sound
            // to rewrite.
            if !expr_referenced_vars(&captured)
                .iter()
                .any(|v| modified_set.contains(v.as_str()))
            {
                continue;
            }
            let appears_in_ensures = effective_ensures
                .iter()
                .any(|e| expr_contains_subexpr(e, &captured));
            if !appears_in_ensures {
                continue;
            }
            let snap_deref = PureExpr::Deref(Arc::new(PureExpr::Var(snap_name.clone(), None)));
            expr_initial_subs.push((captured, snap_deref));
            if verbose {
                debug!(snapshot = %snap_name, "rewriting captured ensures sub-expression via snapshot deref (#2702)");
            }
        }
        if !expr_initial_subs.is_empty() {
            effective_ensures = effective_ensures
                .iter()
                .map(|e| {
                    let mut rewritten = e.clone();
                    for (from, to) in &expr_initial_subs {
                        rewritten = replace_subexpr(&rewritten, from, to);
                    }
                    rewritten
                })
                .collect();
        }
    }

    if let Some(state) = structural_state {
        let produced_name = state.produced_name.as_str();
        effective_requires = effective_requires
            .into_iter()
            .map(|expr| annotate_seq_loop_var(&expr, produced_name))
            .collect();
        effective_invariants = effective_invariants
            .into_iter()
            .map(|expr| annotate_seq_loop_var(&expr, produced_name))
            .collect();
        effective_ensures = effective_ensures
            .into_iter()
            .map(|expr| annotate_seq_loop_var(&expr, produced_name))
            .collect();
        loop_condition = loop_condition.map(|expr| annotate_seq_loop_var(&expr, produced_name));
        variant = variant.map(|expr| annotate_seq_loop_var(&expr, produced_name));
    }

    // Loop-invariant inference Stage 0 (#flagship): supply the missing iterator
    // bound `produced.len() <= L` so a `*len - produced.len()` variant can be
    // proven non-negative (`loop_variant_nonneg`). Injected as a CANDIDATE into
    // `effective_invariants` only — the standard WP obligations verify it, so a
    // wrong guess just fails (never a false-accept). Narrowly gated to genuine
    // produced-bearing for-loops with that exact variant shape.
    let inferred_produced_len_bound = infer_iterator_produced_len_bound(
        variant.as_ref(),
        structural_state,
        &effective_invariants,
    );
    if !inferred_produced_len_bound.is_empty() {
        if verbose {
            debug!(
                count = inferred_produced_len_bound.len(),
                "inferred iterator produced-length bound (loop-invariant inference Stage 0)"
            );
            for inv in &inferred_produced_len_bound {
                trace!("produced-length bound invariant: {inv:?}");
            }
        }
        for inv in inferred_produced_len_bound {
            if !effective_invariants.contains(&inv) {
                effective_invariants.push(inv);
            }
        }
    }

    let mut continuation_assumptions = effective_invariants.clone();

    if let Some(state) = structural_state {
        let structural_inv = build_for_loop_structural_invariant(state);
        let rewritten_inv =
            super::super::iterator_spec_rewrite::rewrite_iterator_spec_expr(&structural_inv);
        if include_structural_invariant_in_loop_vc(
            state,
            &effective_invariants,
            &effective_ensures,
            loop_condition.as_ref(),
            variant.as_ref(),
        ) && !effective_invariants.contains(&rewritten_inv)
        {
            effective_invariants.push(rewritten_inv.clone());
        }
        if !continuation_assumptions.contains(&rewritten_inv) {
            continuation_assumptions.push(rewritten_inv);
        }
    }

    let mut init_facts = build_for_loop_init_facts(&effective_invariants, structural_state);
    for fact in pre_loop_init_facts {
        if !init_facts.contains(&fact) {
            init_facts.push(fact);
        }
    }
    let added_pre_loop_call_init_facts = append_first_outermost_pre_loop_call_assumptions(
        &mut init_facts,
        loop_analysis,
        loop_idx,
        &parsed.pre_loop_call_assumptions,
    );
    if verbose && added_pre_loop_call_init_facts > 0 {
        debug!(
            added = added_pre_loop_call_init_facts,
            "seeded first outermost loop initialization with pre-loop call assumptions"
        );
    }
    if verbose && !init_facts.is_empty() {
        trace!("loop init facts: {init_facts:?}");
    }
    let mut transition_facts =
        structural_state.map_or_else(Vec::new, build_transition_facts_for_loop_state);
    let cons_discriminant =
        |get: &LogicFnDef| crate::callbacks::list_match_exit::cons_discriminant_of(tcx, get);
    for fact in nested_loop_exit_transition_facts(
        loop_analysis,
        loop_idx,
        per_loop_effective_invariants,
        per_loop_conditions,
        req.logic_fns.map(|fns| {
            (
                fns,
                &cons_discriminant as &dyn Fn(&LogicFnDef) -> Option<i64>,
            )
        }),
    ) {
        if !transition_facts.contains(&fact) {
            transition_facts.push(fact);
        }
    }
    for fact in call_facts {
        if !transition_facts.contains(&fact) {
            transition_facts.push(fact);
        }
    }
    let mut bridge_facts = Vec::new();
    // Layer-3 prophecy-datatype structure facts. For a recursive-datatype loop
    // `while let Cons(head, tail) = scrut { ..*head..; scrut = tail }`, emit the
    // current-value and prophecy constructor splits so recursive_unfolding's
    // symbolic unfold can reduce `get(^scrut, i)` / `len(^scrut)` (and their
    // current-value forms) to bounded one-step ground facts instead of leaving an
    // inert `match ^scrut {..}`. SOUND: `scrut`'s self-referential cons-tail
    // body_effect (`Deref(tuple_get_1(Deref(Var scrut)))`) is present only when the
    // provably-rooted `trace_cons_tail_ref_root` check accepted the reborrow, so
    // `scrut` is genuinely the while-let-Cons recursion variable and `head`/`tail`
    // are its field reborrows.
    for (scrut, effect) in &body_effect {
        let PureExpr::Deref(inner) = effect else {
            continue;
        };
        let PureExpr::LogicFnCall { name, args } = inner.as_ref() else {
            continue;
        };
        if *name != tuple_field_logic_fn_name(1) || args.len() != 1 {
            continue;
        }
        let PureExpr::Deref(d) = &args[0] else {
            continue;
        };
        let PureExpr::Var(v, scrut_sort) = d.as_ref() else {
            continue;
        };
        if v != scrut {
            continue;
        }
        let head = modified_vars
            .iter()
            .find(|m| m.as_str() != scrut.as_str() && deref_body_effect.contains_key(*m));
        let tail = modified_vars
            .iter()
            .find(|m| m.as_str() != scrut.as_str() && !deref_body_effect.contains_key(*m));
        if let (Some(head), Some(tail)) = (head, tail) {
            let var = |n: &str| PureExpr::Var(n.to_string(), None);
            let cons = |a: PureExpr, b: PureExpr| PureExpr::LogicFnCall {
                name: "Cons".to_string(),
                args: vec![a, b],
            };
            let eq = |l: PureExpr, r: PureExpr| {
                PureExpr::BinOp(Arc::new(l), trust_wp_core::formula::BinOp::Eq, Arc::new(r))
            };
            let deref = |e: PureExpr| PureExpr::Deref(Arc::new(e));
            let final_ = |e: PureExpr| PureExpr::Final(Arc::new(e));
            // G1 current-value split: `*scrut == Cons(*head, *tail)`.
            bridge_facts.push(eq(
                deref(var(scrut)),
                cons(deref(var(head)), deref(var(tail))),
            ));
            // G2 prophecy split: `^scrut == Cons(^head, ^scrut_prime)`. The tail is
            // written as the PRIMED cursor's prophecy `^scrut_prime`
            // (`loop_l_prime_final`) — the exact term the primed invariant `P`
            // quantifies over — NOT `^tail` (`^next`). Using `^scrut_prime` makes
            // the layer-5 unfold recurse as `get(^scrut, i) == ite(.., get(^scrut_prime, i-1))`,
            // so `get(^scrut_prime, i-1)` matches `P(^scrut_prime)`'s trigger
            // SYNTACTICALLY (no reliance on merging the many Box↔List coercion
            // constants of `^next`). SOUND: the next cursor IS the reborrowed tail,
            // so `^scrut == Cons(^head, ^scrut_prime)` is a genuine identity
            // (equivalently `^scrut == Cons(^head, ^tail)` with `^scrut_prime == *(^tail)`).
            bridge_facts.push(eq(
                final_(var(scrut)),
                cons(
                    final_(var(head)),
                    final_(PureExpr::Var(format!("{scrut}_prime"), scrut_sort.clone())),
                ),
            ));
            // G4 prophecy continuity: the loop body reassigns `scrut = tail`, so
            // the NEXT iteration's `scrut` IS `tail`; as &mut references they are
            // the same borrow, hence their prophecies coincide:
            // `^scrut_prime == ^tail`. The primed invariant speaks of
            // `^scrut_prime` (its `P(^scrut_prime)` is the induction hypothesis,
            // really `P(^next)`), while recursive_unfolding's layer-5 unfold speaks
            // of the recursive RHS `get(^tail, i-1)` = `get(^next, i-1)`. Prophecy
            // finals are encoded as INDEPENDENT opaque constants with no
            // Final-congruence, so `^scrut_prime` (e.g. `loop_l_prime#94`) and
            // `^tail` (e.g. `next_final__upgraded#165`) never link and the layer-5
            // recursion step cannot be discharged by the IH — the VC stalls to
            // UNKNOWN. Asserting this identity bridges the two names so E-matching
            // closes the c>0 branch. SOUND: `scrut_prime == tail` holds by the body
            // reassignment and `Final` is a function of the &mut, so both denote
            // one prophecy value — this only ADDS a true equality between two
            // encodings of the same value; it can never turn a genuinely SAT
            // (real-counterexample) obligation UNSAT. (#994 all_zero_list layer-5)
            // The primed cursor's prophecy `^{scrut}_prime` must carry the SAME
            // sort annotation the (primed) invariant uses for `^loop_l`
            // (`Some(MutRef(Datatype(..)))`); with `None` the synthetic prime var's
            // `Final` resolves to a DEAD constant (`{scrut}_prime_final`) instead of
            // the invariant's `{scrut}_prime`, so the linking equality lands on the
            // wrong term and never fires. `next` is a real program var whose `Final`
            // resolves by name, so `None` there is fine.
            // `tail` is `&mut Box<List>`, so `scrut = tail` is a reborrow THROUGH
            // the Box (`scrut = &mut **tail`): the new cursor's prophecy is the
            // List inside the tail's final Box, i.e. `^scrut_prime == *(^tail)` =
            // `Deref(Final(tail))`. This matches the Box-stripped List
            // (`next_final__upgraded`) that `get`/`len` operate on in the layer-5
            // unfold; asserting the un-deref'd `Final(tail)` (a `Box<List>`) links
            // to a different coercion constant and never merges.
            bridge_facts.push(eq(
                final_(PureExpr::Var(format!("{scrut}_prime"), scrut_sort.clone())),
                deref(final_(var(tail))),
            ));
            // G3 head prophecy resolution: the head borrow is written `*head := e`
            // and then dropped at the end of the iteration — it is a LEAF (not
            // reborrowed, reassigned, or double-deref-written), so its prophecy
            // resolves to that final written value: `^head == e`. This is the
            // fact preservation needs for the index-0 element of `^scrut`
            // (`get(^scrut,0) == Some(^head) == Some(e)`). SOUND only for a leaf
            // head: gated on a concrete deref-write with no reassignment / nested
            // write that could transfer or invalidate the prophecy.
            if let Some(final_val) = deref_body_effect.get(head) {
                if !body_effect.contains_key(head) && !double_deref_body_effect.contains_key(head) {
                    bridge_facts.push(eq(final_(var(head)), final_val.clone()));
                }
            }
        }
    }
    let mut post_facts = build_for_loop_completion_facts(&effective_invariants, structural_state);
    // The exit assumptions negate the condition, and the condition's call
    // runs once more at the exit, in the exit state.
    for fact in &condition_facts {
        if !continuation_assumptions.contains(fact) {
            continuation_assumptions.push(fact.clone());
        }
    }
    for fact in &post_facts {
        if !continuation_assumptions.contains(fact) {
            continuation_assumptions.push(fact.clone());
        }
    }
    let final_transfer_facts = build_loop_exit_final_transfer_facts(
        &effective_invariants,
        &effective_ensures,
        &post_loop_deref_final_values,
        structural_state,
    );
    for fact in &final_transfer_facts {
        if !continuation_assumptions.contains(fact) {
            continuation_assumptions.push(fact.clone());
        }
    }
    if verbose && !final_transfer_facts.is_empty() {
        debug!(
            count = final_transfer_facts.len(),
            "synthesized loop-exit final-view transfer facts"
        );
    }

    let mut borrow_vars = Vec::new();
    if structural_state.is_some_and(|st| {
        super::super::iterator_spec_rewrite::helpers::is_logical_fmap_iter(&st.iter_state)
    }) {
        borrow_vars = deref_body_effect
            .keys()
            .filter(|k| !pre_loop_assignments.contains_key(*k))
            .cloned()
            .collect();
        borrow_vars.sort();

        if let Some(state) = structural_state {
            if let Some(iterable) = &state.iterable {
                // Resolve the concrete FMap-value expression being iterated:
                // either a bare `Var` bound in `pre_loop_assignments` to an
                // insert chain, or the insert-chain expression itself (recovered
                // directly from the `into_iter` argument for ghost-block loops).
                let iterable_value = match iterable {
                    PureExpr::Var(name, _) => {
                        pre_loop_assignments.get(name.as_str()).map(|b| &b.value)
                    }
                    other => Some(other),
                };
                // SOUND single-entry gate (cc/fmap layer c): fire the FMap
                // identity bridge ONLY when the iterated map is a PROVABLE
                // singleton — exactly one insert of `(bor_k, bor_v)` into a
                // provably-empty base (`FMap::new()/empty()`). Then the sole
                // yielded entry's key/value references ARE `bor_k`/`bor_v`, so
                // `Final(k2) == Final(bor_k)` is a theorem. For a non-empty or
                // multi-entry map the yielded entry need not be the inserted
                // one, so the bridge would be UNSOUND and must not fire.
                if let Some(iterable_map) = iterable_value {
                    if let Some((insert_key, insert_val)) =
                        single_insert_into_empty_fmap(iterable_map)
                    {
                        let insert_pairs = vec![(insert_key.clone(), insert_val.clone())];
                        let mut pos_map = build_tuple_position_map(&borrow_vars, &body_effect);
                        // Fallback for `for (k2, v2) in fmap` destructuring
                        // where the tuple-get pattern is split between
                        // iterator-next return value handling (outside the
                        // loop body) and the loop's variables (#994 Phase
                        // 3 B3). If body_effect doesn't contain explicit
                        // TupleGet entries for the borrow vars, assume
                        // they map positionally based on borrow_vars order
                        // — k2/v2 stand for the key/value yielded by FMap
                        // iteration.
                        if pos_map.is_empty() && borrow_vars.len() == 2 {
                            pos_map.insert(0, borrow_vars[0].clone());
                            pos_map.insert(1, borrow_vars[1].clone());
                        }
                        let identity_bridge_facts =
                            build_fmap_identity_bridge_facts(&insert_pairs, &pos_map);
                        for fact in &identity_bridge_facts {
                            if !continuation_assumptions.contains(fact) {
                                continuation_assumptions.push(fact.clone());
                            }
                        }
                        bridge_facts.extend(identity_bridge_facts);

                        // Layer (d, revised): &mut-into-backing-local prophecy
                        // resolution via ENSURES REWRITE (not frame havoc).
                        //
                        // The inserted key/value borrows `bor_k = &mut k`,
                        // `bor_v = &mut v` are the only way the loop mutates the
                        // backing locals `k`/`v` (through the yielded element, whose
                        // prophecy the bridge above ties to `bor_k`/`bor_v`). After
                        // the loop the borrows have provably expired (each backing
                        // local is read post-loop), so reading `k` yields `^bor_k`.
                        // Rewrite each backing local to its borrow's final value in
                        // the (already ghost-return-substituted) postcondition, so
                        // the goal reads the RESOLVED value `^bor_k + ^bor_v` rather
                        // than the frozen loop-entry value. SOUND: `k == ^bor_k`
                        // post-loop by borrow expiry (borrow checker); gated on the
                        // provable-singleton condition, and covers BOTH key and value
                        // borrows.
                        //
                        // This is preferable to (a) marking `k`/`v` modified — which
                        // havocs them and spuriously demands re-proving the usize type
                        // invariant `0 <= k'` in PRESERVATION where nothing constrains
                        // the havoced value — and to (b) asserting `k == ^bor_k` as a
                        // postcondition fact, which CONTRADICTS the surviving pre-loop
                        // frame `k == 0` once cardinality forces `^bor_k == 1`, giving
                        // a vacuous proof. The rewrite leaves the frame `k == 0`
                        // harmlessly out of the (rewritten) goal.
                        // Rewrite each backing local `k` to its borrow's final value
                        // `^bor_k` in BOTH the loop-slice ensures and the function-level
                        // return expression, so every postcondition goal reads the
                        // RESOLVED value `^bor_k + ^bor_v` rather than the frozen
                        // loop-entry value. The surviving pre-loop frame `k == 0` is then
                        // harmlessly absent from the (rewritten) goal — no contradiction,
                        // no vacuous proof. SOUND: reading `k` after the loop yields
                        // `^bor_k` because the borrow has provably expired (borrow
                        // checker); gated on the provable-singleton condition, covering
                        // BOTH the key and value borrows.
                        let mut backing_subst: std::collections::HashMap<String, PureExpr> =
                            std::collections::HashMap::new();
                        for borrow_name in [&insert_key, &insert_val] {
                            let Some(backing) = borrow_backing_names.get(borrow_name.as_str())
                            else {
                                continue;
                            };
                            backing_subst.insert(
                                backing.clone(),
                                PureExpr::Final(Arc::new(PureExpr::Var(borrow_name.clone(), None))),
                            );

                            // Snapshot-final bridge for the COMPOSITIONAL function path:
                            // the user invariant `^snap == 1` encodes its final via the
                            // SNAPSHOT variable (`snap_final`), while the rewritten goal
                            // reads `^bor` (`bor_final`). `let snap = snapshot!{ bor }`
                            // makes `snap` an alias of `bor`, so `^snap == ^bor` — assert
                            // it (in the same `Final(Var(..))` form both consts use) so
                            // the invariant's conclusion (`^snap == 1`) reaches the goal's
                            // `^bor`. SOUND: a snapshot of a `&mut` shares its prophecy.
                            for (snap_name, binding) in &pre_loop_assignments {
                                if matches!(&binding.value, PureExpr::Var(v, _) if v == borrow_name)
                                {
                                    let snap_eq = PureExpr::BinOp(
                                        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                                            snap_name.clone(),
                                            None,
                                        )))),
                                        trust_wp_core::formula::BinOp::Eq,
                                        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                                            borrow_name.clone(),
                                            None,
                                        )))),
                                    );
                                    if !continuation_assumptions.contains(&snap_eq) {
                                        continuation_assumptions.push(snap_eq);
                                    }
                                }
                            }
                        }
                        if !backing_subst.is_empty() {
                            effective_ensures = effective_ensures
                                .iter()
                                .map(|ens| ens.substitute(&backing_subst))
                                .collect();
                            return_expr = return_expr.map(|r| r.substitute(&backing_subst));
                        }

                        // Singleton cardinality for the loop POSTCONDITION: the
                        // iterated map has exactly one entry, so the exhausted-iterator
                        // completion fact `View(produced).len() == View(iterable).len()`
                        // pins `produced.len() == 1`, discharging the invariant
                        // `produced.len() == 0 || (^snap_k == 1 && ^snap_v == 1)`.
                        // SOUND: `View(iterable).len() == 1` because `iterable` is a
                        // single insert of a fresh key into the provably-empty map
                        // (same gate). z3 cross-checked with the exit VC.
                        let iterable_len_one = PureExpr::BinOp(
                            Arc::new(PureExpr::MethodCall {
                                receiver: Arc::new(PureExpr::View(Arc::new(iterable_map.clone()))),
                                method: "len".to_string(),
                                args: vec![],
                            }),
                            trust_wp_core::formula::BinOp::Eq,
                            Arc::new(PureExpr::Int(1)),
                        );
                        if !post_facts.contains(&iterable_len_one) {
                            post_facts.push(iterable_len_one.clone());
                        }
                        if !continuation_assumptions.contains(&iterable_len_one) {
                            continuation_assumptions.push(iterable_len_one);
                        }
                    }
                }
            }
        }
    }

    let modified_vars_refs: Vec<&str> = modified_vars.iter().map(String::as_str).collect();

    if std::env::var_os("TRUST_WP_LOOP_EFFECT_DUMP").is_some() {
        let def_path = req.def_path;
        eprintln!(
            "TRUST_WP_LOOP_EFFECT_DUMP def_path={def_path} loop={loop_idx} \
             invariants={effective_invariants:?} condition={loop_condition:?} \
             transition_facts={transition_facts:?} init_facts={init_facts:?}"
        );
    }

    let mut config = encoder_config_from_req(req)
        .with_transition_facts(&transition_facts)
        .with_bridge_facts(&bridge_facts)
        .with_condition_facts(&condition_facts)
        .with_stated_invariants(stated_invariant_count);
    if !borrow_vars.is_empty() {
        config = config.with_loop_element_borrow_vars(borrow_vars);
    }
    let mut loop_ctx = LoopVerificationContext::new(
        &effective_requires,
        &effective_ensures,
        &effective_invariants,
        &modified_vars_refs,
        BodyEffects::new(&body_effect, &deref_body_effect, &double_deref_body_effect),
        &pre_loop_assignments,
    )
    .with_init_extra_facts(&init_facts)
    .with_post_extra_facts(&post_facts)
    .with_postcondition_effects(BodyEffects::new(
        &body_effect,
        &filtered_postcondition_deref,
        &double_deref_body_effect,
    ))
    .with_config(config);
    if let Some(ref cond) = loop_condition {
        loop_ctx = loop_ctx.with_loop_condition(cond);
    }
    if condition_is_body_break {
        loop_ctx = loop_ctx.with_body_break();
    }
    if let Some(var) = variant.as_ref() {
        loop_ctx = loop_ctx.with_variant(var);
    }
    if let Some(ref ret) = return_expr {
        loop_ctx = loop_ctx.with_return_expr(ret);
    }
    let mut loop_outcome = verify_loop_invariant_outcome(&loop_ctx)?;
    // prophecy-store: the initialization VC binds every name to its
    // function-entry value (`*bor` = `bor_current`). A store through a
    // reference before loop entry (`*bor = 5`, `let r = &mut v; *r = 5`) is
    // not reflected there, so an invariant that reads such a name at entry
    // would be credited against a stale value. Fail closed. `^x` and
    // `old(..)` subterms are unaffected by a store and do not count. Whether
    // a model of such a VC is a run of the program is `PreLoopStoreLinks`'s
    // question, below.
    if matches!(
        loop_outcome.initialization.result,
        trust_wp_ay::VerificationResult::Verified(_)
    ) && invariant_reads_pre_loop_store_at_entry(
        effective_invariants.iter(),
        &pre_loop_deref_stored_names,
    ) {
        if verbose {
            debug!(
                names = ?pre_loop_deref_stored_names,
                "loop initialization reads a value stored through a reference before loop entry; failing closed"
            );
        }
        loop_outcome.initialization = trust_wp_ay::VerificationOutcome::without_provenance(
            trust_wp_ay::VerificationResult::Unknown(trust_wp_ay::UnknownReason::Unsupported),
        );
    }
    let stale_store = PreLoopStoreLinks::new(
        &pre_loop_deref_stored_names,
        effective_requires
            .iter()
            .chain(&effective_invariants)
            .chain(loop_condition.as_ref())
            .chain(variant.as_ref())
            .chain(&transition_facts)
            .chain(&bridge_facts)
            .chain(&condition_facts)
            .chain(&init_facts)
            .chain(&post_facts),
        [
            &body_effect,
            &deref_body_effect,
            &double_deref_body_effect,
            &filtered_postcondition_deref,
        ]
        .into_iter()
        .flatten()
        .chain(
            pre_loop_assignments
                .iter()
                .map(|(name, binding)| (name, &binding.value)),
        ),
    );
    // A model of a one-iteration VC is a counterexample only if it satisfies
    // every premise the iteration supplies. A premise the VC left out can rule
    // the model out, so the refutation is withheld rather than reported as a
    // run of the program (loop_body_call_postcondition_premise_control).
    let mut iteration_goals: Vec<&PureExpr> = effective_invariants
        .iter()
        .take(stated_invariant_count)
        .collect();
    iteration_goals.extend(variant.as_ref());
    if condition_is_body_break {
        iteration_goals.extend(loop_condition.as_ref());
    }
    if let Some(reason) = unstated_iteration_premise(
        &dropped_premises,
        &iteration_goals,
        &modified_vars,
        &changed_places,
        [&body_effect, &deref_body_effect, &double_deref_body_effect],
    ) {
        withhold_refutation(&mut loop_outcome.preservation, &reason);
        if let Some(decrease) = loop_outcome.variant_decrease.as_mut() {
            withhold_refutation(decrease, &reason);
        }
        if condition_is_body_break {
            // The exit test reads the post-iteration state.
            withhold_refutation(&mut loop_outcome.postcondition, &reason);
        }
    }
    if let Some(reason) = stale_store.reason(iteration_goals.iter().copied()) {
        withhold_refutation(&mut loop_outcome.preservation, &reason);
        for variant_check in [
            loop_outcome.variant_nonneg.as_mut(),
            loop_outcome.variant_decrease.as_mut(),
        ]
        .into_iter()
        .flatten()
        {
            withhold_refutation(variant_check, &reason);
        }
        if condition_is_body_break {
            withhold_refutation(&mut loop_outcome.postcondition, &reason);
        }
    }
    // Every VC but initialization assumes the loop condition or its
    // negation; when that reads a call result no premise constrains, a model
    // picks it freely (loop_condition_call_unstated_control).
    if let Some(what) = condition_unstated.as_deref() {
        let reason = format!("the loop condition reads a value the loop VC does not state: {what}");
        withhold_refutation(&mut loop_outcome.preservation, &reason);
        if let Some(decrease) = loop_outcome.variant_decrease.as_mut() {
            withhold_refutation(decrease, &reason);
        }
        withhold_refutation(&mut loop_outcome.postcondition, &reason);
    }
    // The initialization VC reads every variable at loop entry, and a model
    // of it is a counterexample only if each value it picks is one the
    // program can hold there.
    let stated_goals: Vec<&PureExpr> = effective_invariants
        .iter()
        .take(stated_invariant_count)
        .collect();
    let entry = EntryPremises {
        pre_loop_assignments: &pre_loop_assignments,
        init_facts: &init_facts,
        arg_names: &parsed.arg_names,
        pre_loop_written_params: &pre_loop_written_params,
        written_by_earlier_loops: &written_by_earlier_loops,
    };
    if let Some(name) = entry.first_unbound(&stated_goals, |_| true) {
        let reason = format!("the loop VC does not determine `{name}` at loop entry");
        withhold_refutation(&mut loop_outcome.initialization, &reason);
    }
    if let Some(reason) = stale_store.reason(stated_goals.iter().copied()) {
        withhold_refutation(&mut loop_outcome.initialization, &reason);
    }
    // The exit VC reads the state the loop leaves through its goals and the
    // invariants and negated condition it assumes.
    if !condition_is_body_break {
        // `result` is the return expression's value, not a variable of the
        // exit state.
        let ensures_read: Vec<PureExpr> = effective_ensures
            .iter()
            .map(|ensure| match return_expr.as_ref() {
                Some(ret) => ensure.substitute(&std::collections::HashMap::from([(
                    "result".to_string(),
                    ret.clone(),
                )])),
                None => ensure.clone(),
            })
            .collect();
        let mut exit_reads: Vec<&PureExpr> = stated_goals.clone();
        exit_reads.extend(ensures_read.iter());
        exit_reads.extend(loop_condition.as_ref());
        if let Some(reason) = unstated_exit_premise(
            &exit_reads,
            &modified_vars,
            &changed_places,
            [&body_effect, &deref_body_effect, &double_deref_body_effect],
            &entry,
        ) {
            withhold_refutation(&mut loop_outcome.postcondition, &reason);
        }
        // A name the loop does not write keeps its entry value there, and a
        // final value `^p` is read at the pointee the loop leaves
        // (loop_postcondition_after_param_store_control).
        if let Some(reason) = stale_store.reason(exit_reads.iter().copied()) {
            withhold_refutation(&mut loop_outcome.postcondition, &reason);
        }
    }
    emit_loop_verification_diagnostics(req.def_path, &loop_outcome);
    let evidence_gap_reasons = loop_verification_evidence_gap_reasons(&loop_outcome);
    let loop_result = loop_outcome.as_result();

    if verbose {
        let status = |result: &trust_wp_ay::VerificationResult| match result {
            trust_wp_ay::VerificationResult::Verified(_)
            | trust_wp_ay::VerificationResult::Assumed(_) => "ok",
            trust_wp_ay::VerificationResult::Failed(_) => "FAIL",
            trust_wp_ay::VerificationResult::Unknown(_) => "unknown",
            _ => "error",
        };
        debug!(
            loop_idx,
            init = status(&loop_result.initialization),
            preservation = status(&loop_result.preservation),
            postcondition = status(&loop_result.postcondition),
            "loop result"
        );
    }

    let continuation_assumptions =
        filter_post_loop_stale_deref_assumptions(continuation_assumptions, &post_loop_deref_writes);

    Ok(SingleLoopResult {
        result: loop_result,
        frame_contributions,
        continuation_assumptions,
        return_expr,
        post_loop_final_values: post_loop_deref_final_values,
        effective_invariants,
        evidence_gap_reasons,
    })
}

/// Why a one-iteration refutation over this loop body is not a statement
/// about the program, if it is not.
///
/// Two ways: the body walk left out a premise some path supplies (a
/// postcondition it could not state, a walk that did not finish), which may
/// constrain any value; or a variable a goal reads after the iteration has a
/// changed part the VC gives no value, or only one naming a placeholder, so the
/// model picks it freely although the program determines it.
fn unstated_iteration_premise(
    dropped_premises: &[crate::mir_analysis::DroppedPremise],
    goals: &[&PureExpr],
    modified_vars: &[String],
    changed_places: &ChangedPlaces,
    [direct, deref, double_deref]: [&std::collections::HashMap<String, PureExpr>; 3],
) -> Option<String> {
    if let Some(premise) = dropped_premises
        .iter()
        .find(|premise| premise.only_about.is_none())
    {
        return Some(format!("the loop VC does not state {}", premise.what));
    }
    let mut read: std::collections::HashSet<String> = std::collections::HashSet::new();
    for goal in goals {
        read.extend(expr_referenced_vars(goal));
    }
    let mut about_read: Vec<&crate::mir_analysis::DroppedPremise> = dropped_premises
        .iter()
        .filter(|premise| {
            premise
                .only_about
                .as_ref()
                .is_some_and(|name| read.contains(name))
        })
        .collect();
    about_read.sort_by(|a, b| a.only_about.cmp(&b.only_about));
    if let Some(premise) = about_read.first() {
        return Some(format!("the loop VC does not state {}", premise.what));
    }
    undetermined_after_iteration(
        &read,
        modified_vars,
        changed_places,
        [direct, deref, double_deref],
    )
    .map(|name| format!("the loop VC does not determine `{name}` after an iteration"))
}

/// The first variable of `read` the body writes to (by the modified-variable
/// scan) whose new value the walk does not determine: no effect for the part
/// that changes, or one naming a placeholder.
fn undetermined_after_iteration<'a>(
    read: &std::collections::HashSet<String>,
    modified_vars: &'a [String],
    changed_places: &ChangedPlaces,
    [direct, deref, double_deref]: [&std::collections::HashMap<String, PureExpr>; 3],
) -> Option<&'a String> {
    let determined = |map: &std::collections::HashMap<String, PureExpr>, name: &str| {
        map.get(name)
            .is_some_and(|value| !names_a_placeholder(value))
    };
    let mut undetermined: Vec<&String> = modified_vars
        .iter()
        .filter(|name| read.contains(name.as_str()))
        .filter(|name| {
            let direct = determined(direct, name);
            let through_ref = determined(deref, name) || determined(double_deref, name);
            match changed_places.0.get(name.as_str()) {
                Some(ChangedPlacesTree::Deref(_)) => !through_ref,
                Some(_) => !direct,
                None => !direct && !through_ref,
            }
        })
        .collect();
    undetermined.sort();
    undetermined.first().copied()
}

/// Why a refutation of the loop's exit VC is not a statement about the
/// program, if it is not.
///
/// The exit VC reads the state the loop leaves: a variable the loop writes
/// holds whatever the invariant and the negated condition allow, and one it
/// does not write keeps its entry value. A variable the scan counts as
/// written but whose change the walk never determines may keep its entry
/// value, a frame the VC does not state (cc/fmap's `snap_k`, a snapshot the
/// body never assigns); a variable the loop does not write whose entry value
/// the VC leaves free is picked by the model.
fn unstated_exit_premise(
    goals: &[&PureExpr],
    modified_vars: &[String],
    changed_places: &ChangedPlaces,
    effects: [&std::collections::HashMap<String, PureExpr>; 3],
    entry: &EntryPremises<'_>,
) -> Option<String> {
    let mut read: std::collections::HashSet<String> = std::collections::HashSet::new();
    for goal in goals {
        read.extend(expr_referenced_vars(goal));
    }
    if let Some(name) = undetermined_after_iteration(&read, modified_vars, changed_places, effects)
    {
        return Some(format!(
            "the loop VC does not determine `{name}` after the loop"
        ));
    }
    let written: std::collections::HashSet<&str> =
        modified_vars.iter().map(String::as_str).collect();
    entry
        .first_unbound(goals, |name| !written.contains(name))
        .map(|name| format!("the loop VC does not determine `{name}`, which the loop keeps"))
}

/// What the initialization VC states about each variable's value at loop
/// entry.
struct EntryPremises<'a> {
    pre_loop_assignments:
        &'a std::collections::HashMap<String, trust_wp_core::formula::NamedBindingValue>,
    init_facts: &'a [PureExpr],
    arg_names: &'a [String],
    pre_loop_written_params: &'a std::collections::HashSet<String>,
    written_by_earlier_loops: &'a std::collections::HashSet<String>,
}

impl EntryPremises<'_> {
    /// The first variable the goals read, among those `consider` admits, whose
    /// entry value the VC leaves free although the program determines it.
    ///
    /// A pre-loop binding or an initialization fact describes a variable; a
    /// parameter no code before the loop writes is free exactly as the
    /// function's caller leaves it. Anything else — a value an earlier loop
    /// left (bug/164's second loop reads the `x` its first loop's `break`
    /// set), a variable of an enclosing loop, a pre-loop value that did not
    /// translate — is picked freely by the model. A binding or fact whose value
    /// is a stand-in nothing constrains (merge_fmaps' `snapshot!` of a
    /// closure-taking call) describes nothing.
    fn first_unbound(
        &self,
        goals: &[&PureExpr],
        consider: impl Fn(&str) -> bool,
    ) -> Option<String> {
        let mut read: Vec<String> = goals
            .iter()
            .flat_map(|goal| expr_referenced_vars(goal))
            .filter(|name| consider(name))
            .collect();
        read.sort();
        read.dedup();
        let described_by_facts = |name: &str| {
            self.init_facts.iter().any(|fact| {
                expr_referenced_vars(fact).contains(name)
                    && !self.names_unconstrained_stand_in(fact, Some(fact))
            })
        };
        read.into_iter().find(|name| {
            if let Some(binding) = self.pre_loop_assignments.get(name) {
                if !self.names_unconstrained_stand_in(&binding.value, None) {
                    return false;
                }
                return !described_by_facts(name);
            }
            if self.written_by_earlier_loops.contains(name) {
                return true;
            }
            let untouched_parameter =
                self.arg_names.contains(name) && !self.pre_loop_written_params.contains(name);
            !untouched_parameter && !described_by_facts(name)
        })
    }

    /// Whether `expr` names a stand-in no initialization fact constrains: a
    /// value that did not translate, or a call result no fact but `expr`
    /// itself mentions.
    fn names_unconstrained_stand_in(&self, expr: &PureExpr, itself: Option<&PureExpr>) -> bool {
        let mut stand_ins: Vec<String> = Vec::new();
        expr.for_each_recursive(|node| {
            if let PureExpr::Var(name, _) = node {
                if names_a_placeholder(node) {
                    stand_ins.push(name.clone());
                }
            }
        });
        stand_ins.iter().any(|name| {
            if !name.starts_with("$_") {
                return true;
            }
            !self.init_facts.iter().any(|fact| {
                !itself.is_some_and(|itself| std::ptr::eq(itself, fact))
                    && expr_referenced_vars(fact).contains(name.as_str())
            })
        })
    }
}

/// Whether an effect value names a stand-in for a value the walk could not
/// translate, which leaves the variable it describes free in the VC.
fn names_a_placeholder(value: &PureExpr) -> bool {
    let mut found = false;
    value.for_each_recursive(|node| {
        if let PureExpr::Var(name, _) = node {
            if name == trust_wp_core::formula::INDEX_MUT_OPAQUE_VALUE
                || name.starts_with("$_")
                || crate::mir_analysis::is_fallback_arg_placeholder(name)
            {
                found = true;
            }
        }
    });
    found
}

/// Whether any of `exprs` reads, at loop entry, a name a store through a
/// reference before the loop may have changed (`pre_loop_deref_stored_names`).
/// An `old(..)` subterm reads the function-entry value, and a final value `^p`
/// is a prophecy; no store decides either.
fn invariant_reads_pre_loop_store_at_entry<'a>(
    exprs: impl IntoIterator<Item = &'a PureExpr>,
    stored: &std::collections::HashSet<String>,
) -> bool {
    !stored.is_empty()
        && exprs.into_iter().any(|expr| {
            expr.rewrite_bottom_up(|e| match e {
                PureExpr::Old(_) | PureExpr::Final(_) => PureExpr::Bool(true),
                other => other,
            })
            .any_free_var(|name, _| stored.contains(name))
        })
}

/// Replace a refutation with the withheld verdict naming `reason`.
fn withhold_refutation(outcome: &mut trust_wp_ay::VerificationOutcome, reason: &str) {
    if matches!(outcome.result, trust_wp_ay::VerificationResult::Failed(_)) {
        *outcome = trust_wp_ay::VerificationOutcome::without_provenance(
            trust_wp_ay::VerificationResult::Unknown(trust_wp_ay::UnknownReason::SolverMessage(
                format!("{}: {reason}", trust_wp_ay::REFUTATION_AUTHORITY_MESSAGE),
            )),
        );
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    use super::{
        build_loop_exit_final_transfer_facts, eq_expr, final_expr, implies_expr,
        inherit_outer_invariant, len_expr, lt_expr, method_call, nested_loop_exit_transition_facts,
        view_expr, zero, BinOp, ExprSort, PureExpr,
    };
    use crate::mir_analysis::{ForLoopGhostState, LoopAnalysis, LoopInfo};

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn var_sort(name: &str, sort: ExprSort) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(sort))
    }

    #[test]
    fn duplicate_inner_invariant_still_inherits_outer_require() {
        let shared_invariant = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("door_open".to_string(), None)),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(100)),
        );
        let mut effective_requires = Vec::new();
        let mut effective_invariants = vec![shared_invariant.clone()];
        let modified_vars = vec!["door_open".to_string()];

        let added = inherit_outer_invariant(
            &mut effective_requires,
            &mut effective_invariants,
            &shared_invariant,
            &modified_vars,
        );

        assert_eq!(
            added, 1,
            "outer duplicate invariant should still contribute an initialization require"
        );
        assert_eq!(
            effective_requires,
            vec![shared_invariant.clone()],
            "duplicate inner invariant must not block outer require inheritance"
        );
        assert_eq!(
            effective_invariants,
            vec![shared_invariant],
            "unstable outer invariant should not be duplicated into invariants"
        );
    }

    #[test]
    fn loop_exit_final_transfer_replays_produced_prefix_invariant() {
        let produced_len = len_expr(var_sort("produced", ExprSort::Seq));
        let j = var_sort("j", ExprSort::Int);
        let v = var("v");
        let invariant = PureExpr::Forall {
            var: "j".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(implies_expr(
                PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(zero()),
                        BinOp::Le,
                        Arc::new(j.clone()),
                    )),
                    BinOp::And,
                    Arc::new(lt_expr(j.clone(), produced_len)),
                ),
                eq_expr(
                    method_call(v.clone(), "index_logic", vec![j.clone()]),
                    zero(),
                ),
            )),
            triggers: vec![],
        };

        let final_v = final_expr(v.clone());
        let i = var("i");
        let ensure = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(implies_expr(
                PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(zero()),
                        BinOp::Le,
                        Arc::new(i.clone()),
                    )),
                    BinOp::And,
                    Arc::new(lt_expr(i.clone(), len_expr(view_expr(final_v.clone())))),
                ),
                eq_expr(method_call(final_v, "index_logic", vec![i]), zero()),
            )),
            triggers: vec![],
        };

        let state = ForLoopGhostState {
            produced_name: "produced".to_string(),
            iter_old: var("__old"),
            iter_state: var("__state"),
            iter_state_binding: var("iter"),
            iter_state_next: var("__next"),
            loop_elem: var("i"),
            iterable: None,
            range_bounds: None,
        };
        let final_values = HashMap::from([("v".to_string(), PureExpr::Deref(Arc::new(var("v"))))]);

        let facts = build_loop_exit_final_transfer_facts(
            &[invariant],
            &[ensure],
            &final_values,
            Some(&state),
        );

        assert_eq!(facts.len(), 3);
        assert_eq!(
            facts[0],
            eq_expr(view_expr(final_expr(var("v"))), view_expr(var("v")))
        );
        assert_eq!(
            facts[1],
            eq_expr(
                len_expr(view_expr(var("v"))),
                len_expr(view_expr(final_expr(var("v"))))
            )
        );
        assert!(
            matches!(
                &facts[2],
                PureExpr::Forall { triggers, .. }
                    if triggers.len() == 1
                        && matches!(
                            triggers[0].first(),
                            Some(PureExpr::MethodCall { method, .. }) if method == "index_logic"
                        )
            ),
            "transfer fact should be a triggered final index universal: {:?}",
            facts[2]
        );
    }

    #[test]
    fn outer_loop_transition_inherits_nested_loop_exit_facts() {
        let outer_header = rustc_middle::mir::BasicBlock::from_u32(1);
        let inner_header = rustc_middle::mir::BasicBlock::from_u32(2);
        let outer_body = HashSet::from([outer_header, inner_header]);
        let inner_body = HashSet::from([inner_header]);
        let analysis = LoopAnalysis {
            loops: vec![
                LoopInfo {
                    header: outer_header,
                    body_blocks: outer_body,
                },
                LoopInfo {
                    header: inner_header,
                    body_blocks: inner_body,
                },
            ],
            has_loops: true,
        };
        let inner_invariant = eq_expr(var("moved"), var("current_bucket"));
        let inner_condition = var_sort("l_is_cons", ExprSort::Bool);
        let per_loop_effective_invariants =
            vec![vec![var("outer_inv")], vec![inner_invariant.clone()]];
        let per_loop_conditions = vec![Some(var("outer_cond")), Some(inner_condition.clone())];
        let facts = nested_loop_exit_transition_facts(
            &analysis,
            0,
            &per_loop_effective_invariants,
            &per_loop_conditions,
            None,
        );

        assert_eq!(facts.len(), 2);
        assert!(facts.contains(&inner_invariant));
        assert!(facts.contains(&PureExpr::UnOp(
            trust_wp_core::formula::UnOp::Not,
            Arc::new(inner_condition)
        )));
        assert!(
            nested_loop_exit_transition_facts(
                &analysis,
                1,
                &per_loop_effective_invariants,
                &per_loop_conditions,
                None
            )
            .is_empty(),
            "inner loop should not inherit enclosing-loop exit facts as transition facts"
        );
    }

    mod unstated_premises {
        use std::collections::{HashMap, HashSet};

        use trust_wp_core::formula::NamedBindingValue;

        use super::{
            super::{
                invariant_reads_pre_loop_store_at_entry, unstated_exit_premise, ChangedPlaces,
                EntryPremises,
            },
            eq_expr, var, PureExpr,
        };

        fn binding(value: PureExpr) -> NamedBindingValue {
            NamedBindingValue { sort: None, value }
        }

        fn first_unbound(
            goal: &PureExpr,
            assignments: &HashMap<String, NamedBindingValue>,
            facts: &[PureExpr],
        ) -> Option<String> {
            let none = HashSet::new();
            let entry = EntryPremises {
                pre_loop_assignments: assignments,
                init_facts: facts,
                arg_names: &[],
                pre_loop_written_params: &none,
                written_by_earlier_loops: &none,
            };
            entry.first_unbound(&[goal], |_| true)
        }

        /// merge_fmaps: `merge` is bound to a value that did not translate,
        /// and the one fact about it equates it with a call result nothing
        /// else describes, so the model picks it.
        #[test]
        fn a_binding_to_an_unconstrained_stand_in_binds_nothing() {
            let assignments =
                HashMap::from([("merge".to_string(), binding(var("$fallback_arg0_6")))]);
            let facts = [eq_expr(var("merge"), var("$_call_11"))];
            assert_eq!(
                first_unbound(
                    &eq_expr(var("merge"), PureExpr::Int(5)),
                    &assignments,
                    &facts
                )
                .as_deref(),
                Some("merge")
            );
        }

        #[test]
        fn a_call_result_another_fact_describes_binds() {
            let assignments = HashMap::from([("x".to_string(), binding(var("$_call_7")))]);
            let facts = [eq_expr(var("$_call_7"), PureExpr::Int(0))];
            assert_eq!(
                first_unbound(&eq_expr(var("x"), PureExpr::Int(0)), &assignments, &facts),
                None
            );
            let lone: [PureExpr; 0] = [];
            assert_eq!(
                first_unbound(&eq_expr(var("x"), PureExpr::Int(0)), &assignments, &lone).as_deref(),
                Some("x")
            );
        }

        /// cc/fmap: the scan counts `snap` as written, the walk records no
        /// write, so the exit VC may have dropped its frame.
        #[test]
        fn an_exit_read_of_a_variable_the_walk_never_writes_is_unstated() {
            let none_set = HashSet::new();
            let no_assignments = HashMap::new();
            let entry = EntryPremises {
                pre_loop_assignments: &no_assignments,
                init_facts: &[],
                arg_names: &[],
                pre_loop_written_params: &none_set,
                written_by_earlier_loops: &none_set,
            };
            let modified = vec!["i".to_string(), "snap".to_string()];
            let direct = HashMap::from([(
                "i".to_string(),
                PureExpr::BinOp(
                    std::sync::Arc::new(var("i")),
                    super::BinOp::Add,
                    std::sync::Arc::new(PureExpr::Int(1)),
                ),
            )]);
            let empty = HashMap::new();
            let effects = [&direct, &empty, &empty];
            let reads_i = eq_expr(var("i"), PureExpr::Int(10));
            assert_eq!(
                unstated_exit_premise(
                    &[&reads_i],
                    &modified,
                    &ChangedPlaces::default(),
                    effects,
                    &entry
                ),
                None,
                "a written variable the walk determines is the invariant's to constrain"
            );
            let reads_snap = eq_expr(var("snap"), PureExpr::Int(1));
            assert!(unstated_exit_premise(
                &[&reads_snap],
                &modified,
                &ChangedPlaces::default(),
                effects,
                &entry
            )
            .is_some_and(|reason| reason.contains("`snap`")));
        }

        #[test]
        fn an_exit_read_of_a_kept_variable_needs_its_entry_value() {
            let none_set = HashSet::new();
            let assignments = HashMap::from([("k".to_string(), binding(var("$fallback_arg0_1")))]);
            let entry = EntryPremises {
                pre_loop_assignments: &assignments,
                init_facts: &[],
                arg_names: &["n".to_string()],
                pre_loop_written_params: &none_set,
                written_by_earlier_loops: &none_set,
            };
            let empty = HashMap::new();
            let effects = [&empty, &empty, &empty];
            let reads_n = eq_expr(var("n"), PureExpr::Int(1));
            assert_eq!(
                unstated_exit_premise(&[&reads_n], &[], &ChangedPlaces::default(), effects, &entry),
                None,
                "an untouched parameter is free exactly as the caller leaves it"
            );
            let reads_k = eq_expr(var("k"), PureExpr::Int(1));
            assert!(unstated_exit_premise(
                &[&reads_k],
                &[],
                &ChangedPlaces::default(),
                effects,
                &entry
            )
            .is_some_and(|reason| reason.contains("`k`")));
        }

        /// An invariant read at loop entry through the pointee sees the stale
        /// value; `old(..)` and a prophecy `^p` do not
        /// (loop_invariant_entry_after_param_store_false).
        #[test]
        fn an_entry_read_of_a_stored_pointee_is_stale_and_old_and_prophecy_are_not() {
            let stored = HashSet::from(["a".to_string()]);
            let pointee = PureExpr::Deref(std::sync::Arc::new(var("a")));
            let prophecy = PureExpr::Final(std::sync::Arc::new(var("a")));
            let entry_value = PureExpr::Old(std::sync::Arc::new(pointee.clone()));
            assert!(invariant_reads_pre_loop_store_at_entry([&pointee], &stored));
            assert!(!invariant_reads_pre_loop_store_at_entry(
                [&prophecy],
                &stored
            ));
            assert!(!invariant_reads_pre_loop_store_at_entry(
                [&entry_value],
                &stored
            ));
            assert!(!invariant_reads_pre_loop_store_at_entry(
                [&var("b")],
                &stored
            ));
            assert!(!invariant_reads_pre_loop_store_at_entry(
                [&pointee],
                &HashSet::new()
            ));
        }
    }
}
