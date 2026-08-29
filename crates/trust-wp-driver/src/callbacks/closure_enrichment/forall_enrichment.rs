// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Forall goal enrichment with closure ensures.
//!
//! Replaces universally-quantified `postcondition_mut => precondition` goal
//! obligations with ground instantiations using the closure's concrete
//! requires/ensures clauses.

use std::{collections::HashMap, sync::Arc};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::formula::{BinOp, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    closure_receiver_base_name, collect_closure_receiver_bindings,
    substitute::substitute_captures_inline, substitute_closure_params_with_args, ClosureSpec,
};
use crate::mir_analysis::resolve_arg_names_or_warn;

/// Replace Forall postcondition_mut obligation goals with ground instantiations
/// using the concrete closure's requires clauses (#970).
///
/// Goals like `Forall st, r: postcondition_mut(RECV, args, st, r) ==> precondition(st, args)`
/// cannot be proved by ay-dpll (quantifier handling limitation). Instead, replace
/// them with the ground obligation: the closure's requires clause where captures
/// are substituted with ensures-derived post-state expressions.
///
/// For a closure with `#[requires(x@ < 1_000_000)]` and `#[ensures(x@ == old(x)@ + 1)]`:
/// The Forall becomes the ground check: `view(tuple_get_0(RECV)) + 1 < 1000000`.
#[allow(clippy::ptr_arg)] // needs Vec for remove/extend
pub(in crate::callbacks) fn enrich_forall_goals_with_closure_ensures(
    tcx: TyCtxt<'_>,
    parent_local_def_id: LocalDefId,
    user_specs: &HashMap<DefId, StdSpec>,
    goals: &mut Vec<PureExpr>,
) -> usize {
    // Build both requires (precondition) and ensures (postcondition) for each closure
    let mut closure_specs: Vec<ClosureSpec> = Vec::new();
    for binding in collect_closure_receiver_bindings(parent_local_def_id) {
        let spec = match user_specs.get(&binding.def_id) {
            Some(s) if !s.ensures.is_empty() && !s.requires.is_empty() => s,
            _ => continue,
        };
        let Some(closure_local_def_id) = binding.def_id.as_local() else {
            continue;
        };
        let captures = tcx.closure_captures(closure_local_def_id);
        if captures.is_empty() {
            continue;
        }
        let capture_bindings: Vec<(usize, String)> = captures
            .iter()
            .enumerate()
            .map(|(idx, cap)| (idx, cap.var_ident.as_str().to_string()))
            .collect();
        let param_names = resolve_arg_names_or_warn(tcx, binding.def_id, spec.param_names.as_ref());

        let mut requires_exprs = Vec::new();
        for requires_str in &spec.requires {
            if let Ok(req_expr) = trust_wp_core::contract_parser::parse_contract(requires_str) {
                requires_exprs.push(req_expr);
            }
        }
        let mut ensures_exprs = Vec::new();
        for ensures_str in &spec.ensures {
            if let Ok(ensures_expr) = trust_wp_core::contract_parser::parse_contract(ensures_str) {
                ensures_exprs.push(ensures_expr);
            }
        }
        if !requires_exprs.is_empty() && !ensures_exprs.is_empty() {
            closure_specs.push(ClosureSpec {
                receiver_name: binding.receiver_name,
                param_names,
                capture_bindings,
                requires_exprs,
                ensures_exprs,
            });
        }
    }

    if closure_specs.is_empty() {
        return 0;
    }

    let mut enrichment_count = 0;
    let mut new_goals = Vec::new();
    let mut to_remove = Vec::new();
    for (idx, goal) in goals.iter().enumerate() {
        if let Some(ground) = try_ground_forall_obligation(goal, &closure_specs) {
            new_goals.push(ground);
            to_remove.push(idx);
            enrichment_count += 1;
        }
    }

    // Replace Forall goals with ground versions (reverse order to preserve indices)
    for idx in to_remove.into_iter().rev() {
        goals.remove(idx);
    }
    goals.extend(new_goals);

    enrichment_count
}

/// Unwrap nested Forall quantifiers to find the innermost body.
fn unwrap_foralls(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Forall { body, .. } => unwrap_foralls(body),
        other => other,
    }
}

/// Find a postcondition_mut method call in an expression.
/// Returns (receiver, args_expr, post_state_expr, result_expr) if found.
fn find_postcondition_mut_in_expr(
    expr: &PureExpr,
) -> Option<(&PureExpr, &PureExpr, &PureExpr, &PureExpr)> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "postcondition_mut" && args.len() == 3 => {
            Some((receiver.as_ref(), &args[0], &args[1], &args[2]))
        }
        _ => None,
    }
}

/// Try to convert a Forall postcondition_mut obligation into a ground goal.
///
/// For `Forall st, r: postcondition_mut(RECV, ARGS, st, r) ==> precondition(st, ARGS)`:
/// Replace with `ensures(pre=RECV, post=S) ==> requires(post=S)` where S is a fresh
/// free variable. ay handles the free variable via ground arithmetic: the ensures
/// constrains S based on RECV, and the negated check becomes
/// `ensures(S, RECV) AND NOT requires(S)` which is UNSAT when the ensures-derived
/// post-state satisfies the precondition.
pub(in crate::callbacks) fn try_ground_forall_obligation(
    expr: &PureExpr,
    closure_specs: &[ClosureSpec],
) -> Option<PureExpr> {
    let inner = unwrap_foralls(expr);

    // Pattern: postcondition_mut(RECV, ARGS, st, r) ==> CONSEQUENT
    let PureExpr::BinOp(antecedent, BinOp::Implies, _consequent) = inner else {
        return None;
    };

    let (recv, args_expr, _st_expr, _r_expr) = find_postcondition_mut_in_expr(antecedent)?;
    let spec = match closure_receiver_base_name(recv) {
        Some(receiver_name) => {
            let mut matching = closure_specs
                .iter()
                .filter(|spec| spec.receiver_name == receiver_name);
            match matching.next() {
                Some(spec) if matching.next().is_none() => spec,
                _ => {
                    // No name match or ambiguous; fall back to single-entry match
                    // for chained postcondition_mut with intermediate state receivers.
                    if closure_specs.len() == 1 {
                        &closure_specs[0]
                    } else {
                        return None;
                    }
                }
            }
        }
        None => {
            // Receiver is a tuple constructor; single-entry fallback.
            if closure_specs.len() == 1 {
                &closure_specs[0]
            } else {
                return None;
            }
        }
    };

    // Use a fresh free variable S for the symbolic post-state.
    // In SMT, free variables are implicitly universally quantified.
    // The negated check becomes: ensures(RECV, S) AND NOT requires(S),
    // which is UNSAT when the ensures-derived post-state satisfies the precondition.
    // Sort is None (untyped) because the post-state represents the entire
    // closure capture environment, which is a product type (tuple of captured
    // variable sorts), not necessarily Int. The ay encoder infers Sort::Int
    // as the default for untyped variables, which matches the SMT encoding
    // where all uninterpreted sorts map to Int.
    let fresh_post_var = PureExpr::Var("__forall_post_state".to_string(), None);
    let unused_result = PureExpr::Var("_unused".to_string(), None);

    // Build ensures(pre=RECV, post=S): constrains S based on RECV.
    // substitute_captures_inline maps:
    //   Var(capture) outside old → tuple_get_i(post_state=S)
    //   Old(Var(capture))        → tuple_get_i(pre_state=RECV)
    let ensures_conj = spec
        .ensures_exprs
        .iter()
        .map(|ens_expr| {
            let ens_expr =
                substitute_closure_params_with_args(ens_expr, &spec.param_names, args_expr);
            substitute_captures_inline(
                &ens_expr,
                &spec.capture_bindings,
                recv,
                &fresh_post_var,
                &unused_result,
                false,
            )
        })
        .reduce(|acc, p| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(p)));

    // Build requires(post=S): checks precondition on post-state.
    // Requires has no old(), so captures map to post_state=S.
    let requires_conj = spec
        .requires_exprs
        .iter()
        .map(|req_expr| {
            let req_expr =
                substitute_closure_params_with_args(req_expr, &spec.param_names, args_expr);
            substitute_captures_inline(
                &req_expr,
                &spec.capture_bindings,
                recv,
                &fresh_post_var,
                &unused_result,
                false,
            )
        })
        .reduce(|acc, p| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(p)));

    match (ensures_conj, requires_conj) {
        (Some(ens), Some(req)) => {
            let grounded = PureExpr::BinOp(Arc::new(ens), BinOp::Implies, Arc::new(req));
            Some(scalarize_grounded_obligation(grounded, recv))
        }
        _ => None,
    }
}

/// Reduce a grounded forall obligation over a CONCRETE tuple closure env to
/// scalar form so the encoder does not fragment it into disconnected
/// sort-coercion constants (closures/07 test_fnmut2).
///
/// `substitute_captures_inline` leaves two projection shapes in the grounded
/// implication:
///
/// - `tuple_get_i(tupleN(f_0, .., f_{N-1}))` on the pre-state (receiver) side —
///   reduced to `f_i` (the constructor/projection identity the encoder itself
///   asserts as an axiom for every tuple term).
/// - `tuple_get_i(__forall_post_state)` on the universal post-state side —
///   replaced by a fresh free field variable carrying the receiver field's
///   inferred scalar sort. `__forall_post_state` has no other uses (only
///   projections of it occur), so this is an equisatisfiable renaming of the
///   implicitly-universal state, NOT a witness instantiation.
///
/// Afterwards `collapse_idempotent_views` removes the now provably-scalar
/// `View` wrappers, leaving a pure arithmetic implication the solver can
/// discharge against the caller-side prophecy-tower premises.
///
/// Gated on the receiver being a concrete tuple constructor whose fields all
/// root in sorted `Var`s: opaque receivers (e.g. `call_N` from Box-wrapped
/// FnMut chains) are returned unchanged.
fn scalarize_grounded_obligation(grounded: PureExpr, recv: &PureExpr) -> PureExpr {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity;

    // Gate: receiver must be a concrete tuple constructor (possibly behind
    // Deref/Final wrappers) with every field rooted in a sorted Var.
    let stripped = super::strip_receiver_state_wrappers(recv);
    let PureExpr::LogicFnCall { name, args } = &stripped else {
        return grounded;
    };
    if tuple_logic_fn_arity(name) != Some(args.len()) {
        return grounded;
    }
    let field_sorts: Vec<_> = args.iter().map(root_var_sort).collect();
    if field_sorts.iter().any(Option::is_none) {
        return grounded;
    }

    let reduced = reduce_tuple_projections(&grounded, &field_sorts);
    crate::callbacks::proof_assert_extract::collapse_idempotent_views(reduced)
}

/// The sort of the `Var` at the root of an expression, looking through
/// `Deref`/`Final`/`View` wrappers.
fn root_var_sort(expr: &PureExpr) -> Option<trust_wp_core::formula::ExprSort> {
    match expr {
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            root_var_sort(inner)
        }
        _ => None,
    }
}

/// Bottom-up rewrite of the two grounded projection shapes (see
/// [`scalarize_grounded_obligation`]).
fn reduce_tuple_projections(
    expr: &PureExpr,
    field_sorts: &[Option<trust_wp_core::formula::ExprSort>],
) -> PureExpr {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity;

    expr.rewrite_bottom_up(|node: PureExpr| {
        let PureExpr::LogicFnCall { name, args } = &node else {
            return node;
        };
        let Some(field_idx) = tuple_getter_field_index(name) else {
            return node;
        };
        if args.len() != 1 {
            return node;
        }
        match &args[0] {
            // tuple_get_i(tupleN(f_0, ..)) → f_i
            PureExpr::LogicFnCall {
                name: ctor,
                args: fields,
            } if tuple_logic_fn_arity(ctor) == Some(fields.len()) && field_idx < fields.len() => {
                fields[field_idx].clone()
            }
            // tuple_get_i(__forall_post_state) → fresh sorted field var
            PureExpr::Var(state, _) if state == "__forall_post_state" => PureExpr::Var(
                format!("__forall_post_field_{field_idx}"),
                field_sorts.get(field_idx).cloned().flatten(),
            ),
            _ => node,
        }
    })
}

/// Field index of a `__trust_wp_tuple_get_N` logic-fn name, if it is one.
fn tuple_getter_field_index(name: &str) -> Option<usize> {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;
    for idx in 0..8 {
        if name == tuple_field_logic_fn_name(idx) {
            return Some(idx);
        }
    }
    None
}
