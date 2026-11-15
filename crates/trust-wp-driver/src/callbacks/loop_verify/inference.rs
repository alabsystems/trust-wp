// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant inference.
//!
//! Infers unsigned non-negativity invariants from MIR types, stable loop
//! invariants from unmodified pre-loop assignments, and type-invariant
//! preservation for unchanged places.

use std::sync::Arc;

use rustc_middle::{mir::Local, ty::TyKind};
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::tuple_field_logic_fn_index, BinOp, ExprSort, NamedBindingValue,
        PureExpr,
    },
    logic::is_invariant_method_name,
};

use super::{
    super::super::mir_analysis::{ChangedPlaces, ChangedPlacesTree, ForLoopGhostState},
    expr_utils::expr_referenced_vars,
};

/// Returns true if `expr` is `produced.len()` for the given ghost-sequence name.
fn is_produced_len_call(expr: &PureExpr, produced_name: &str) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { receiver, method, args }
            if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == produced_name)
    )
}

/// Infer the iterator produced-length bound `produced.len() <= L` (Stage 0 of
/// loop-invariant inference).
///
/// Creusot infers a bound on the number of produced elements for `for`-loops so
/// that a decreasing variant such as `#[variant(*len - produced.len())]` can be
/// proven non-negative (the `loop_variant_nonneg` obligation requires
/// `*len - produced.len() >= 0`, i.e. `produced.len() <= *len`). The user does
/// not write this bound, so trust-wp must supply it.
///
/// This is a SOUND, template-based candidate: it is injected into the loop's
/// `effective_invariants`, which feed ONLY the standard WP obligations
/// (initialization, preservation, postcondition). There is no trusted-invariant
/// channel, so a wrong candidate simply fails verification — it can never cause
/// a false-accept. The candidate is inductive from facts already in scope:
///   * entry: `produced.len() == 0` (`build_for_loop_init_facts`),
///   * step:  `produced' == produced.push_back(x)` (transition facts),
///   * length: `View(iter_old) == produced.concat(View(iter_state))`
///     (`build_for_loop_structural_invariant`).
///
/// # Narrow gate
///
/// The rule emits NOTHING unless ALL hold (so it is a no-op outside genuine
/// iterator/produced-bearing for-loops):
///   1. a for-loop ghost `state` is present (a real `for x in iter` loop),
///   2. a `variant` is present with the exact shape `L - produced.len()` where
///      `produced` is `state.produced_name`.
///
/// `L` is taken VERBATIM from the variant's left operand, so the emitted
/// invariant `produced.len() <= L` references the identical source-length term
/// the variant uses (e.g. `*len` = `Deref(Var("len"))`). This makes the
/// `loop_variant_nonneg` obligation `L - produced.len() >= 0` follow directly.
pub(in crate::callbacks) fn infer_iterator_produced_len_bound(
    variant: Option<&PureExpr>,
    state: Option<&ForLoopGhostState>,
    existing_invariants: &[PureExpr],
) -> Vec<PureExpr> {
    // Gate 1: must be a genuine for-loop with a `produced` ghost sequence.
    let Some(state) = state else {
        return Vec::new();
    };
    let produced_name = state.produced_name.as_str();

    // Gate 2: variant must be `L - produced.len()`.
    let Some(PureExpr::BinOp(lhs, BinOp::Sub, rhs)) = variant else {
        return Vec::new();
    };
    if !is_produced_len_call(rhs.as_ref(), produced_name) {
        return Vec::new();
    }
    let source_len = lhs.as_ref().clone();

    // Candidate: produced.len() <= L (with L taken verbatim from the variant).
    let bound = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                produced_name.to_string(),
                Some(ExprSort::Seq),
            )),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Le,
        Arc::new(source_len),
    );

    if existing_invariants.contains(&bound) {
        return Vec::new();
    }
    vec![bound]
}

pub(in crate::callbacks) fn infer_unsigned_nonneg_invariants(
    body: &rustc_middle::mir::Body<'_>,
    arg_names: &[String],
) -> Vec<PureExpr> {
    let mut names = std::collections::BTreeSet::new();

    for (idx, arg_name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(idx + 1);
        if matches!(body.local_decls[local].ty.kind(), TyKind::Uint(_)) {
            names.insert(arg_name.clone());
        }
    }

    for dbg in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &dbg.value {
            if place.projection.is_empty()
                && matches!(body.local_decls[place.local].ty.kind(), TyKind::Uint(_))
            {
                names.insert(dbg.name.to_string());
            }
        }
    }

    names
        .into_iter()
        .map(|name| {
            // Already filtered to Uint types — ExprSort::Int is correct.
            PureExpr::BinOp(
                Arc::new(PureExpr::Var(name, Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )
        })
        .collect()
}

pub(in crate::callbacks) fn infer_unsigned_nonneg_requires(
    body: &rustc_middle::mir::Body<'_>,
    arg_names: &[String],
) -> Vec<PureExpr> {
    arg_names
        .iter()
        .enumerate()
        .filter_map(|(idx, arg_name)| {
            let local = Local::from_usize(idx + 1);
            if matches!(body.local_decls[local].ty.kind(), TyKind::Uint(_)) {
                // Already filtered to Uint types — ExprSort::Int is correct.
                Some(PureExpr::BinOp(
                    Arc::new(PureExpr::Var(arg_name.clone(), Some(ExprSort::Int))),
                    BinOp::Ge,
                    Arc::new(PureExpr::Int(0)),
                ))
            } else {
                None
            }
        })
        .collect()
}

/// Detect fallback `arg{N}` placeholder names introduced by pre-loop call
/// resolution when an argument cannot be translated (see
/// `translated_args_for_pre_loop_call` in `pre_loop_resolve.rs`).
///
/// Returns true if `name` matches `arg\d+` and is NOT a real function
/// argument. These placeholders carry a `TypeParam` sort that triggers
/// spurious sort coercion in the loop encoder (#5226). Treating an
/// assignment binding involving such a placeholder as a stable invariant
/// makes the preservation VC produce fresh unconstrained coercion
/// constants that the solver can use as counterexamples.
fn references_fallback_arg_placeholder(expr: &PureExpr, real_arg_names: &[String]) -> bool {
    let vars = expr_referenced_vars(expr);
    vars.iter().any(|v| {
        crate::mir_analysis::is_fallback_arg_placeholder(v)
            || v.strip_prefix("arg")
                .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()))
                && !real_arg_names.iter().any(|real| real == v)
    })
}

/// Infer loop invariants from stable pre-loop assignments and stable requires.
///
/// Phase 1 of #1816: promotes postcondition-only frame equalities to explicit
/// loop invariants, making them available during preservation and variant checks.
///
/// Inference rules:
/// 1. For each `pre_loop_assignments[name] = value` where `name` is not in
///    `modified_vars`, emit `name == value` as an invariant.
/// 2. For each `requires` clause whose free variables are all unmodified,
///    emit the clause itself as a loop invariant.
///
/// Deduplicates against `existing_invariants` to avoid strengthening preservation
/// obligations with invariants the user (or other inference) already provides.
///
/// `arg_names` is the list of real function argument names; assignments
/// whose value references a synthetic `arg{N}` placeholder NOT in this list
/// are rejected. These placeholders are introduced by pre-loop call resolution
/// when an argument cannot be translated, and their `TypeParam` sort causes
/// the loop encoder to inject unconstrained sort-coercion fresh constants
/// during preservation (#5226).
pub(in crate::callbacks) fn infer_stable_loop_invariants(
    requires: &[PureExpr],
    pre_loop_assignments: &std::collections::HashMap<String, NamedBindingValue>,
    modified_vars: &[String],
    existing_invariants: &[PureExpr],
    arg_names: &[String],
) -> Vec<PureExpr> {
    let mut inferred = Vec::new();

    // Rule 1: Unmodified pre-loop assignments become equality invariants.
    // Both the variable AND its assigned value must reference only unmodified
    // variables. If `let n = i;` where `i` is modified in the loop, we cannot
    // infer `n == i` as an invariant — the primed form `n == i_prime` would
    // assert n equals the post-iteration value of i, which is unsound as a
    // general invariant.
    // Sort by name for deterministic output order.
    let mut sorted_names: Vec<&String> = pre_loop_assignments.keys().collect();
    sorted_names.sort();
    for name in sorted_names {
        if modified_vars.contains(name) {
            continue;
        }
        let binding = &pre_loop_assignments[name];
        // Reject assignments whose value references a synthetic `arg{N}`
        // placeholder that is not a real function argument. These come from
        // pre-loop call resolution fallbacks (e.g., `Ghost::new` arg that
        // could not be translated) and carry generic `TypeParam` sorts that
        // trigger spurious sort coercion in the preservation VC (#5226).
        if references_fallback_arg_placeholder(&binding.value, arg_names) {
            continue;
        }
        // Ensure the value expression only references unmodified variables.
        let value_vars = expr_referenced_vars(&binding.value);
        if value_vars.iter().any(|v| modified_vars.contains(v)) {
            continue;
        }
        let eq_inv = PureExpr::BinOp(
            Arc::new(PureExpr::Var(name.clone(), None)),
            BinOp::Eq,
            Arc::new(binding.value.clone()),
        );
        if !existing_invariants.contains(&eq_inv) && !inferred.contains(&eq_inv) {
            inferred.push(eq_inv);
        }
    }

    // Rule 2: Requires clauses referencing only unmodified variables are stable.
    for req_clause in requires {
        let vars = expr_referenced_vars(req_clause);
        let all_stable = vars.iter().all(|v| !modified_vars.contains(v));
        if all_stable && !existing_invariants.contains(req_clause) && !inferred.contains(req_clause)
        {
            inferred.push(req_clause.clone());
        }
    }

    inferred
}

/// Infer type-invariant preservation for unchanged places (#1816 Phase 3).
///
/// If a `requires` clause is a type-invariant method call (`x.invariant()` or
/// `x.__trust_wp_invariant_Foo()`) and the receiver place is unchanged in the
/// loop body (per `changed_places`), the type invariant is trivially preserved
/// across iterations and can be inferred as a loop invariant.
///
/// This recovers Creusot-like "type invariant persists when place is untouched"
/// semantics without solver-side changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReceiverProjectionStep {
    Field(u32),
    Deref,
}

fn parse_var_projection_path(name: &str) -> Option<(String, Vec<ReceiverProjectionStep>)> {
    let mut segments = name.split('.');
    let root = segments.next()?.trim();
    if root.is_empty() {
        return None;
    }
    let mut path = Vec::new();
    for seg in segments {
        // Unknown non-numeric field segments are conservatively treated as
        // root-level access: if the root changed at all, we reject inference.
        let Ok(field_idx) = seg.parse::<u32>() else {
            return Some((root.to_string(), Vec::new()));
        };
        path.push(ReceiverProjectionStep::Field(field_idx));
    }
    Some((root.to_string(), path))
}

fn parse_receiver_projection_path(
    receiver: &PureExpr,
) -> Option<(String, Vec<ReceiverProjectionStep>)> {
    match receiver {
        PureExpr::Var(name, _) => parse_var_projection_path(name),
        PureExpr::Old(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            parse_receiver_projection_path(inner)
        }
        PureExpr::Deref(inner) => {
            let (root, mut path) = parse_receiver_projection_path(inner)?;
            path.push(ReceiverProjectionStep::Deref);
            Some((root, path))
        }
        PureExpr::LogicFnCall { name, args } => {
            let field_idx = tuple_field_logic_fn_index(name)?;
            let base = args.first()?;
            if args.len() != 1 {
                return None;
            }
            let (root, mut path) = parse_receiver_projection_path(base)?;
            let field_idx = u32::try_from(field_idx).ok()?;
            path.push(ReceiverProjectionStep::Field(field_idx));
            Some((root, path))
        }
        _ => None,
    }
}

fn changed_tree_has_change_at_path(
    tree: &ChangedPlacesTree,
    path: &[ReceiverProjectionStep],
) -> bool {
    if path.is_empty() {
        // Any subtree entry means this exact place (or one of its sub-places)
        // is modified, so the receiver is not stable.
        return true;
    }

    match path[0] {
        ReceiverProjectionStep::Field(field_idx) => match tree {
            ChangedPlacesTree::Changed => true,
            ChangedPlacesTree::Fields(fields) => fields
                .get(&field_idx)
                .is_some_and(|inner| changed_tree_has_change_at_path(inner, &path[1..])),
            // Deref writes do not mutate sibling fields on the outer place.
            ChangedPlacesTree::Deref(_) => false,
        },
        ReceiverProjectionStep::Deref => match tree {
            ChangedPlacesTree::Changed => true,
            ChangedPlacesTree::Deref(inner) => changed_tree_has_change_at_path(inner, &path[1..]),
            // Direct field writes do not imply deref-target mutation.
            ChangedPlacesTree::Fields(_) => false,
        },
    }
}

fn receiver_projection_is_unchanged(receiver: &PureExpr, changed_places: &ChangedPlaces) -> bool {
    let Some((root, path)) = parse_receiver_projection_path(receiver) else {
        return false;
    };
    let Some(root_tree) = changed_places.0.get(&root) else {
        return true;
    };
    !changed_tree_has_change_at_path(root_tree, &path)
}

pub(in crate::callbacks) fn infer_stable_type_invariant_clauses(
    requires: &[PureExpr],
    changed_places: &ChangedPlaces,
    existing_invariants: &[PureExpr],
) -> Vec<PureExpr> {
    let mut inferred = Vec::new();

    for req_clause in requires {
        if let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = req_clause
        {
            // Only consider zero-argument invariant method calls.
            if !args.is_empty() || !is_invariant_method_name(method) {
                continue;
            }
            // If receiver place is unchanged in the loop body, the invariant holds.
            if receiver_projection_is_unchanged(receiver, changed_places)
                && !existing_invariants.contains(req_clause)
                && !inferred.contains(req_clause)
            {
                inferred.push(req_clause.clone());
            }
        }
    }

    inferred
}

/// Infer prophecy frame invariants for unchanged `&mut` parameters (#1816 Phase 2).
///
/// For each `&mut` parameter whose pointee is unchanged in the loop body
/// (per `changed_places`), generates:
/// 1. A synthetic pre-loop assignment: `{param}_final_old = ^param`
/// 2. A loop invariant: `^param == {param}_final_old`
///
/// This constrains the prophecy value across iterations, mirroring Creusot's
/// `^x == ^x_old` inference for unchanged mutable references.
///
/// The inference is skipped entirely when `modified_vars` is empty: with no
/// body modifications, the loop encoder does not prime any variable, so
/// `^param` is identical pre- and post-iteration. The synthetic invariant
/// would be vacuous but still injects an `untyped(Final(Var))` binding that
/// triggers sort coercion against `^param`'s `MutRef`-derived sort during
/// preservation, producing fresh unconstrained constants that the solver
/// uses as spurious counterexamples (bug/1743, #5226).
///
/// Returns `(synthetic_pre_loop_assignments, invariants)`.
pub(in crate::callbacks) fn infer_parameter_frame_invariants(
    arg_names: &[String],
    mut_ref_param_names: &std::collections::HashSet<String>,
    changed_places: &ChangedPlaces,
    pre_loop_assignments: &std::collections::HashMap<String, NamedBindingValue>,
    existing_invariants: &[PureExpr],
    modified_vars: &[String],
) -> (
    std::collections::HashMap<String, NamedBindingValue>,
    Vec<PureExpr>,
) {
    let mut synthetic_assignments = std::collections::HashMap::new();
    let mut invariants = Vec::new();

    // Vacuous-inference guard (#5226): when no body modification primes any
    // variable, `^param` is preserved trivially. Skipping the synthetic
    // binding avoids the sort-coercion bridge to `{param}_final_old`.
    if modified_vars.is_empty() {
        return (synthetic_assignments, invariants);
    }

    for param in arg_names {
        if !mut_ref_param_names.contains(param) {
            continue;
        }
        // If the parameter (or its pointee) is modified in the loop body, skip.
        // Any entry in changed_places means something under this local was written.
        if changed_places.0.contains_key(param) {
            continue;
        }
        // If there's already a pre-loop assignment for the prophecy old name,
        // the user (or prior inference) already handles this.
        let old_name = format!("{param}_final_old");
        if pre_loop_assignments.contains_key(&old_name) {
            continue;
        }

        // ^param (the prophecy/final value)
        let final_expr = PureExpr::Final(Arc::new(PureExpr::Var(param.clone(), None)));

        // Invariant: ^param == {param}_final_old
        let inv = PureExpr::BinOp(
            Arc::new(final_expr.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Var(old_name.clone(), None)),
        );

        // Dedup against existing invariants
        if existing_invariants.contains(&inv) || invariants.contains(&inv) {
            continue;
        }

        // Synthetic pre-loop assignment: {param}_final_old = ^param
        synthetic_assignments.insert(old_name, NamedBindingValue::untyped(final_expr));
        invariants.push(inv);
    }

    (synthetic_assignments, invariants)
}
