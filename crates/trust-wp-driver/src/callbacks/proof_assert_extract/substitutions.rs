// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Substitution handling and sort inference for proof_assert extraction.
//!
//! Handles resolution of internal variable references in substitution maps,
//! generation of substitution-based assumptions, and sort inference for
//! substitution LHS/RHS expressions.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{
    intern_sort_name, resolve_sort_name, BinOp, ExprSort, Pattern, PureExpr, UnOp,
};

use super::view_normalization::{
    collapse_idempotent_views, is_provably_view_identity_domain,
    preserve_transparent_adapter_view_witness, transparent_adapter_inner,
};
use crate::mir_analysis::NameSubstitutions;

/// Resolve internal variable references within a substitution map.
///
/// When the substitution map has entries like `"set" → call_1` and
/// `"length1" → Final(Var("set")).len()`, the second entry contains
/// `Var("set")` which should be resolved to `call_1`. Without this,
/// the SMT solver sees `Final(Var("set"))` and `Final(call_1)` as
/// distinct terms — `Final` is encoded as an uninterpreted function,
/// so the solver cannot automatically derive their equality even when
/// `Var("set") == call_1` is asserted. (#1581)
///
/// Performs a single pass: for each entry, substitutes all other entries'
/// values into its expression. This handles one level of indirection,
/// which covers the common pattern of ghost method calls referencing
/// previously-assigned locals.
#[cfg(test)]
pub(in crate::callbacks) fn resolve_internal_references(
    substitutions: &mut HashMap<String, PureExpr>,
) {
    resolve_internal_references_at_current_state(substitutions, &HashSet::new());
}

/// [`resolve_internal_references`] for a map whose `written_memory` names
/// read memory a write may have changed before the cutoff (D-185).
///
/// Each binding was translated at its own program point, so a `Deref(Var
/// x)` inside one is the pointee as it was read there: before any write, the
/// entry value. The `*x` entry is the pointee at the cutoff, and `x ->
/// ^x`-style advances are the reference after a later call; resolving either
/// into another binding moved that binding's read past the write (`let v = *x
/// + 1; *x = 5;` resolved `v` to `5 + 1`). Neither resolves into another
/// binding for a name in `written_memory`.
pub(in crate::callbacks) fn resolve_internal_references_at_current_state(
    substitutions: &mut HashMap<String, PureExpr>,
    written_memory: &HashSet<String>,
) {
    // Build the full resolution map (name → concrete expression).
    // We need a snapshot to avoid borrowing issues.
    let snapshot: HashMap<String, PureExpr> = substitutions.clone();
    for (name, expr) in substitutions.iter_mut() {
        // Preserve bare post-state carriers like `^call_4` instead of resolving
        // them to `^seq_empty()`. Proof-assert mutation facts need the symbolic
        // carrier so later assumptions can relate the pre-state (`call_4`) and
        // post-state (`^call_4`) through helper specs. (#2616)
        if preserves_bare_final_carrier(expr) {
            continue;
        }
        // A `snapshot!(*a)` of a `&mut T` freezes `*a`'s CURRENT value at the
        // capture point, stored as the bare current-deref carrier
        // `Deref(Var("a"))` (= `a_current`, an SSA-stable quantity pinned by the
        // function precondition). The frozen value must NOT be advanced by the
        // POST-capture state of the same reference. Two later updates would
        // corrupt it if resolved in:
        //   - `a -> Final(Var("a"))` (reference advanced to prophecy after an
        //     intervening `&mut` call) → would give `Deref(Final(Var("a")))`,
        //   - `"*a" -> <post-call deref>` (current pointee re-read after the
        //     call resolves the reborrow) → would give the post-call value.
        // Both apply to the LIVE reference, never to a frozen captured current.
        // Exclude exactly the self-rooted advancement keys when resolving such a
        // carrier; all other entries still resolve normally. (#682)
        let frozen_current_root = bare_current_deref_carrier_root(expr);
        // Build a substitution map excluding self to avoid circular replacement.
        let mut resolve_map: HashMap<String, PureExpr> = HashMap::new();
        for (other_name, other_expr) in &snapshot {
            if other_name == name {
                continue;
            }
            if let Some(root) = frozen_current_root {
                let advances_self_ref =
                    other_name == root && advances_carrier_to_final(root, other_expr);
                let is_self_post_call_deref = other_name == &format!("*{root}");
                if advances_self_ref || is_self_post_call_deref {
                    continue;
                }
            }
            if let Some(root) = other_name.strip_prefix('*') {
                if written_memory.contains(root) {
                    continue;
                }
            }
            if written_memory.contains(other_name.as_str())
                && advances_carrier_to_final(other_name, other_expr)
            {
                continue;
            }
            resolve_map.insert(other_name.clone(), other_expr.clone());
        }
        if !resolve_map.is_empty() {
            *expr = expr.substitute_no_tuple_beta(&resolve_map);
        }
    }
}

/// If `expr` is a bare current-deref carrier `Deref(<carrier>)` whose carrier
/// leaf is a variable, return that variable name. These denote the SSA-stable
/// current pointee `name_current` (e.g. a frozen `snapshot!(*name)`). (#682)
fn bare_current_deref_carrier_root(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Deref(inner) = expr else {
        return None;
    };
    final_carrier_root_name(inner)
}

/// True when `name`'s substitution advances the reference to its own prophecy,
/// i.e. the value is a `Final`-carrier rooted at `name` (`name -> Final(.. name ..)`).
fn advances_carrier_to_final(name: &str, expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Final(_))
        && final_carrier_root_name(expr).is_some_and(|root| root == name)
}

fn final_carrier_root_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Final(inner) | PureExpr::Deref(inner) => final_carrier_root_name(inner),
        _ => None,
    }
}

fn preserves_bare_final_carrier(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Final(inner) if final_carrier_leaf(inner))
}

fn final_carrier_leaf(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, _) => true,
        PureExpr::Final(inner) | PureExpr::Deref(inner) => final_carrier_leaf(inner),
        _ => false,
    }
}

/// `substitutions` without the `name` and `*name` entries of the names in
/// `written_memory` (D-185): those entries are the CURRENT value of memory a
/// write changed, and as a fact `*name == v` (or `name == v` of a capture or
/// an advanced borrow) they would equate it with the entry value (the
/// encoders name both by the one symbol, `name_current` or the capture),
/// turning every entry fact and every copy taken before the write into one
/// about the written value. The assertion still reads the current value
/// through the substitution itself.
pub(in crate::callbacks) fn without_current_pointee_keys(
    substitutions: &NameSubstitutions,
    written_memory: &HashSet<String>,
) -> NameSubstitutions {
    if written_memory.is_empty() {
        return substitutions.clone();
    }
    let mut kept = substitutions.clone();
    kept.exprs.retain(|key, _| {
        let root = key.strip_prefix('*').unwrap_or(key);
        !written_memory.contains(root)
    });
    kept
}

pub(in crate::callbacks) fn substitution_assumptions(
    substitutions: &NameSubstitutions,
) -> Vec<PureExpr> {
    let mut entries: Vec<_> = substitutions.iter().collect();
    entries.sort_by_key(|(lhs_a, _)| *lhs_a);
    entries
        .into_iter()
        .filter_map(|(lhs, rhs)| {
            let lhs_expr = annotate_substitution_expr_sorts(
                &parse_substitution_lhs(lhs, substitutions)?,
                substitutions,
            );
            let rhs_expr = preserve_transparent_adapter_view_witness(
                annotate_substitution_expr_sorts(rhs, substitutions),
            );

            // When the LHS has a non-view-identity sort (e.g., Duration) but the
            // RHS is already in view-identity domain (from `result@ == <expr>`
            // spec extraction), emit
            // `View(LHS) == RHS` instead of `LHS == RHS` to avoid sort mismatch.
            // The spec extraction path extracts view expressions but the substitution
            // map stores them as values of the raw variable. (#976)
            let effective_lhs = if needs_view_bridge(&lhs_expr, &rhs_expr) {
                PureExpr::View(Arc::new(lhs_expr))
            } else {
                lhs_expr
            };

            Some(collapse_idempotent_views(PureExpr::BinOp(
                Arc::new(effective_lhs),
                BinOp::Eq,
                Arc::new(rhs_expr),
            )))
        })
        .collect()
}

/// Check if a substitution assumption needs a View bridge: the LHS has a
/// non-view-identity sort (Datatype/ref/unresolved) but the RHS is already
/// in view-identity domain.
fn needs_view_bridge(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    infer_substitution_expr_sort(lhs)
        .is_some_and(|lhs_sort| !is_existing_view_domain_sort(&lhs_sort))
        && rhs_needs_view_bridge(rhs)
}

fn rhs_needs_view_bridge(rhs: &PureExpr) -> bool {
    let rhs = transparent_adapter_inner(rhs).unwrap_or(rhs);
    if is_provably_view_identity_domain(rhs) {
        return true;
    }
    if infer_substitution_expr_sort(rhs).is_some_and(|sort| is_existing_view_domain_sort(&sort)) {
        return true;
    }
    let text = format!("{rhs:?}");
    text.contains("Intersection")
        || text.contains("Difference")
        || text.contains("intersection")
        || text.contains("difference")
}

fn parse_substitution_lhs(lhs: &str, substitutions: &NameSubstitutions) -> Option<PureExpr> {
    let base_sort = substitution_lhs_base_sort(lhs, substitutions);

    // `^*x` appears in ghost contexts where final dereference state is tracked.
    if let Some(name) = lhs.strip_prefix("^*") {
        if is_dotted_ident(name) {
            return Some(PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var(name.to_string(), base_sort.clone()),
            )))));
        }
        return None;
    }

    // `^^x` can arise from nested final wrappers.
    if let Some(name) = lhs.strip_prefix("^^") {
        if is_dotted_ident(name) {
            return Some(PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Var(name.to_string(), base_sort.clone()),
            )))));
        }
        return None;
    }

    if let Some(name) = lhs.strip_prefix('^') {
        if is_dotted_ident(name) {
            return Some(PureExpr::Final(Arc::new(PureExpr::Var(
                name.to_string(),
                base_sort.clone(),
            ))));
        }
        return None;
    }

    if let Some(name) = lhs.strip_prefix('*') {
        // Accept both simple identifiers (`*x`) and dotted-with-deref keys
        // (`*self.0`) so synthesized closure-capture substitutions for
        // `Box<&mut T>` ByValue captures can drive proof-assert assumptions
        // about the inner pointee. (#5 closures/09)
        if is_dotted_ident(name) {
            return Some(PureExpr::Deref(Arc::new(PureExpr::Var(
                name.to_string(),
                base_sort.clone(),
            ))));
        }
        return None;
    }

    // Accept `self.N` keys for closure-capture substitutions where the body
    // extraction phase records writes into closure env fields. Without this,
    // every `self.N` substitution would be silently dropped. (#5 closures/09)
    if is_dotted_ident(lhs) {
        return Some(PureExpr::Var(lhs.to_string(), base_sort));
    }

    None
}

/// Identifier with optional dotted-number suffix: `x`, `self`, `self.0`,
/// `foo.1.2`. Permits the dotted form so closure-env keys like `self.1`
/// flow through proof-assert substitution.
fn is_dotted_ident(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let mut parts = name.split('.');
    let Some(first) = parts.next() else {
        return false;
    };
    if !is_simple_ident(first) {
        return false;
    }
    parts.all(|part| !part.is_empty() && part.chars().all(|c| c.is_ascii_digit()))
}

fn substitution_lhs_base_sort(lhs: &str, substitutions: &NameSubstitutions) -> Option<ExprSort> {
    let base_name = lhs
        .strip_prefix("^*")
        .or_else(|| lhs.strip_prefix("^^"))
        .or_else(|| lhs.strip_prefix('^'))
        .or_else(|| lhs.strip_prefix('*'))
        .unwrap_or(lhs);

    is_dotted_ident(base_name)
        .then_some(base_name)
        .and_then(|name| substitution_name_sort(name, substitutions))
}

fn annotate_substitution_expr_sorts(
    expr: &PureExpr,
    substitutions: &NameSubstitutions,
) -> PureExpr {
    annotate_substitution_expr_sorts_with_scope(expr, substitutions, &HashSet::new())
}

fn annotate_substitution_expr_sorts_with_scope(
    expr: &PureExpr,
    substitutions: &NameSubstitutions,
    scoped_names: &HashSet<String>,
) -> PureExpr {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => expr.clone(),
        PureExpr::Var(name, None) if !scoped_names.contains(name) => {
            PureExpr::Var(name.clone(), substitution_name_sort(name, substitutions))
        }
        PureExpr::Var(_, Some(_)) => expr.clone(),
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(annotate_substitution_expr_sorts_with_scope(
                left,
                substitutions,
                scoped_names,
            )),
            *op,
            Arc::new(annotate_substitution_expr_sorts_with_scope(
                right,
                substitutions,
                scoped_names,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(annotate_substitution_expr_sorts_with_scope(
                inner,
                substitutions,
                scoped_names,
            )),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(annotate_substitution_expr_sorts_with_scope(
                cond,
                substitutions,
                scoped_names,
            )),
            Arc::new(annotate_substitution_expr_sorts_with_scope(
                then_expr,
                substitutions,
                scoped_names,
            )),
            Arc::new(annotate_substitution_expr_sorts_with_scope(
                else_expr,
                substitutions,
                scoped_names,
            )),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(
            annotate_substitution_expr_sorts_with_scope(inner, substitutions, scoped_names),
        )),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(
            annotate_substitution_expr_sorts_with_scope(inner, substitutions, scoped_names),
        )),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(
            annotate_substitution_expr_sorts_with_scope(inner, substitutions, scoped_names),
        )),
        PureExpr::View(inner) => PureExpr::View(Arc::new(
            annotate_substitution_expr_sorts_with_scope(inner, substitutions, scoped_names),
        )),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(annotate_substitution_expr_sorts_with_scope(
                receiver,
                substitutions,
                scoped_names,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| {
                    annotate_substitution_expr_sorts_with_scope(arg, substitutions, scoped_names)
                })
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let mut scoped_names = scoped_names.clone();
            scoped_names.insert(var.clone());
            PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(annotate_substitution_expr_sorts_with_scope(
                    body,
                    substitutions,
                    &scoped_names,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                annotate_substitution_expr_sorts_with_scope(
                                    expr,
                                    substitutions,
                                    &scoped_names,
                                )
                            })
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let mut scoped_names = scoped_names.clone();
            scoped_names.insert(var.clone());
            PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(annotate_substitution_expr_sorts_with_scope(
                    body,
                    substitutions,
                    &scoped_names,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                annotate_substitution_expr_sorts_with_scope(
                                    expr,
                                    substitutions,
                                    &scoped_names,
                                )
                            })
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(annotate_substitution_expr_sorts_with_scope(
                scrutinee,
                substitutions,
                scoped_names,
            )),
            arms: arms
                .iter()
                .map(|arm| {
                    let mut arm_scoped_names = scoped_names.clone();
                    pattern_bound_names(&arm.pattern, &mut arm_scoped_names);
                    trust_wp_core::formula::MatchArm {
                        pattern: arm.pattern.clone(),
                        body: annotate_substitution_expr_sorts_with_scope(
                            &arm.body,
                            substitutions,
                            &arm_scoped_names,
                        ),
                    }
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| {
                    annotate_substitution_expr_sorts_with_scope(arg, substitutions, scoped_names)
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => {
            let value_scoped_names = scoped_names.clone();
            let mut body_scoped_names = scoped_names.clone();
            body_scoped_names.insert(var.clone());
            PureExpr::Let {
                var: var.clone(),
                value: Arc::new(annotate_substitution_expr_sorts_with_scope(
                    value,
                    substitutions,
                    &value_scoped_names,
                )),
                body: Arc::new(annotate_substitution_expr_sorts_with_scope(
                    body,
                    substitutions,
                    &body_scoped_names,
                )),
            }
        }
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(annotate_substitution_expr_sorts_with_scope(
                assumption,
                substitutions,
                scoped_names,
            )),
            body: Arc::new(annotate_substitution_expr_sorts_with_scope(
                body,
                substitutions,
                scoped_names,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(annotate_substitution_expr_sorts_with_scope(
                obligation,
                substitutions,
                scoped_names,
            )),
            body: Arc::new(annotate_substitution_expr_sorts_with_scope(
                body,
                substitutions,
                scoped_names,
            )),
        },
        PureExpr::Closure { params, body } => {
            let mut scoped_names = scoped_names.clone();
            for (param, _) in params {
                scoped_names.insert(param.clone());
            }
            PureExpr::Closure {
                params: params.clone(),
                body: Arc::new(annotate_substitution_expr_sorts_with_scope(
                    body,
                    substitutions,
                    &scoped_names,
                )),
            }
        }
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

fn pattern_bound_names(pattern: &Pattern, bound_names: &mut HashSet<String>) {
    match pattern {
        Pattern::Binding(name) => {
            bound_names.insert(name.clone());
        }
        Pattern::Constructor { inner, .. } => {
            if let Some(inner) = inner {
                pattern_bound_names(inner, bound_names);
            }
        }
        Pattern::Tuple(patterns) => {
            for pattern in patterns {
                pattern_bound_names(pattern, bound_names);
            }
        }
        Pattern::Wildcard | Pattern::Literal(_) => {}
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

fn substitution_name_sort(name: &str, substitutions: &NameSubstitutions) -> Option<ExprSort> {
    let mut visited = HashSet::new();
    substitution_name_sort_recursive(name, substitutions, &mut visited)
}

fn substitution_name_sort_recursive(
    name: &str,
    substitutions: &NameSubstitutions,
    visited: &mut HashSet<String>,
) -> Option<ExprSort> {
    if !visited.insert(name.to_string()) {
        return None;
    }

    if let Some(sort) = substitutions.name_sorts.get(name).cloned().flatten() {
        return Some(sort);
    }

    let Some(expr) = substitutions.get(name) else {
        return None;
    };

    if let Some(sort) = preserved_name_sort_from_expr(expr, substitutions, visited) {
        return Some(sort);
    }

    infer_substitution_expr_sort(expr)
}

fn preserved_name_sort_from_expr(
    expr: &PureExpr,
    substitutions: &NameSubstitutions,
    visited: &mut HashSet<String>,
) -> Option<ExprSort> {
    match expr {
        PureExpr::Var(_, Some(sort)) => Some(sort.clone()),
        PureExpr::Var(name, None) => substitution_name_sort_recursive(name, substitutions, visited),
        PureExpr::Final(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => preserved_name_sort_from_expr(inner, substitutions, visited),
        _ => None,
    }
}

pub(in crate::callbacks) fn infer_substitution_expr_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Bool(_) => Some(ExprSort::Bool),
        PureExpr::Int(_) => Some(ExprSort::Int),
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::BinOp(_, op, _) => match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or
            | BinOp::Implies => Some(ExprSort::Bool),
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr => Some(ExprSort::Int),
            #[allow(unreachable_patterns)]
            _ => None,
        },
        PureExpr::UnOp(UnOp::Not, _) => Some(ExprSort::Bool),
        PureExpr::UnOp(UnOp::Neg, _) => Some(ExprSort::Int),
        PureExpr::UnOp(_, _) => None,
        PureExpr::Ite(_, then_expr, else_expr) => infer_substitution_expr_sort(then_expr)
            .or_else(|| infer_substitution_expr_sort(else_expr)),
        PureExpr::Old(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            infer_substitution_expr_sort(inner)
        }
        PureExpr::Deref(inner) => {
            // Dereferencing a MutRef(T) yields T: `*(&mut i32)` is `i32`, not
            // `&mut i32`. Without this unwrapping, ghost context assumptions
            // like `*g2 == 1` (from `**g2 = 1` in ghost blocks) would have
            // their LHS sort inferred as MutRef(Int) instead of Int, causing a
            // spurious View bridge that breaks postcondition matching. (#2671)
            match infer_substitution_expr_sort(inner) {
                Some(ExprSort::MutRef(inner_sort)) => Some(*inner_sort),
                other => other,
            }
        }
        PureExpr::MethodCall { method, .. } => infer_method_call_sort(method),
        PureExpr::LogicFnCall { name, .. } => infer_logic_fn_call_sort(name),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => Some(ExprSort::Bool),
        PureExpr::Match { arms, .. } => arms
            .iter()
            .find_map(|arm| infer_substitution_expr_sort(&arm.body)),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. }
        | PureExpr::Closure { body, .. } => infer_substitution_expr_sort(body),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn infer_method_call_sort(method: &str) -> Option<ExprSort> {
    match method {
        "is_some" | "is_none" | "is_ok" | "is_err" | "contains" | "precondition"
        | "postcondition" | "postcondition_mut" | "postcondition_once" => Some(ExprSort::Bool),
        "len" | "len_logic" | "sum" | "discriminant" => Some(ExprSort::Int),
        // Sequence-transforming methods produce a Seq model term, which the
        // proof_assert boundary normalization needs to distinguish from
        // wrapper-carrier equalities like `v == ^call_4`. (#2616)
        "push_back" | "push_front" | "concat" | "set" | "subsequence" | "reverse" => {
            Some(ExprSort::Seq)
        }
        // deep_model/shallow_model return the mathematical model which varies
        // by receiver type (Int for numerics, Seq for Vec, FMap for HashMap).
        // Return None so the sort cascade handles it correctly.
        "deep_model" | "shallow_model" => None,
        _ => None,
    }
}

fn infer_logic_fn_call_sort(name: &str) -> Option<ExprSort> {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity;
    match name {
        "seq" | "seq_empty" | "Seq::empty" => Some(ExprSort::Seq),
        "fmap_insert" | "fmap_merge" | "fmap_empty" | "FMap::empty" => Some(ExprSort::FMap),
        "resolve" => Some(ExprSort::Bool),
        "Some" | "None" => Some(ExprSort::Datatype(intern_sort_name("core::option::Option"))),
        "Ok" | "Err" => Some(ExprSort::Datatype(intern_sort_name("core::result::Result"))),
        // A machine bit operation at its type (D-242) is an integer, as the
        // bare operator it wraps is.
        _ if trust_wp_core::formula::internal::machine_bitop::parse(name).is_some() => {
            Some(ExprSort::Int)
        }
        _ => tuple_logic_fn_arity(name)
            .and_then(|arity| u8::try_from(arity).ok().map(ExprSort::Tuple)),
    }
}

/// Check if a PureExpr is a `T::deref_mut.precondition(...)` method call.
///
/// These arise as call obligations when ghost blocks access values through
/// `Deref::deref` or `DerefMut::deref_mut`. For value types (tuples,
/// primitives), both deref and deref_mut always succeed — there is no
/// meaningful precondition. The solver has no axiom for the uninterpreted
/// `T::deref.precondition` / `T::deref_mut.precondition` symbols, so
/// leaving these as proof obligations makes verification impossible. (#1572)
pub(in crate::callbacks) fn is_deref_precondition(expr: &PureExpr) -> bool {
    if let PureExpr::MethodCall {
        receiver, method, ..
    } = expr
    {
        if method == "precondition" {
            if let PureExpr::Var(name, _) = receiver.as_ref() {
                return name.contains("deref_mut") || name.contains("deref");
            }
        }
    }
    false
}

pub(in crate::callbacks) fn is_simple_ident(name: &str) -> bool {
    // A renamed shadowed binding names a source binding too (D-237).
    crate::mir_analysis::binding_identity::is_binding_ident(name)
}

fn is_existing_view_domain_sort(sort: &ExprSort) -> bool {
    is_scalar_view_identity_sort(sort) || matches!(sort, ExprSort::Seq | ExprSort::FMap)
}

pub(in crate::callbacks) fn is_scalar_view_identity_sort(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Int | ExprSort::Bool | ExprSort::Float(_) | ExprSort::Unit => true,
        // The creusot/trust-wp logic integer type `Int` is carried as an
        // `ExprSort::Datatype("…::Int")` (ty_to_expr_sort_enriched maps every
        // ADT to a Datatype sort). Semantically it IS the mathematical integer
        // (SMT Int — the encoder's `is_int_model_type` re-maps it to Sort::Int),
        // so `View`/`@`/`deep_model` on it is the identity. Recognizing it here
        // lets `collapse_idempotent_views` strip the spurious `View(Int)` that a
        // scalar-returning ghost helper such as `FSet::len_ghost`/`FMap::len_ghost`
        // (`ensures result == self.len()`) produces. Without the collapse the
        // encoder declares a `<name>_view` carrier for the un-collapsed `View`
        // and projects it as a Bool (`ite view (= 1 len) (= 0 len)`), which is
        // UNSAT whenever the collection length ∉ {0,1} — a contradictory
        // (vacuous) base that wedges the whole ghost block. (ghost_set/ghost_map)
        ExprSort::Datatype(id) => is_logic_int_sort_name(&resolve_sort_name(*id)),
        _ => false,
    }
}

/// Whether a resolved Datatype sort name denotes the creusot/trust-wp logic
/// integer type `Int` (whose logical view is the identity). Matches only the
/// bare `Int` type — NOT the other `is_int_model_type` entries (`FSet`,
/// `HashSet`, `Duration`, …) whose views are genuine model transforms, not
/// identities.
fn is_logic_int_sort_name(name: &str) -> bool {
    name == "Int" || name.rsplit("::").next() == Some("Int")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logic_int_datatype_is_scalar_view_identity() {
        // `FSet::len_ghost`/`FMap::len_ghost` return the logic integer `Int`,
        // carried as `Datatype("creusot_std::Int")`. Its view is the identity,
        // so `collapse_idempotent_views` must be able to strip `View(Int)`.
        for name in ["Int", "creusot_std::Int", "trust_wp_std::logic::Int"] {
            assert!(
                is_scalar_view_identity_sort(&ExprSort::Datatype(intern_sort_name(name))),
                "logic Int datatype {name:?} must be a scalar view-identity sort"
            );
        }
        // Genuine collection/model datatypes must NOT be treated as identity —
        // `View(FSet)`/`View(HashSet)` are real set-model transforms.
        for name in ["FSet", "HashSet", "creusot_std::logic::FMap"] {
            assert!(
                !is_scalar_view_identity_sort(&ExprSort::Datatype(intern_sort_name(name))),
                "collection datatype {name:?} must NOT be a scalar view-identity sort"
            );
        }
        // Primitive scalars remain identity domains.
        assert!(is_scalar_view_identity_sort(&ExprSort::Int));
        assert!(is_scalar_view_identity_sort(&ExprSort::Bool));
    }

    #[test]
    fn substitution_assumptions_preserve_copied_adapter_view_witness() {
        let mut substitutions = NameSubstitutions::default();
        substitutions.exprs.insert(
            "result".to_string(),
            PureExpr::LogicFnCall {
                name: "Copied".to_string(),
                args: vec![PureExpr::LogicFnCall {
                    name: "Intersection".to_string(),
                    args: vec![
                        PureExpr::Var("xs".to_string(), None),
                        PureExpr::Var("ys".to_string(), None),
                    ],
                }],
            },
        );
        substitutions.name_sorts.insert(
            "result".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("HashSet"))),
        );

        let assumptions = substitution_assumptions(&substitutions);
        assert_eq!(assumptions.len(), 1);
        let assump = &assumptions[0];
        assert!(
            matches!(
                assump,
                PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                    if matches!(lhs.as_ref(), PureExpr::View(_))
                    && matches!(rhs.as_ref(), PureExpr::View(inner)
                        if matches!(inner.as_ref(), PureExpr::LogicFnCall { name, .. } if name == "Intersection"))
            ),
            "copied adapter RHS should keep a View witness in substitution assumptions: {assump:?}"
        );
    }
}
