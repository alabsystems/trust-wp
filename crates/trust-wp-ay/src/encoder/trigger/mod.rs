// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trigger synthesis for triggerless quantifiers.
//!
//! This module provides E-matching trigger pattern synthesis for `forall`/`exists`
//! quantifiers that lack user-supplied triggers.
//!
//! # Submodules
//!
//! - [`coverage`]: Coverage tracking infrastructure (bitmask + fallback)
//! - [`walker`]: Recursive PureExpr walker for candidate collection
//!
//! # Key Functions
//!
//! - [`synthesize_triggers`]: Main entry — produces trigger patterns covering bound variables
//! - [`collect_nested_quantifier_vars`]: Gathers bound vars from nested same-kind quantifiers
//! - [`expr_mentions_any_var`]: Checks whether an expression references given variable names
//!
//! Recursive logic function evaluation helpers have been extracted to
//! [`super::recursive_eval`].

mod coverage;
pub(super) mod walker;

use std::collections::HashSet;

use coverage::{QuantifiedVarIndex, TriggerCandidate};
use trust_wp_core::formula::{BinOp, PureExpr};

pub(crate) use self::coverage::collect_quantified_var_usage;
use super::quantifier::QuantifierKind;

/// Bonus applied to trigger candidates that appear in an implication
/// consequent. This prefers the "interesting" branch of a proof obligation
/// over guard-side or antecedent-only calls.
const TRUST_WP_IMPLICATION_CONSEQUENT_BONUS: i32 = 15;

/// Collect all bound variable names from a chain of nested same-kind quantifiers.
///
/// When user-supplied triggers are empty, the nested-quantifier collapse in
/// `encode_pure_quantifier_impl` does not fire. This helper traverses the
/// nesting to gather all variable names and locate the innermost body, so
/// that trigger synthesis can search the full body for trigger candidates
/// that cover all bound variables.
pub(crate) fn collect_nested_quantifier_vars<'a>(
    kind: QuantifierKind,
    first_var: &str,
    outer_body: &'a PureExpr,
) -> (Vec<String>, &'a PureExpr) {
    let mut vars = vec![first_var.to_string()];
    let mut body = outer_body;
    loop {
        match body {
            PureExpr::Forall {
                var,
                body: inner,
                triggers,
                ..
            } if kind == QuantifierKind::Forall && triggers.is_empty() => {
                vars.push(var.clone());
                body = inner;
            }
            PureExpr::Exists {
                var,
                body: inner,
                triggers,
                ..
            } if kind == QuantifierKind::Exists && triggers.is_empty() => {
                vars.push(var.clone());
                body = inner;
            }
            _ => break,
        }
    }
    (vars, body)
}

/// Check whether a `PureExpr` directly or indirectly references any of the
/// given variable names.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn expr_mentions_any_var(expr: &PureExpr, vars: &[String]) -> bool {
    coverage::collect_quantified_var_usage(vars, expr).mentions_any()
}

/// Walk a `PureExpr` and collect `MethodCall` and `LogicFnCall` nodes that
/// reference at least one of the given bound variables.
///
/// Excludes arithmetic `BinOp` nodes — they are theory operators whose
/// trigger patterns would cause matching loops in E-matching.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn collect_trigger_candidates<'a>(
    expr: &'a PureExpr,
    vars: &[String],
    shadowed: &mut HashSet<String>,
    depth: usize,
    candidates: &mut Vec<TriggerCandidate<'a>>,
) {
    let index = QuantifiedVarIndex::new(vars);
    walker::collect_trigger_candidates_with_index(expr, &index, shadowed, depth, candidates);
}

/// Collect `LogicFnCall` and `MethodCall` sub-expressions from a quantifier body
/// that are completely ground — they do NOT reference any of the given bound variables.
///
/// These ground sub-expressions can be registered in the ground pool to help E-matching
/// fire on the quantifier. For example, in `forall<i> 0 <= i && i < v.len() ==> f(v.get(i))`,
/// the sub-expression `v.len()` is ground and should be in the ground pool so that axioms
/// about `seq_len` can be instantiated. (#2696)
///
/// Returns cloned `PureExpr` nodes (not references) because the caller re-encodes them
/// at `quantifier_depth == 0`.
pub(crate) fn collect_ground_subexprs(expr: &PureExpr, bound_vars: &[String]) -> Vec<PureExpr> {
    let index = QuantifiedVarIndex::new(bound_vars);
    let mut result = Vec::new();
    collect_ground_subexprs_impl(expr, &index, &mut HashSet::new(), 0, &mut result);
    result
}

/// Maximum sub-expressions to collect to avoid excessive re-encoding.
/// Increased from 8 to 12 to accommodate View-wrapped expressions and
/// deeper nesting patterns in quantified postconditions. (#2696)
const TRUST_WP_MAX_GROUND_SUBEXPRS: usize = 12;

/// Check whether an expression contains any `Var(name)` where `name` is in
/// the `shadowed` set. Does NOT respect internal binding (let, match, closure)
/// because the caller already tracks shadowing at the `collect_ground_subexprs_impl`
/// level.
///
/// Used to reject false "ground" classifications: when `collect_quantified_coverage`
/// reports empty coverage (the expression doesn't reference the outer quantifier's
/// bound vars), the expression may still reference variables from inner scopes
/// (nested quantifiers, let bindings, closures) tracked in `shadowed`. Re-encoding
/// such an expression at depth 0 would create free variables. (#2696 fix)
///
/// Uses `any_recursive` for exhaustive variant coverage — all PureExpr variants
/// are walked without manual enumeration. This is conservative: variables rebound
/// by inner scopes (Forall, Let, Closure, Match) still trigger a match, which
/// safely rejects rather than falsely accepts. (#2654)
fn expr_references_any_shadowed(expr: &PureExpr, shadowed: &HashSet<String>) -> bool {
    if shadowed.is_empty() {
        return false;
    }
    expr.any_recursive(|e| matches!(e, PureExpr::Var(name, _) if shadowed.contains(name.as_str())))
}

fn collect_ground_subexprs_impl(
    expr: &PureExpr,
    index: &QuantifiedVarIndex<'_>,
    shadowed: &mut HashSet<String>,
    depth: usize,
    out: &mut Vec<PureExpr>,
) {
    if out.len() >= TRUST_WP_MAX_GROUND_SUBEXPRS || depth > super::MAX_ENCODING_DEPTH {
        return;
    }
    let next = depth.saturating_add(1);
    match expr {
        PureExpr::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            // Check if the entire sub-tree is ground (no bound vars from the
            // outer quantifier AND no vars from inner scopes like nested
            // quantifiers, let bindings, or closures).
            //
            // The coverage check via `collect_quantified_coverage` only tests
            // against the outer quantifier's bound variables (the `index`).
            // Variables from inner scopes are in `shadowed` — they show as
            // empty coverage because they're not in the index, but they ARE
            // locally-bound. Re-encoding such an expression at depth 0 would
            // create free variables. (#2696 fix)
            let coverage = walker::collect_quantified_coverage(expr, index, shadowed, depth);
            if coverage.is_empty() && !expr_references_any_shadowed(expr, shadowed) {
                // Completely ground — register this call.
                out.push(expr.clone());
                // Don't recurse further; we already captured the whole sub-tree.
                return;
            }
            // Not fully ground — recurse into receiver and args to find
            // ground sub-expressions deeper in the tree.
            collect_ground_subexprs_impl(receiver, index, shadowed, next, out);
            for arg in args {
                collect_ground_subexprs_impl(arg, index, shadowed, next, out);
            }
        }
        PureExpr::LogicFnCall { name: _, args } => {
            let coverage = walker::collect_quantified_coverage(expr, index, shadowed, depth);
            if coverage.is_empty() && !expr_references_any_shadowed(expr, shadowed) {
                out.push(expr.clone());
                return;
            }
            for arg in args {
                collect_ground_subexprs_impl(arg, index, shadowed, next, out);
            }
        }
        PureExpr::BinOp(l, _, r) => {
            collect_ground_subexprs_impl(l, index, shadowed, next, out);
            collect_ground_subexprs_impl(r, index, shadowed, next, out);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner) => {
            collect_ground_subexprs_impl(inner, index, shadowed, next, out);
        }
        PureExpr::View(inner) => {
            // View-wrapped method calls like `v@.len()` or `(^v)@` are common
            // in quantified postconditions. When the entire View(call) is ground,
            // register the View-wrapped call to ensure the ground pool sees the
            // same form as the quantifier body encoding. (#2696)
            match inner.as_ref() {
                PureExpr::MethodCall { .. } | PureExpr::LogicFnCall { .. } => {
                    let coverage =
                        walker::collect_quantified_coverage(expr, index, shadowed, depth);
                    if coverage.is_empty() && !expr_references_any_shadowed(expr, shadowed) {
                        out.push(expr.clone());
                        return;
                    }
                }
                _ => {}
            }
            collect_ground_subexprs_impl(inner, index, shadowed, next, out);
        }
        PureExpr::Ite(c, t, e) => {
            collect_ground_subexprs_impl(c, index, shadowed, next, out);
            collect_ground_subexprs_impl(t, index, shadowed, next, out);
            collect_ground_subexprs_impl(e, index, shadowed, next, out);
        }
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            let was_new = shadowed.insert(var.clone());
            collect_ground_subexprs_impl(body, index, shadowed, next, out);
            if was_new {
                shadowed.remove(var);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_ground_subexprs_impl(scrutinee, index, shadowed, next, out);
            for arm in arms {
                let added: Vec<String> = arm
                    .pattern
                    .bound_names()
                    .into_iter()
                    .filter(|n| shadowed.insert(n.to_string()))
                    .map(|n| n.to_string())
                    .collect();
                collect_ground_subexprs_impl(&arm.body, index, shadowed, next, out);
                for name in &added {
                    shadowed.remove(name);
                }
            }
        }
        PureExpr::Let { var, value, body } => {
            collect_ground_subexprs_impl(value, index, shadowed, next, out);
            let was_new = shadowed.insert(var.clone());
            collect_ground_subexprs_impl(body, index, shadowed, next, out);
            if was_new {
                shadowed.remove(var);
            }
        }
        PureExpr::Closure { params, body } => {
            let added: Vec<String> = params
                .iter()
                .map(|(p, _)| p.clone())
                .filter(|p| shadowed.insert(p.clone()))
                .collect();
            collect_ground_subexprs_impl(body, index, shadowed, next, out);
            for name in &added {
                shadowed.remove(name);
            }
        }
        // Leaf nodes and other patterns — nothing to collect.
        _ => {}
    }
}

/// Maximum number of alternative trigger patterns to emit per quantifier.
///
/// Each alternative pattern gives the solver an independent instantiation
/// opportunity. More alternatives improve completeness but increase solver
/// workload. 4 is a good balance — it covers the common case of 2-3
/// independent function applications in a quantifier body without
/// overwhelming the solver's pattern-matching engine.
const TRUST_WP_MAX_ALTERNATIVE_PATTERNS: usize = 4;

/// Score bonus (subtracted from score, so lower = better) for trigger
/// candidates that appear in the consequent of an implication body.
///
/// In `forall x. guard(x) ==> consequent(x)`, triggers from the consequent
/// are more useful for E-matching because they target the "interesting" part
/// of the quantifier. Guards like `0 <= i && i < v.len()` are range bounds;
/// the consequent like `P(v.get(i))` is what needs instantiation. (#2696)
/// Score bonus for trigger candidates that appear as operands of equality comparisons.
///
/// In `forall x. ... f(x) == g(x) ...`, triggers from equality operands are
/// important because the equality is typically the property being verified.
/// Prioritizing these over incidental function calls in guards gives the solver
/// better instantiation targets. (#2696)
const TRUST_WP_EQUALITY_OPERAND_BONUS: i32 = 10;

/// Recursively collect trigger candidates from implication consequents in a
/// quantifier body.
///
/// This handles:
/// - `guard ==> consequent` -- collects from consequent
/// - `(g1 ==> P) && (g2 ==> Q)` -- collects from both P and Q
/// - `g1 ==> (g2 ==> consequent)` -- collects from the innermost consequent
/// - `g ==> if cond { A } else { B }` -- collects from both Ite branches
///
/// This gives the solver better trigger selection by prioritizing candidates
/// from the "interesting" part of the quantifier (the consequent) over range
/// bounds in the guard. (#2696)
fn collect_implication_consequent_candidates<'a>(
    body: &'a PureExpr,
    index: &QuantifiedVarIndex<'_>,
    out: &mut Vec<coverage::TriggerCandidate<'a>>,
) {
    match body {
        PureExpr::BinOp(_, BinOp::Implies, consequent) => {
            // Recurse into nested implications: `g1 ==> (g2 ==> P)` should
            // score P, not `g2 ==> P` as a whole.
            // Also recurse through And/Or in the consequent position.
            if matches!(
                consequent.as_ref(),
                PureExpr::BinOp(_, BinOp::Implies, _)
                    | PureExpr::BinOp(_, BinOp::And, _)
                    | PureExpr::BinOp(_, BinOp::Or, _)
            ) {
                collect_implication_consequent_candidates(consequent, index, out);
            } else if let PureExpr::Ite(_, then_branch, else_branch) = consequent.as_ref() {
                // `guard ==> if cond { A } else { B }`: collect from both
                // branches. Common in Creusot conditional postconditions like
                // `forall<x> g(x) ==> if take_first { A(x) } else { B(x) }`.
                // (#2696)
                collect_consequent_leaf_candidates(then_branch, index, out);
                collect_consequent_leaf_candidates(else_branch, index, out);
            } else {
                walker::collect_trigger_candidates_with_index(
                    consequent,
                    index,
                    &mut HashSet::new(),
                    1, // depth 1 since consequent is one level deep
                    out,
                );
            }
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            // Recurse into both branches of conjunctions to find implications
            // like `(g1 ==> P) && (g2 ==> Q)`.
            collect_implication_consequent_candidates(left, index, out);
            collect_implication_consequent_candidates(right, index, out);
        }
        _ => {}
    }
}

/// Collect trigger candidates from leaf expressions in an implication
/// consequent. Handles And/Or/Ite nesting within the consequent before
/// collecting from leaf terms.
fn collect_consequent_leaf_candidates<'a>(
    expr: &'a PureExpr,
    index: &QuantifiedVarIndex<'_>,
    out: &mut Vec<coverage::TriggerCandidate<'a>>,
) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) | PureExpr::BinOp(left, BinOp::Or, right) => {
            collect_consequent_leaf_candidates(left, index, out);
            collect_consequent_leaf_candidates(right, index, out);
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            collect_consequent_leaf_candidates(then_branch, index, out);
            collect_consequent_leaf_candidates(else_branch, index, out);
        }
        _ => {
            walker::collect_trigger_candidates_with_index(expr, index, &mut HashSet::new(), 1, out);
        }
    }
}

/// Collect trigger candidates from equality operands in a quantifier body.
///
/// When the body contains `f(x) == g(y)`, the operands `f(x)` and `g(y)` are
/// valuable trigger candidates because the equality is the core property. This
/// handles:
/// - Direct equalities: `f(x) == g(y)`
/// - Guarded equalities: `guard ==> (f(x) == g(y))`
/// - Conjunctions of equalities: `(f(x) == a) && (g(y) == b)`
/// - Equalities inside Ite branches
///
/// (#2696)
fn collect_equality_operand_candidates<'a>(
    body: &'a PureExpr,
    index: &QuantifiedVarIndex<'_>,
    out: &mut Vec<coverage::TriggerCandidate<'a>>,
) {
    match body {
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            // Both sides of equality are valuable trigger sources
            walker::collect_trigger_candidates_with_index(lhs, index, &mut HashSet::new(), 1, out);
            walker::collect_trigger_candidates_with_index(rhs, index, &mut HashSet::new(), 1, out);
        }
        PureExpr::BinOp(_, BinOp::Implies, consequent) => {
            // Recurse into implication consequent to find equalities
            collect_equality_operand_candidates(consequent, index, out);
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_equality_operand_candidates(left, index, out);
            collect_equality_operand_candidates(right, index, out);
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            collect_equality_operand_candidates(then_branch, index, out);
            collect_equality_operand_candidates(else_branch, index, out);
        }
        _ => {}
    }
}

/// Synthesize trigger patterns for a triggerless quantifier.
///
/// Returns `Vec<Vec<PureExpr>>` where each inner Vec is one multi-pattern
/// (a set of terms that together cover all bound variables). Multiple
/// inner Vecs represent **alternative** trigger patterns -- the solver can
/// instantiate the quantifier when ANY of them matches. Returns empty
/// if no suitable trigger can be found (falls back to ay auto-extraction).
///
/// # Alternative pattern emission
///
/// When multiple candidates each independently cover all bound variables,
/// earlier versions returned only the single best candidate. This left the
/// solver with exactly one instantiation opportunity, which could miss
/// matches when the best candidate's function symbol did not appear in the
/// ground term set but an alternative's symbol did. Now, up to
/// [`TRUST_WP_MAX_ALTERNATIVE_PATTERNS`] full-coverage candidates are emitted as
/// alternative patterns, giving the solver multiple independent chances
/// to instantiate the quantifier.
pub(crate) fn synthesize_triggers(vars: &[String], body: &PureExpr) -> Vec<Vec<PureExpr>> {
    let index = QuantifiedVarIndex::new(vars);
    let mut candidates = Vec::new();
    walker::collect_trigger_candidates_with_index(
        body,
        &index,
        &mut HashSet::new(),
        0,
        &mut candidates,
    );

    if candidates.is_empty() {
        return Vec::new();
    }

    // Prefer trigger candidates that occur in implication consequents. This
    // keeps the synthesized pattern aligned with the proof goal rather than
    // a cheaper antecedent helper call such as `inv(y)`.
    {
        let mut consequent_candidates = Vec::new();
        collect_implication_consequent_candidates(body, &index, &mut consequent_candidates);
        if !consequent_candidates.is_empty() {
            let consequent_ptrs: HashSet<*const PureExpr> = consequent_candidates
                .iter()
                .map(|c| c.expr as *const PureExpr)
                .collect();
            for candidate in &mut candidates {
                if consequent_ptrs.contains(&(candidate.expr as *const PureExpr)) {
                    candidate.score -= TRUST_WP_IMPLICATION_CONSEQUENT_BONUS;
                }
            }
        }
    }

    // Equality-aware scoring: walk the body to find equality operands and
    // apply a score bonus (lower = better) to trigger candidates that appear
    // on either side of an equality. This makes triggers from the verified
    // property rank higher than incidental guard-side candidates. (#2696)
    {
        let mut equality_operand_candidates = Vec::new();
        collect_equality_operand_candidates(body, &index, &mut equality_operand_candidates);
        if !equality_operand_candidates.is_empty() {
            // Build a set of equality operand candidate expression pointers for fast lookup.
            let equality_operand_ptrs: HashSet<*const PureExpr> = equality_operand_candidates
                .iter()
                .map(|c| c.expr as *const PureExpr)
                .collect();
            // Apply bonus to candidates whose expr pointer matches an equality operand candidate.
            for candidate in &mut candidates {
                if equality_operand_ptrs.contains(&(candidate.expr as *const PureExpr)) {
                    candidate.score -= TRUST_WP_EQUALITY_OPERAND_BONUS;
                }
            }
        }
    }

    // Sort by score (lower is better)
    candidates.sort_by_key(|c| c.score);

    // Collect all single candidates that fully cover all variables.
    // Emit up to TRUST_WP_MAX_ALTERNATIVE_PATTERNS as alternative trigger patterns,
    // deduplicated by expression content (structurally identical expressions
    // from different tree positions produce duplicate patterns that waste
    // solver pattern-matching slots without adding new instantiation info).
    let full_coverage: Vec<&TriggerCandidate<'_>> = candidates
        .iter()
        .filter(|c| index.coverage_is_full(&c.coverage))
        .collect();

    if !full_coverage.is_empty() {
        let mut alternatives: Vec<Vec<PureExpr>> = Vec::new();
        for c in &full_coverage {
            if alternatives.len() >= TRUST_WP_MAX_ALTERNATIVE_PATTERNS {
                break;
            }
            let pattern = vec![c.expr.clone()];
            if !alternatives.contains(&pattern) {
                alternatives.push(pattern);
            }
        }
        return alternatives;
    }

    // Try to find a pair of triggers that together cover all variables.
    // Collect up to TRUST_WP_MAX_ALTERNATIVE_PATTERNS distinct pairs, deduplicated.
    {
        let mut pair_patterns: Vec<Vec<PureExpr>> = Vec::new();
        'pair_search: for (i, c1) in candidates.iter().enumerate() {
            for c2 in candidates.iter().skip(i + 1) {
                if index.combined_coverage_is_full(&c1.coverage, &c2.coverage) {
                    let pattern = vec![c1.expr.clone(), c2.expr.clone()];
                    if !pair_patterns.contains(&pattern) {
                        pair_patterns.push(pattern);
                    }
                    if pair_patterns.len() >= TRUST_WP_MAX_ALTERNATIVE_PATTERNS {
                        break 'pair_search;
                    }
                }
            }
        }
        if !pair_patterns.is_empty() {
            return pair_patterns;
        }
    }

    // Greedy set-cover for 3+ variable quantifiers (#1143).
    // Pick the candidate that covers the most uncovered variables (break ties
    // by score), repeat until all variables are covered or no progress.
    if vars.len() > 2 {
        let mut uncovered = index.full_coverage();
        let mut selected = Vec::new();
        while !uncovered.is_empty() {
            let best = candidates
                .iter()
                .filter(|c| QuantifiedVarIndex::new_coverage_count(&c.coverage, &uncovered) > 0)
                .max_by_key(|c| {
                    let new_coverage =
                        QuantifiedVarIndex::new_coverage_count(&c.coverage, &uncovered);
                    // Primary: max new coverage. Secondary: min score (negate for max_by_key).
                    (new_coverage, std::cmp::Reverse(c.score))
                });
            match best {
                Some(c) => {
                    QuantifiedVarIndex::remove_from_uncovered(&mut uncovered, &c.coverage);
                    selected.push(c.expr.clone());
                }
                None => break,
            }
        }
        if uncovered.is_empty() && selected.len() > 2 {
            return vec![selected];
        }
    }

    // If we can't cover all variables, use the single best candidate anyway.
    // A partial trigger is better than no trigger — it provides at least some
    // E-matching guidance to ay.
    vec![vec![candidates[0].expr.clone()]]
}
