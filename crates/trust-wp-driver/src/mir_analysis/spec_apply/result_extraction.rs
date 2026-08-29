// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Result expression extraction from postcondition ensures clauses.
//!
//! Extracts direct `result == <expr>` constraints from postconditions,
//! including match-arm patterns and view (`result@`) operators.

use std::{collections::HashMap, sync::Arc};

use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_arity, BinOp, ExprSort, MatchArm, Pattern, PureExpr,
};

use super::{unresolved_symbolic_names, warn_unresolved_names};
use crate::callbacks::{
    proof_assert_extract::{
        is_provably_view_identity_domain, preserve_transparent_adapter_view_witness,
        transparent_adapter_inner,
    },
    strip_deref_wrappers,
};

pub(super) fn try_extract_result_expr(
    ensures_expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
    match_view_result: bool,
) -> Option<PureExpr> {
    let rhs_fn = if match_view_result {
        result_equality_rhs_with_view
    } else {
        result_equality_rhs
    };
    if let Some(substituted) = rhs_fn(ensures_expr, substitutions, param_names, ensures_str) {
        return Some(substituted);
    }
    // Try ITE/And recursive extraction before match-arm fallback. (#2366)
    //
    // Postconditions like `if *a >= *b { ... && result == a } else { ... && result == b }`
    // parse as `Ite(cond, And(..., result == a), And(..., result == b))`. The flat
    // equality matchers above don't recurse into ITE branches or conjunction bodies.
    if let Some(ite_result) = extract_result_rhs_recursive(
        ensures_expr,
        substitutions,
        param_names,
        ensures_str,
        match_view_result,
    ) {
        return Some(ite_result);
    }
    resolved_match_arm_result_rhs(
        ensures_expr,
        substitutions,
        param_names,
        ensures_str,
        match_view_result,
    )
}

fn result_equality_rhs(
    expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
) -> Option<PureExpr> {
    result_equality_rhs_inner(expr, substitutions, param_names, ensures_str, false)
}

/// Like `result_equality_rhs` but also matches `result@ == <expr>` patterns.
///
/// For primitive return types (e.g., `usize` from `Vec::len()`), the view
/// operator is transparent, so `result@ == x` is equivalent to `result == x`.
/// Both normal and loop body paths now use this variant. (#1463, #1673)
fn result_equality_rhs_with_view(
    expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
) -> Option<PureExpr> {
    result_equality_rhs_inner(expr, substitutions, param_names, ensures_str, true)
}

fn result_equality_rhs_inner(
    expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
    match_view_result: bool,
) -> Option<PureExpr> {
    fn preserve_view_if_needed(expr: PureExpr) -> PureExpr {
        let expr = normalize_direct_result_expr(&expr);
        if transparent_adapter_inner(&expr).is_some() {
            return preserve_transparent_adapter_view_witness(expr);
        }
        if is_set_adapter_view_expr(&expr) {
            PureExpr::View(Arc::new(expr))
        } else {
            expr
        }
    }

    // Pattern: result == <expr>
    if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
        if let PureExpr::Var(ref lhs_name, _) = **lhs {
            if lhs_name == "result" {
                let unresolved = unresolved_symbolic_names(rhs, substitutions, param_names);
                if unresolved.is_empty() {
                    return Some(preserve_view_if_needed(rhs.substitute(substitutions)));
                }
                // Warn but don't count — the clause may still be applied as a predicate
                // assumption in the second pass. The drop count is incremented there if
                // the clause is ultimately not applied.
                warn_unresolved_names(ensures_str, &unresolved, "postcondition");
                return None;
            }
        }
        // Pattern: <expr> == result
        if let PureExpr::Var(ref rhs_name, _) = **rhs {
            if rhs_name == "result" {
                let unresolved = unresolved_symbolic_names(lhs, substitutions, param_names);
                if unresolved.is_empty() {
                    return Some(preserve_view_if_needed(lhs.substitute(substitutions)));
                }
                warn_unresolved_names(ensures_str, &unresolved, "postcondition");
                return None;
            }
        }
    }

    // Pattern: result@ == <expr> (view of result — common for Vec::len, slice::len, etc.)
    // Matched in both normal and loop body paths since #1673.
    // For primitive return types, the view is the identity, so result@ == x is
    // equivalent to result == x. (#1463, #1673)
    if match_view_result {
        if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
            // Pattern: result@ == <expr>
            if let PureExpr::View(inner) = lhs.as_ref() {
                if let PureExpr::Var(ref lhs_name, _) = **inner {
                    if lhs_name == "result" {
                        let unresolved = unresolved_symbolic_names(rhs, substitutions, param_names);
                        if unresolved.is_empty() {
                            return Some(preserve_view_if_needed(rhs.substitute(substitutions)));
                        }
                        warn_unresolved_names(ensures_str, &unresolved, "postcondition");
                        return None;
                    }
                }
            }

            // Pattern: <expr> == result@ (symmetric view pattern)
            if let PureExpr::View(inner) = rhs.as_ref() {
                if let PureExpr::Var(ref rhs_name, _) = **inner {
                    if rhs_name == "result" {
                        let unresolved = unresolved_symbolic_names(lhs, substitutions, param_names);
                        if unresolved.is_empty() {
                            return Some(preserve_view_if_needed(lhs.substitute(substitutions)));
                        }
                        warn_unresolved_names(ensures_str, &unresolved, "postcondition");
                        return None;
                    }
                }
            }
        }
    }

    None
}

fn is_set_adapter_view_expr(expr: &PureExpr) -> bool {
    if is_provably_view_identity_domain(expr) {
        return false;
    }
    let text = format!("{expr:?}");
    text.contains("Intersection")
        || text.contains("Difference")
        || text.contains("intersection")
        || text.contains("difference")
}

/// Normalize an extracted result expression after parameter substitution.
///
/// After parameter substitution, postconditions may contain `Deref(Var("a"))` from
/// `*ma` where `ma` was substituted to `Var("a")` (the call-site target). Since the
/// borrow was already resolved at the call site, the `Deref` is semantically a no-op
/// for value-typed targets. Without stripping, the encoder produces `a_current` in SMT,
/// while the invariant uses `a` — and the loop preservation VC lacks the identity link.
///
/// Keep derefs around explicitly reference-typed variables: those represent
/// reading through a real reference carrier. Also normalize nullary enum
/// constructors that the parser accepts as bare identifiers in branch bodies
/// (`None` -> `None()`).
fn normalize_extracted_result_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Deref(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::Var(_, sort) if should_strip_deref_sort(sort)
            ) =>
        {
            inner.as_ref().clone()
        }
        PureExpr::Var(name, None) if is_nullary_constructor_name(name) => PureExpr::LogicFnCall {
            name: name.clone(),
            args: vec![],
        },
        PureExpr::BinOp(lhs, op, rhs) => PureExpr::BinOp(
            Arc::new(normalize_extracted_result_expr(lhs)),
            *op,
            Arc::new(normalize_extracted_result_expr(rhs)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(normalize_extracted_result_expr(inner)))
        }
        PureExpr::Ite(c, t, e) => PureExpr::Ite(
            Arc::new(normalize_extracted_result_expr(c)),
            Arc::new(normalize_extracted_result_expr(t)),
            Arc::new(normalize_extracted_result_expr(e)),
        ),
        PureExpr::View(inner) => PureExpr::View(Arc::new(normalize_extracted_result_expr(inner))),
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.iter().map(normalize_extracted_result_expr).collect(),
        },
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(normalize_extracted_result_expr(receiver)),
            method: method.clone(),
            args: args.iter().map(normalize_extracted_result_expr).collect(),
        },
        _ => expr.clone(),
    }
}

fn normalize_direct_result_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_extracted_result_expr(cond)),
            Arc::new(normalize_extracted_result_expr(then_expr)),
            Arc::new(normalize_extracted_result_expr(else_expr)),
        ),
        PureExpr::Var(name, None) if is_nullary_constructor_name(name) => PureExpr::LogicFnCall {
            name: name.clone(),
            args: vec![],
        },
        _ => expr.clone(),
    }
}

fn should_strip_deref_sort(sort: &Option<ExprSort>) -> bool {
    !matches!(sort, Some(ExprSort::Ref(_) | ExprSort::MutRef(_)))
}

fn is_nullary_constructor_name(name: &str) -> bool {
    matches!(name, "None")
}

/// Recursively extract `result == <expr>` from ITE branches and conjunction bodies. (#2366)
///
/// Handles postconditions of the form:
///   `if cond { X && result == a } else { Y && result == b }`
/// by recursing into each ITE branch and each And conjunct.
///
/// Returns `Ite(cond_substituted, a_rhs, b_rhs)` when both branches yield a result RHS.
/// Returns `None` (fail-closed) if either branch fails to yield a result binding.
fn extract_result_rhs_recursive(
    expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
    match_view_result: bool,
) -> Option<PureExpr> {
    let rhs_fn = if match_view_result {
        result_equality_rhs_with_view
    } else {
        result_equality_rhs
    };

    match expr {
        // ITE: extract from both branches, build ITE result.
        PureExpr::Ite(cond, then_branch, else_branch) => {
            let then_rhs =
                rhs_fn(then_branch, substitutions, param_names, ensures_str).or_else(|| {
                    extract_result_rhs_recursive(
                        then_branch,
                        substitutions,
                        param_names,
                        ensures_str,
                        match_view_result,
                    )
                })?;
            let else_rhs =
                rhs_fn(else_branch, substitutions, param_names, ensures_str).or_else(|| {
                    extract_result_rhs_recursive(
                        else_branch,
                        substitutions,
                        param_names,
                        ensures_str,
                        match_view_result,
                    )
                })?;
            let cond_substituted = normalize_extracted_result_expr(&cond.substitute(substitutions));
            Some(PureExpr::Ite(
                Arc::new(cond_substituted),
                Arc::new(normalize_extracted_result_expr(&then_rhs)),
                Arc::new(normalize_extracted_result_expr(&else_rhs)),
            ))
        }
        // And: try extracting from either conjunct (left or right).
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            rhs_fn(lhs, substitutions, param_names, ensures_str)
                .or_else(|| {
                    extract_result_rhs_recursive(
                        lhs,
                        substitutions,
                        param_names,
                        ensures_str,
                        match_view_result,
                    )
                })
                .or_else(|| rhs_fn(rhs, substitutions, param_names, ensures_str))
                .or_else(|| {
                    extract_result_rhs_recursive(
                        rhs,
                        substitutions,
                        param_names,
                        ensures_str,
                        match_view_result,
                    )
                })
        }
        _ => None,
    }
}

fn resolved_match_arm_result_rhs(
    ensures_expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
    match_view_result: bool,
) -> Option<PureExpr> {
    let PureExpr::Match { scrutinee, arms } = ensures_expr else {
        return None;
    };
    let scrutinee_value = strip_deref_wrappers(&scrutinee.substitute(substitutions));

    let rhs_fn = if match_view_result {
        result_equality_rhs_with_view
    } else {
        result_equality_rhs
    };

    let mut any_arm_matched_pattern = false;
    for arm in arms {
        let Some(bindings) = match_pattern_bindings(&arm.pattern, &scrutinee_value) else {
            continue;
        };
        any_arm_matched_pattern = true;
        let mut arm_substitutions = substitutions.clone();
        arm_substitutions.extend(bindings);
        if let Some(substituted) = rhs_fn(&arm.body, &arm_substitutions, param_names, ensures_str) {
            return Some(substituted);
        }
    }

    // Fallback: when the scrutinee is a variable (not a constructor), try to
    // extract `result == <expr>` from each arm body using only parameter
    // substitutions (pattern-bound variables stay as free vars). If ALL arms
    // yield a result RHS, build a new Match expression that represents what
    // result equals. The ay encoder handles this via constructor testers and
    // selector-based pattern bindings.
    //
    // Example: `match *self { Some(v) => result == Ok(v), None => result == Err(err) }`
    // When self is a variable (not a known constructor value), this produces:
    //   Match { scrutinee: self_var, arms: [Some(v) => Ok(v), None => Err(err_sub)] }
    // which the ay encoder converts to an ITE chain.
    if !any_arm_matched_pattern && !arms.is_empty() {
        if let Some(match_result) = try_extract_match_to_result_match(
            &scrutinee_value,
            arms,
            substitutions,
            param_names,
            ensures_str,
            match_view_result,
        ) {
            return Some(match_result);
        }
    }

    // Match-style postcondition recognized but no arm yielded result == <expr>.
    //
    // This does NOT mean the postcondition is lost: the full match expression
    // is still pushed as a CALL_ASSUMPTION in the predicate fallback loop
    // (apply_postconditions_with_self_inner, second ensures loop). The match
    // encoding in ay translates it to an ITE chain with constructor testers
    // (is_some/is_none), which the solver can reason about.
    //
    // The warning is informational — it means the call site will use the
    // full match expression as a predicate assumption rather than extracting
    // a direct `result = <expr>` substitution. (#1477, #1581)
    if any_arm_matched_pattern {
        debug!(
            "trust-wp: info: match-style postcondition: no arm produced \
             result == <expr> extraction (will use as predicate assumption) \
             in clause `{ensures_str}`"
        );
    } else if !arms.is_empty() {
        debug!(
            "trust-wp: info: match-style postcondition: scrutinee is not a constructor \
             (will use as predicate assumption) in clause `{ensures_str}`"
        );
    }

    None
}

/// Check if an expression is "variable-like" -- a Var, Deref(Var), View(Var),
/// or other form that could represent an ADT value whose constructor is
/// unknown at the call site. Rejects literals and concrete constructor
/// applications (LogicFnCall, Int, Bool, etc.).
fn is_variable_like(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(..) => true,
        PureExpr::Deref(inner) | PureExpr::View(inner) | PureExpr::Old(inner) => {
            is_variable_like(inner)
        }
        // MethodCall on a variable (e.g., `self.field()`) is variable-like
        PureExpr::MethodCall { receiver, .. } => is_variable_like(receiver),
        _ => false,
    }
}

/// Extract `result == <expr>` from each arm of a match postcondition when the
/// scrutinee is a variable (not a constructor value).
///
/// When all arms contain `result == <expr>`, returns a Match expression where
/// each arm body is the extracted RHS (what result equals). Pattern-bound
/// variables (e.g., `v` in `Some(v)`) remain as free `Var` nodes and are
/// resolved by the ay encoder's pattern binding/selector mechanism.
///
/// Fail-closed: returns `None` if any arm does not yield `result == <expr>`.
fn try_extract_match_to_result_match(
    scrutinee_value: &PureExpr,
    arms: &[MatchArm],
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
    ensures_str: &str,
    match_view_result: bool,
) -> Option<PureExpr> {
    // Guard: only apply this fallback when the scrutinee is a variable
    // (or deref/view of a variable) — i.e., something that could be an ADT
    // whose constructor is unknown at the call site. Reject literals and
    // other concrete expressions that would produce a semantically wrong
    // match (e.g., matching Int(42) against Some/None patterns).
    if !is_variable_like(scrutinee_value) {
        return None;
    }

    // Guard: at least one arm must use a Constructor pattern. This confirms
    // the match is over an ADT (Option, Result, user enum), not integers
    // or booleans. Without this, a match on a variable against Wildcard/Binding
    // patterns could produce spurious extractions.
    let has_constructor_arm = arms
        .iter()
        .any(|arm| matches!(arm.pattern, Pattern::Constructor { .. }));
    if !has_constructor_arm {
        return None;
    }

    let rhs_fn = if match_view_result {
        result_equality_rhs_with_view
    } else {
        result_equality_rhs
    };

    let mut new_arms = Vec::with_capacity(arms.len());
    for arm in arms {
        // Try to extract `result == <expr>` from the arm body using only
        // parameter substitutions. Pattern-bound variables (like `v` from
        // `Some(v)`) are not in the substitution map and stay as free Vars.
        // The `unresolved_symbolic_names` check in `result_equality_rhs_inner`
        // only flags known symbolic names (self, result, param_names, etc.),
        // so pattern-bound variables pass through.
        let extracted =
            rhs_fn(&arm.body, substitutions, param_names, ensures_str).or_else(|| {
                extract_result_rhs_recursive(
                    &arm.body,
                    substitutions,
                    param_names,
                    ensures_str,
                    match_view_result,
                )
            })?;
        new_arms.push(MatchArm {
            pattern: arm.pattern.clone(),
            body: extracted,
        });
    }

    Some(PureExpr::Match {
        scrutinee: Arc::new(scrutinee_value.clone()),
        arms: new_arms,
    })
}

fn match_pattern_bindings(
    pattern: &Pattern,
    value: &PureExpr,
) -> Option<HashMap<String, PureExpr>> {
    match pattern {
        Pattern::Wildcard => Some(HashMap::new()),
        Pattern::Binding(name) => {
            let mut bindings = HashMap::new();
            bindings.insert(name.clone(), value.clone());
            Some(bindings)
        }
        Pattern::Alias { alias, pattern } => {
            let mut bindings = match_pattern_bindings(pattern, value)?;
            let mut alias_binding = HashMap::new();
            alias_binding.insert(alias.clone(), value.clone());
            merge_pattern_bindings(&mut bindings, alias_binding)?;
            Some(bindings)
        }
        Pattern::Literal(lit) => (lit == value).then(HashMap::new),
        Pattern::Constructor { name, inner } => {
            let PureExpr::LogicFnCall {
                name: ctor_name,
                args,
            } = value
            else {
                return None;
            };
            if ctor_name != name {
                return None;
            }

            match inner {
                None => args.is_empty().then(HashMap::new),
                Some(inner_pattern) => {
                    if args.len() == 1 {
                        return match_pattern_bindings(inner_pattern, &args[0]);
                    }
                    if let Pattern::Tuple(patterns) = inner_pattern.as_ref() {
                        if patterns.len() != args.len() {
                            return None;
                        }
                        let mut all_bindings = HashMap::new();
                        for (pattern_elem, value_elem) in patterns.iter().zip(args.iter()) {
                            let elem_bindings = match_pattern_bindings(pattern_elem, value_elem)?;
                            merge_pattern_bindings(&mut all_bindings, elem_bindings)?;
                        }
                        return Some(all_bindings);
                    }
                    None
                }
            }
        }
        Pattern::Tuple(patterns) => {
            let PureExpr::LogicFnCall { name, args } = value else {
                return None;
            };
            if tuple_logic_fn_arity(name) != Some(args.len()) || patterns.len() != args.len() {
                return None;
            }

            let mut all_bindings = HashMap::new();
            for (pattern_elem, value_elem) in patterns.iter().zip(args.iter()) {
                let elem_bindings = match_pattern_bindings(pattern_elem, value_elem)?;
                merge_pattern_bindings(&mut all_bindings, elem_bindings)?;
            }
            Some(all_bindings)
        }
        // Pattern is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => None,
    }
}

fn merge_pattern_bindings(
    target: &mut HashMap<String, PureExpr>,
    incoming: HashMap<String, PureExpr>,
) -> Option<()> {
    for (name, value) in incoming {
        if let Some(existing) = target.get(&name) {
            if existing != &value {
                return None;
            }
            continue;
        }
        target.insert(name, value);
    }
    Some(())
}
