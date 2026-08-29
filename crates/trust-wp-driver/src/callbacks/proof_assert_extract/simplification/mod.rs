// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression simplification and type/field rewrites for proof_assert.
//!
//! Simplifies tautological expressions before SMT encoding, applies
//! type invariant method rewrites, struct field access normalization,
//! and static match elimination for concrete constructor scrutinees.
//!
//! Decomposed from a single 1358-line file (#1988):
//! - `match_reduction`: Static match elimination for concrete constructors
//! - `constructor_methods`: Constructor method call reduction and boolean folding
//! - `tests`: Comprehensive test suite for all simplification passes

mod constructor_methods;
mod match_reduction;
#[cfg(test)]
mod tests;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub(in crate::callbacks) use constructor_methods::reduce_concrete_constructor_method_calls;
use match_reduction::extract_constructor;
pub(in crate::callbacks) use match_reduction::reduce_concrete_matches;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::super::{
    contract_rewrite::{annotate_expr_with_param_sorts, rewrite_named_field_access_expr},
    struct_field_map::build_struct_field_map,
    type_invariants::{
        build_type_invariant_method_map, build_type_invariant_structural_expr_map,
        rewrite_type_invariant_methods_expr_with_structural,
    },
};

/// Check whether a variable name appears free (unbound) in an expression.
///
/// Used by quantifier simplification to verify that a bound variable does not
/// appear in a sub-expression, enabling tautology rewrites like
/// `exists<y> (e == y) → true` when `y ∉ FV(e)`.
fn contains_free_var(expr: &PureExpr, var_name: &str) -> bool {
    expr.any_free_var(|name, _| name == var_name)
}

/// Simplify tautological proof_assert expressions before SMT encoding.
///
/// This pass is intentionally conservative and only applies sound rewrites:
/// - `p ==> p` → `true`
/// - `x == x` → `true`
/// - `forall<...> true` / `forall<...> false` → body constant
/// - `exists<...> true` / `exists<...> false` → body constant
/// - `exists<y> (e == y)` / `exists<y> (y == e)` → `true` when `y ∉ FV(e)`
///
/// In SMT-LIB, all sorts are non-empty, so quantifier elimination on constant
/// bodies is semantics-preserving. The existential witness rule is a standard
/// first-order logic tautology: for any term `t`, `∃y. (t = y)` is true
/// (witnessed by `y = t`). (#2209)
pub(in crate::callbacks) fn simplify_proof_assert_expr(expr: PureExpr) -> PureExpr {
    match expr {
        PureExpr::BinOp(left, op, right) => {
            if matches!(op, BinOp::Implies | BinOp::Eq) && left == right {
                PureExpr::Bool(true)
            } else {
                PureExpr::BinOp(left, op, right)
            }
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => match simplify_proof_assert_expr(Arc::unwrap_or_clone(body)) {
            PureExpr::Bool(value) => PureExpr::Bool(value),
            body => PureExpr::Forall {
                var,
                var_sort,
                body: Arc::new(body),
                triggers,
            },
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => match simplify_proof_assert_expr(Arc::unwrap_or_clone(body)) {
            PureExpr::Bool(value) => PureExpr::Bool(value),
            // exists<y> (e == y) → true when y ∉ FV(e) (existential witness tautology)
            PureExpr::BinOp(ref left, BinOp::Eq, ref right) => {
                let is_tautology = match (left.as_ref(), right.as_ref()) {
                    (_, PureExpr::Var(name, _)) if name == &var => !contains_free_var(left, &var),
                    (PureExpr::Var(name, _), _) if name == &var => !contains_free_var(right, &var),
                    _ => false,
                };
                if is_tautology {
                    PureExpr::Bool(true)
                } else {
                    PureExpr::Exists {
                        var,
                        var_sort,
                        body: Arc::new(PureExpr::BinOp(left.clone(), BinOp::Eq, right.clone())),
                        triggers,
                    }
                }
            }
            body => PureExpr::Exists {
                var,
                var_sort,
                body: Arc::new(body),
                triggers,
            },
        },
        other => other,
    }
}

/// Synthesize constructor equalities from tester+selector fact pairs.
///
/// After implication-style spec postconditions are reduced, we may have:
/// - Tester facts: `x.is_err()`, `x.is_some()`, `x.is_none()`, etc.
/// - Selector facts: `x.unwrap_err() == v`, `x.unwrap() == v`, etc.
///
/// The assertion may use constructor comparisons: `x == Err(v)`.
///
/// Without constructor-tester-selector axioms in the solver, the connection
/// between `x.is_err() ∧ x.unwrap_err() == v` and `x == Err(v)` is lost.
///
/// This pass scans assumed facts for such patterns and synthesizes the
/// corresponding constructor equalities:
/// - `x.is_some() ∧ x.unwrap() == v` → add `x == Some(v)`
/// - `x.is_none()` → add `x == None()`
/// - `x.is_ok() ∧ x.unwrap() == v` → add `x == Ok(v)`
/// - `x.is_err() ∧ x.unwrap_err() == v` → add `x == Err(v)`
///
/// Sound: these are direct consequences of ADT datatype theory axioms. (#2675)
pub(in crate::callbacks) fn synthesize_constructor_equalities(facts: &[PureExpr]) -> Vec<PureExpr> {
    // Phase 1: Collect tester facts (x.is_some(), x.is_err(), etc.)
    // and selector facts (x.unwrap() == v, x.unwrap_err() == v).
    //
    // Key: (variable Display string, tester kind)
    // We use Display because PureExpr doesn't implement Hash.
    let mut testers: HashSet<(String, &str)> = HashSet::new();
    // Key: (variable Display string, selector kind) → value expression
    let mut selectors: HashMap<(String, &str), PureExpr> = HashMap::new();
    // Map from Display string → actual PureExpr for reconstruction
    let mut var_exprs: HashMap<String, PureExpr> = HashMap::new();

    for fact in facts {
        // Tester pattern: x.is_some(), x.is_none(), x.is_ok(), x.is_err()
        // After reduction, these appear as Bool(true) only if the receiver was
        // concrete. For non-concrete receivers, the tester fact appears as the
        // method call itself (when the implication was reduced to the consequent).
        if let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = fact
        {
            if args.is_empty() {
                let key = format!("{receiver}");
                match method.as_str() {
                    "is_some" | "is_none" | "is_ok" | "is_err" => {
                        testers.insert((key.clone(), method.as_str()));
                        var_exprs
                            .entry(key)
                            .or_insert_with(|| receiver.as_ref().clone());
                    }
                    _ => {}
                }
            }
        }

        // Selector pattern: x.unwrap() == v or x.unwrap_err() == v
        // (and symmetric: v == x.unwrap())
        if let PureExpr::BinOp(left, BinOp::Eq, right) = fact {
            // left = x.method(), right = v
            if let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = left.as_ref()
            {
                if args.is_empty() {
                    let key = format!("{receiver}");
                    match method.as_str() {
                        "unwrap" | "unwrap_err" => {
                            selectors
                                .entry((key.clone(), method.as_str()))
                                .or_insert_with(|| right.as_ref().clone());
                            var_exprs
                                .entry(key)
                                .or_insert_with(|| receiver.as_ref().clone());
                        }
                        _ => {}
                    }
                }
            }
            // Symmetric: v == x.method()
            if let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = right.as_ref()
            {
                if args.is_empty() {
                    let key = format!("{receiver}");
                    match method.as_str() {
                        "unwrap" | "unwrap_err" => {
                            selectors
                                .entry((key.clone(), method.as_str()))
                                .or_insert_with(|| left.as_ref().clone());
                            var_exprs
                                .entry(key)
                                .or_insert_with(|| receiver.as_ref().clone());
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // Phase 2: Synthesize constructor equalities from tester+selector pairs.
    let mut synthesized = Vec::new();

    for (var_key, tester) in &testers {
        let var_expr = match var_exprs.get(var_key) {
            Some(e) => e,
            None => continue,
        };

        match *tester {
            "is_none" => {
                // x.is_none() → x == None()
                synthesized.push(PureExpr::BinOp(
                    Arc::new(var_expr.clone()),
                    BinOp::Eq,
                    Arc::new(PureExpr::LogicFnCall {
                        name: "None".to_string(),
                        args: vec![],
                    }),
                ));
            }
            "is_some" => {
                // x.is_some() ∧ x.unwrap() == v → x == Some(v)
                if let Some(value) = selectors.get(&(var_key.clone(), "unwrap")) {
                    synthesized.push(PureExpr::BinOp(
                        Arc::new(var_expr.clone()),
                        BinOp::Eq,
                        Arc::new(PureExpr::LogicFnCall {
                            name: "Some".to_string(),
                            args: vec![value.clone()],
                        }),
                    ));
                }
            }
            "is_ok" => {
                // x.is_ok() ∧ x.unwrap() == v → x == Ok(v)
                if let Some(value) = selectors.get(&(var_key.clone(), "unwrap")) {
                    synthesized.push(PureExpr::BinOp(
                        Arc::new(var_expr.clone()),
                        BinOp::Eq,
                        Arc::new(PureExpr::LogicFnCall {
                            name: "Ok".to_string(),
                            args: vec![value.clone()],
                        }),
                    ));
                }
            }
            "is_err" => {
                // x.is_err() ∧ x.unwrap_err() == v → x == Err(v)
                if let Some(value) = selectors.get(&(var_key.clone(), "unwrap_err")) {
                    synthesized.push(PureExpr::BinOp(
                        Arc::new(var_expr.clone()),
                        BinOp::Eq,
                        Arc::new(PureExpr::LogicFnCall {
                            name: "Err".to_string(),
                            args: vec![value.clone()],
                        }),
                    ));
                }
            }
            _ => {}
        }
    }

    synthesized
}

/// Apply constructor equality substitutions from assumed facts to an expression.
///
/// Scans assumed facts for patterns `var == Constructor(...)` or
/// `Constructor(...) == var`, substitutes the variable with the constructor
/// in the target expression, then re-runs `reduce_concrete_matches` on the
/// result. This resolves match expressions like:
///
/// ```text
/// assumed_fact: result == Ok(call_2)
/// assertion: match result { Ok(i) => i < 5, Err(_) => false }
/// →
/// assertion: match Ok(call_2) { Ok(i) => i < 5, Err(_) => false }
/// → (reduce_concrete_matches)
/// assertion: call_2 < 5
/// ```
///
/// The pass also applies constructor equalities to other assumed facts,
/// enabling cross-fact simplification. (#2675)
pub(in crate::callbacks) fn apply_constructor_equality_substitutions(
    expr: PureExpr,
    assumed_facts: &[PureExpr],
) -> PureExpr {
    let mut substitutions = HashMap::new();

    for fact in assumed_facts {
        if let PureExpr::BinOp(left, BinOp::Eq, right) = fact {
            // var == Constructor(...)
            if let Some(name) = binding_name(left) {
                if extract_constructor(right).is_some() {
                    substitutions
                        .entry(name)
                        .or_insert_with(|| (**right).clone());
                }
            }
            // Constructor(...) == var
            if let Some(name) = binding_name(right) {
                if extract_constructor(left).is_some() {
                    substitutions
                        .entry(name)
                        .or_insert_with(|| (**left).clone());
                }
            }
        }
    }

    if substitutions.is_empty() {
        return expr;
    }

    let substituted = expr.substitute(&substitutions);
    reduce_concrete_constructor_method_calls(reduce_concrete_matches(substituted))
}

/// Apply constructor equality substitutions across assumed facts.
///
/// This is the fact-level companion to `apply_constructor_equality_substitutions`.
/// It handles postcondition facts such as:
///
/// ```text
/// assumed facts:
///   result == Ok(call_2)
///   match result { Ok(i) => i < len, Err(_) => true }
/// ```
///
/// The match fact can be reduced to the selected branch before solver
/// dispatch, avoiding a quantifier-heavy datatype/selector proof.
pub(in crate::callbacks) fn apply_constructor_equality_substitutions_to_facts(
    facts: &[PureExpr],
) -> (Vec<PureExpr>, usize) {
    let mut reduced_count = 0usize;
    let mut out = Vec::new();
    for fact in facts {
        push_unique_fact(&mut out, fact.clone());
        let reduced = apply_constructor_equality_substitutions(fact.clone(), facts);
        if reduced != *fact && !is_trivially_true_fact(&reduced) {
            reduced_count += 1;
            push_unique_fact(&mut out, reduced.clone());
            for conjunct in top_level_conjuncts(&reduced) {
                if conjunct != reduced && !is_trivially_true_fact(&conjunct) {
                    push_unique_fact(&mut out, conjunct);
                }
            }
        }
    }
    (out, reduced_count)
}

/// Instantiate facts by applying simple ground equalities already present in
/// proof-assert preconditions or facts.
///
/// This is intentionally narrow: it rewrites exact, non-quantified terms to
/// integer or boolean literals. For example, from `s@.len() == 5` and the
/// reduced binary-search fact `call_2 < s@.len()`, it adds `call_2 < 5` so the
/// proof assertion can be discharged syntactically instead of relying on a
/// proof-checker path with trusted LRA fallback steps.
pub(in crate::callbacks) fn synthesize_ground_equality_substitution_facts(
    equality_sources: &[PureExpr],
    facts: &[PureExpr],
) -> Vec<PureExpr> {
    let substitutions = collect_literal_term_equalities(equality_sources);
    if substitutions.is_empty() {
        return Vec::new();
    }

    let mut out = Vec::new();
    for fact in facts {
        let rewritten = rewrite_exact_terms(fact, &substitutions);
        if rewritten != *fact && !is_trivially_true_fact(&rewritten) {
            push_unique_fact(&mut out, rewritten.clone());
            for conjunct in top_level_conjuncts(&rewritten) {
                if conjunct != rewritten && !is_trivially_true_fact(&conjunct) {
                    push_unique_fact(&mut out, conjunct);
                }
            }
        }
    }
    out
}

fn collect_literal_term_equalities(sources: &[PureExpr]) -> Vec<(PureExpr, PureExpr)> {
    let mut substitutions = Vec::new();
    for source in sources {
        collect_literal_term_equalities_from_expr(source, &mut substitutions);
    }
    substitutions
}

fn collect_literal_term_equalities_from_expr(
    expr: &PureExpr,
    substitutions: &mut Vec<(PureExpr, PureExpr)>,
) {
    match expr {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if is_literal(right) && is_rewritable_term(left) {
                substitutions.push((left.as_ref().clone(), right.as_ref().clone()));
            } else if is_literal(left) && is_rewritable_term(right) {
                substitutions.push((right.as_ref().clone(), left.as_ref().clone()));
            }
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_literal_term_equalities_from_expr(left, substitutions);
            collect_literal_term_equalities_from_expr(right, substitutions);
        }
        _ => {}
    }
}

fn rewrite_exact_terms(expr: &PureExpr, substitutions: &[(PureExpr, PureExpr)]) -> PureExpr {
    expr.rewrite_bottom_up_prune(
        |node| {
            !matches!(
                node,
                PureExpr::Forall { .. } | PureExpr::Exists { .. } | PureExpr::Closure { .. }
            )
        },
        |node| {
            substitutions
                .iter()
                .find_map(|(from, to)| {
                    if &node == from {
                        Some(to.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or(node)
        },
    )
}

fn is_literal(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Int(_) | PureExpr::Bool(_))
}

fn is_rewritable_term(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { .. }
            | PureExpr::LogicFnCall { .. }
            | PureExpr::View(_)
            | PureExpr::Deref(_)
            | PureExpr::Old(_)
            | PureExpr::Final(_)
    )
}

fn top_level_conjuncts(expr: &PureExpr) -> Vec<PureExpr> {
    let mut out = Vec::new();
    collect_top_level_conjuncts(expr, &mut out);
    out
}

fn collect_top_level_conjuncts(expr: &PureExpr, out: &mut Vec<PureExpr>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_top_level_conjuncts(left, out);
            collect_top_level_conjuncts(right, out);
        }
        _ => out.push(expr.clone()),
    }
}

fn push_unique_fact(facts: &mut Vec<PureExpr>, fact: PureExpr) {
    if !facts.contains(&fact) {
        facts.push(fact);
    }
}

fn is_trivially_true_fact(fact: &PureExpr) -> bool {
    match fact {
        PureExpr::Bool(true) => true,
        PureExpr::BinOp(left, BinOp::Eq, right) => left == right,
        _ => false,
    }
}

/// If a constructor equality is wrapped in `Old(...)` on the binding side,
/// also expose current-value and, for call-result aliases, upgraded versions
/// of the equality.
///
/// This keeps the original snapshot fact intact while making the constructor
/// bridge available to proof-assert slices that reason over the live result
/// alias.
pub(in crate::callbacks) fn normalize_old_constructor_equality_facts(
    fact: &PureExpr,
) -> Vec<PureExpr> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return Vec::new();
    };

    let mut facts = Vec::new();
    match (left.as_ref(), right.as_ref()) {
        (PureExpr::Old(inner), rhs) if extract_constructor(rhs).is_some() => {
            facts.push(PureExpr::BinOp(
                Arc::new(inner.as_ref().clone()),
                BinOp::Eq,
                Arc::new(rhs.clone()),
            ));
            if let PureExpr::Var(name, _) = inner.as_ref() {
                if let Some(upgraded) = call_result_upgrade_name(name) {
                    facts.push(PureExpr::BinOp(
                        Arc::new(PureExpr::Var(upgraded, None)),
                        BinOp::Eq,
                        Arc::new(rhs.clone()),
                    ));
                }
            }
        }
        (lhs, PureExpr::Old(inner)) if extract_constructor(lhs).is_some() => {
            facts.push(PureExpr::BinOp(
                Arc::new(lhs.clone()),
                BinOp::Eq,
                Arc::new(inner.as_ref().clone()),
            ));
            if let PureExpr::Var(name, _) = inner.as_ref() {
                if let Some(upgraded) = call_result_upgrade_name(name) {
                    facts.push(PureExpr::BinOp(
                        Arc::new(lhs.clone()),
                        BinOp::Eq,
                        Arc::new(PureExpr::Var(upgraded, None)),
                    ));
                }
            }
        }
        _ => {}
    }
    facts
}

/// Expand a constructor equality into the corresponding tester/selector facts.
///
/// This is the forward bridge used by proof_assert slices that need the
/// tester form (`x.is_ok()`) or selector form (`x.unwrap() == v`) rather than
/// the raw constructor equality.
pub(in crate::callbacks) fn constructor_equality_to_tester_selector_facts(
    fact: &PureExpr,
) -> Vec<PureExpr> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return Vec::new();
    };

    let Some((var, ctor_name, ctor_args)) = constructor_binding(left, right) else {
        let Some((var, ctor_name, ctor_args)) = constructor_binding(right, left) else {
            return Vec::new();
        };
        return constructor_tester_selector_facts(var, ctor_name, ctor_args);
    };

    constructor_tester_selector_facts(var, ctor_name, ctor_args)
}

fn constructor_binding<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
) -> Option<(PureExpr, &'a str, &'a [PureExpr])> {
    let PureExpr::Var(_, _) = candidate else {
        return None;
    };
    let (ctor_name, ctor_args) = extract_constructor(other)?;
    Some((candidate.clone(), ctor_name, ctor_args))
}

fn constructor_tester_selector_facts(
    var: PureExpr,
    ctor_name: &str,
    ctor_args: &[PureExpr],
) -> Vec<PureExpr> {
    let PureExpr::Var(var_name, _) = var else {
        return Vec::new();
    };

    let receiver = PureExpr::Var(var_name, None);
    match (ctor_name, ctor_args) {
        ("Some", [arg]) => vec![
            PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "is_some".to_string(),
                args: vec![],
            },
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(receiver),
                    method: "unwrap".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(arg.clone()),
            ),
        ],
        ("None", []) => vec![PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "is_none".to_string(),
            args: vec![],
        }],
        ("Ok", [arg]) => vec![
            PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "is_ok".to_string(),
                args: vec![],
            },
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(receiver),
                    method: "unwrap".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(arg.clone()),
            ),
        ],
        ("Err", [arg]) => vec![
            PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "is_err".to_string(),
                args: vec![],
            },
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(receiver),
                    method: "unwrap_err".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(arg.clone()),
            ),
        ],
        _ => Vec::new(),
    }
}

fn call_result_upgrade_name(name: &str) -> Option<String> {
    if name.starts_with("call_") || name.starts_with("_call_") {
        Some(format!("{name}__upgraded"))
    } else {
        None
    }
}

fn binding_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(name.clone()),
        PureExpr::Old(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Apply type invariant method rewrites and struct field access normalization.
///
/// Rewrites `Type::invariant(x)` calls to their expanded predicate form in both
/// the assertion and preconditions, injects type invariant clauses as additional
/// preconditions, and normalizes named struct field access (`__trust_wp_field_a`)
/// to positional tuple-get calls (`__trust_wp_tuple_get_0`). (#1572)
pub(in crate::callbacks) fn apply_type_and_field_rewrites(
    tcx: TyCtxt<'_>,
    containing_def_id: DefId,
    contract_arg_names: &[String],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
    verbose: bool,
    assertion: &mut PureExpr,
    preconditions: &mut Vec<PureExpr>,
) {
    let (param_invariant_methods, result_invariant_method) = build_type_invariant_method_map(
        tcx,
        containing_def_id,
        contract_arg_names,
        type_invariant_defs,
    );
    let (param_structural_exprs, result_structural_expr) = build_type_invariant_structural_expr_map(
        tcx,
        containing_def_id,
        contract_arg_names,
        type_invariant_defs,
    );
    if !param_invariant_methods.is_empty()
        || result_invariant_method.is_some()
        || !param_structural_exprs.is_empty()
        || result_structural_expr.is_some()
    {
        *assertion = rewrite_type_invariant_methods_expr_with_structural(
            assertion,
            &param_invariant_methods,
            result_invariant_method.as_deref(),
            &param_structural_exprs,
            result_structural_expr.as_ref(),
        );
        *preconditions = preconditions
            .iter()
            .map(|expr| {
                rewrite_type_invariant_methods_expr_with_structural(
                    expr,
                    &param_invariant_methods,
                    result_invariant_method.as_deref(),
                    &param_structural_exprs,
                    result_structural_expr.as_ref(),
                )
            })
            .collect();
    }

    // Rewrite named struct field access to positional tuple-get calls (#1572).
    let struct_field_map = build_struct_field_map(tcx, containing_def_id);
    if !struct_field_map.is_empty() {
        *assertion = rewrite_named_field_access_expr(assertion, &struct_field_map);
        for pre in preconditions.iter_mut() {
            *pre = rewrite_named_field_access_expr(pre, &struct_field_map);
        }
        if verbose {
            debug!(
                "trust-wp:   (proof_assert: {} named field(s) rewritten to positional access)",
                struct_field_map.len()
            );
        }
    }

    *assertion =
        annotate_expr_with_param_sorts(tcx, containing_def_id, contract_arg_names, assertion);
    for pre in preconditions.iter_mut() {
        *pre = annotate_expr_with_param_sorts(tcx, containing_def_id, contract_arg_names, pre);
    }
}
