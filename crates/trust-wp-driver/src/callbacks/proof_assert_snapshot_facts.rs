// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use crate::callbacks::proof_assert_extract::collapse_idempotent_views;

pub(in crate::callbacks) fn substitute_snapshot_facts(
    facts: &[PureExpr],
    local_substitutions: &HashMap<String, PureExpr>,
) -> Vec<PureExpr> {
    facts
        .iter()
        .map(|fact| {
            let preserved_final_carriers = fact_boundary_final_carrier_names(fact);
            let substituted = if local_substitutions.is_empty() {
                fact.clone()
            } else if preserved_final_carriers.is_empty() {
                fact.substitute(local_substitutions)
            } else {
                let filtered_substitutions: HashMap<String, PureExpr> = local_substitutions
                    .iter()
                    .filter(|(name, _)| !preserved_final_carriers.contains(*name))
                    .map(|(name, expr)| (name.clone(), expr.clone()))
                    .collect();
                fact.substitute(&filtered_substitutions)
            };
            collapse_idempotent_views(substituted)
        })
        .collect()
}

fn fact_boundary_final_carrier_names(fact: &PureExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    if let PureExpr::BinOp(lhs, _, rhs) = fact {
        if let Some(name) = bare_final_carrier_root_name(lhs) {
            names.insert(name.to_string());
        }
        if let Some(name) = bare_final_carrier_root_name(rhs) {
            names.insert(name.to_string());
        }
    }
    names
}

fn bare_final_carrier_root_name(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Final(inner) = expr else {
        return None;
    };
    final_carrier_root_name(inner)
}

fn final_carrier_root_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Final(inner) | PureExpr::Deref(inner) => final_carrier_root_name(inner),
        _ => None,
    }
}

pub(in crate::callbacks) fn collect_scalar_wrapper_aliases(
    facts: &[PureExpr],
) -> HashMap<String, PureExpr> {
    let mut aliases = HashMap::new();
    for fact in facts {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
            continue;
        };
        collect_scalar_wrapper_alias_from_side(lhs.as_ref(), rhs.as_ref(), &mut aliases);
        collect_scalar_wrapper_alias_from_side(rhs.as_ref(), lhs.as_ref(), &mut aliases);
    }
    aliases
}

pub(in crate::callbacks) fn derive_snapshot_deref_alias_substitutions(
    substitutions: &mut HashMap<String, PureExpr>,
    wrapper_aliases: &HashMap<String, PureExpr>,
) {
    if wrapper_aliases.is_empty() {
        return;
    }

    let snapshot = substitutions.clone();
    for (wrapper, scalar) in wrapper_aliases {
        substitutions
            .entry(format!("*{wrapper}"))
            .or_insert_with(|| scalar.clone());
    }
    for (name, expr) in snapshot {
        if let PureExpr::Var(wrapper, _) = expr {
            if let Some(alias) = wrapper_aliases.get(&wrapper) {
                substitutions
                    .entry(format!("*{name}"))
                    .or_insert_with(|| alias.clone());
            }
        }
    }
}

pub(in crate::callbacks) fn collect_deref_snapshot_aliases(
    expr: &PureExpr,
    facts: &[PureExpr],
) -> HashMap<String, PureExpr> {
    let mut deref_targets = HashSet::new();
    collect_deref_target_names(expr, &mut deref_targets);
    if deref_targets.is_empty() {
        return HashMap::new();
    }

    let mut aliases = HashMap::new();
    for fact in facts {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
            continue;
        };
        collect_deref_snapshot_alias_from_side(
            lhs.as_ref(),
            rhs.as_ref(),
            &deref_targets,
            &mut aliases,
        );
        collect_deref_snapshot_alias_from_side(
            rhs.as_ref(),
            lhs.as_ref(),
            &deref_targets,
            &mut aliases,
        );
    }
    aliases
}

pub(in crate::callbacks) fn substitute_assertion_final_carriers(
    assertion: &PureExpr,
    facts: &[PureExpr],
) -> PureExpr {
    let mut target_names = HashSet::new();
    collect_final_carrier_names(assertion, &mut target_names);
    if target_names.is_empty() {
        return assertion.clone();
    }

    let mut aliases = HashMap::new();
    for fact in facts {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
            continue;
        };
        collect_final_carrier_alias_from_side(
            lhs.as_ref(),
            rhs.as_ref(),
            &target_names,
            &mut aliases,
        );
        collect_final_carrier_alias_from_side(
            rhs.as_ref(),
            lhs.as_ref(),
            &target_names,
            &mut aliases,
        );
    }
    if aliases.is_empty() {
        return assertion.clone();
    }

    rewrite_final_carrier_expr(assertion, &aliases)
}

fn collect_scalar_wrapper_alias_from_side(
    wrapper_candidate: &PureExpr,
    scalar_candidate: &PureExpr,
    aliases: &mut HashMap<String, PureExpr>,
) {
    let PureExpr::Var(wrapper_name, wrapper_sort) = wrapper_candidate else {
        return;
    };
    if is_scalar_wrapper_alias_sort(wrapper_sort.as_ref()) {
        return;
    }
    if !is_scalar_wrapper_alias_expr(scalar_candidate) {
        return;
    }
    aliases
        .entry(wrapper_name.clone())
        .or_insert_with(|| scalar_candidate.clone());
}

fn is_scalar_wrapper_alias_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => true,
        PureExpr::Var(_, sort) => is_scalar_wrapper_alias_sort(sort.as_ref()),
        _ => false,
    }
}

fn is_scalar_wrapper_alias_sort(sort: Option<&ExprSort>) -> bool {
    matches!(
        sort,
        Some(ExprSort::Int | ExprSort::Bool | ExprSort::Float | ExprSort::Unit)
    )
}

fn collect_deref_snapshot_alias_from_side(
    wrapper_candidate: &PureExpr,
    alias_candidate: &PureExpr,
    deref_targets: &HashSet<String>,
    aliases: &mut HashMap<String, PureExpr>,
) {
    let PureExpr::Var(wrapper_name, _) = wrapper_candidate else {
        return;
    };
    if !deref_targets.contains(wrapper_name) {
        return;
    }
    aliases
        .entry(wrapper_name.clone())
        .or_insert_with(|| alias_candidate.clone());
}

fn collect_deref_target_names(expr: &PureExpr, targets: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Deref(inner) = node {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                targets.insert(name.clone());
            }
        }
    });
}

fn collect_final_carrier_names(expr: &PureExpr, targets: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Final(inner) = node {
            if let Some(name) = final_carrier_root_name(inner) {
                targets.insert(name.to_string());
            }
        }
    });
}

fn collect_final_carrier_alias_from_side(
    final_candidate: &PureExpr,
    alias_candidate: &PureExpr,
    targets: &HashSet<String>,
    aliases: &mut HashMap<String, PureExpr>,
) {
    let Some(name) = bare_final_carrier_root_name(final_candidate) else {
        return;
    };
    if !targets.contains(name) || wrapped_var_name(alias_candidate).is_some() {
        return;
    }
    let priority = final_carrier_alias_priority(alias_candidate);
    if aliases
        .get(name)
        .is_some_and(|existing| final_carrier_alias_priority(existing) >= priority)
    {
        return;
    }
    aliases.insert(name.to_string(), alias_candidate.clone());
}

fn final_carrier_alias_priority(expr: &PureExpr) -> u8 {
    match expr {
        PureExpr::MethodCall { .. } | PureExpr::LogicFnCall { .. } => 2,
        _ => 1,
    }
}

fn wrapped_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Final(inner) | PureExpr::Deref(inner) | PureExpr::View(inner) => {
            wrapped_var_name(inner)
        }
        _ => None,
    }
}

fn rewrite_final_carrier_expr(expr: &PureExpr, aliases: &HashMap<String, PureExpr>) -> PureExpr {
    match expr {
        PureExpr::Final(inner) => final_carrier_root_name(inner)
            .and_then(|name| aliases.get(name).cloned())
            .unwrap_or_else(|| {
                PureExpr::Final(std::sync::Arc::new(rewrite_final_carrier_expr(
                    inner, aliases,
                )))
            }),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: std::sync::Arc::new(rewrite_final_carrier_expr(receiver, aliases)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_final_carrier_expr(arg, aliases))
                .collect(),
        },
        PureExpr::BinOp(lhs, op, rhs) => PureExpr::BinOp(
            std::sync::Arc::new(rewrite_final_carrier_expr(lhs, aliases)),
            *op,
            std::sync::Arc::new(rewrite_final_carrier_expr(rhs, aliases)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            std::sync::Arc::new(rewrite_final_carrier_expr(inner, aliases)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(std::sync::Arc::new(rewrite_final_carrier_expr(
            inner, aliases,
        ))),
        PureExpr::View(inner) => PureExpr::View(std::sync::Arc::new(rewrite_final_carrier_expr(
            inner, aliases,
        ))),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            std::sync::Arc::new(rewrite_final_carrier_expr(cond, aliases)),
            std::sync::Arc::new(rewrite_final_carrier_expr(then_expr, aliases)),
            std::sync::Arc::new(rewrite_final_carrier_expr(else_expr, aliases)),
        ),
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_final_carrier_expr(arg, aliases))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: std::sync::Arc::new(rewrite_final_carrier_expr(body, aliases)),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|part| rewrite_final_carrier_expr(part, aliases))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: std::sync::Arc::new(rewrite_final_carrier_expr(body, aliases)),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|part| rewrite_final_carrier_expr(part, aliases))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: std::sync::Arc::new(rewrite_final_carrier_expr(scrutinee, aliases)),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rewrite_final_carrier_expr(&arm.body, aliases),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: std::sync::Arc::new(rewrite_final_carrier_expr(value, aliases)),
            body: std::sync::Arc::new(rewrite_final_carrier_expr(body, aliases)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: std::sync::Arc::new(rewrite_final_carrier_expr(assumption, aliases)),
            body: std::sync::Arc::new(rewrite_final_carrier_expr(body, aliases)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: std::sync::Arc::new(rewrite_final_carrier_expr(obligation, aliases)),
            body: std::sync::Arc::new(rewrite_final_carrier_expr(body, aliases)),
        },
        _ => expr.clone(),
    }
}
