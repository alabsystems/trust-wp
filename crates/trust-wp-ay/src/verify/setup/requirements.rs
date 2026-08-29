// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Goal analysis for verification setup.

use std::collections::HashSet;

use trust_wp_core::{
    formula::PureExpr,
    logic::{type_invariant_method_name, AdtDecls, LogicFnDef, LogicMode, TypeInvariantDef},
};

use crate::{
    error::EncodingError,
    expr::{
        collect_logic_fn_names, expr_has_bitwise_ops, expr_has_closure_spec_method,
        expr_has_datatype_spec_method, expr_has_match_constructor_pattern,
        expr_has_mut_ref_carrier, expr_has_tuple_fn, expr_has_uf_method_call,
        expr_needs_quantifiers,
    },
    expr_seq::{expr_has_seq_index_on_final, expr_has_seq_method_needing_quantifiers},
    logic::filter_logic_fn_indices_for_goal,
};

/// Check whether any expression in (requires, ensures, context_exprs) satisfies a predicate.
pub(crate) fn any_expr_matches(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
    pred: fn(&PureExpr) -> bool,
) -> bool {
    requires.iter().any(pred) || ensures.iter().any(pred) || context_exprs.iter().copied().any(pred)
}

fn expr_needs_custom_sorts(expr: &PureExpr) -> bool {
    expr_has_match_constructor_pattern(expr) || expr_has_datatype_spec_method(expr)
}

fn logic_fns_need_custom_sorts(filtered_logic_fns: Option<&[LogicFnDef]>) -> bool {
    filtered_logic_fns.is_some_and(|fns| {
        fns.iter().any(|logic_fn| {
            expr_needs_custom_sorts(logic_fn.body())
                || logic_fn.requires().iter().any(expr_needs_custom_sorts)
                || logic_fn.ensures().iter().any(expr_needs_custom_sorts)
        })
    })
}

fn type_invariants_need_custom_sorts(
    filtered_type_invariants: Option<&[TypeInvariantDef]>,
) -> bool {
    filtered_type_invariants.is_some_and(|invariants| {
        invariants
            .iter()
            .any(|inv| expr_needs_custom_sorts(inv.body()))
    })
}

fn expr_has_view_operator(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::View(_)))
}

fn any_goal_expr_has_view_operator(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
) -> bool {
    requires.iter().any(expr_has_view_operator)
        || ensures.iter().any(expr_has_view_operator)
        || context_exprs.iter().copied().any(expr_has_view_operator)
}

fn any_goal_expr_has_logic_fn_call(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
) -> bool {
    let mut names = HashSet::new();
    for expr in requires {
        collect_logic_fn_names(expr, &mut names);
    }
    for expr in ensures {
        collect_logic_fn_names(expr, &mut names);
    }
    for expr in context_exprs {
        collect_logic_fn_names(expr, &mut names);
    }
    !names.is_empty()
}

fn is_direct_view_filter_candidate(logic_fn: &LogicFnDef, _effective_mode: LogicMode) -> bool {
    logic_fn.name() == "view"
        && logic_fn.params().len() == 1
        && logic_fn.requires().is_empty()
        && !logic_fn.is_opaque()
        && crate::expr::expr_mentions_var(logic_fn.body(), &logic_fn.params()[0])
}

fn is_view_return_sort_filter_candidate(logic_fn: &LogicFnDef) -> bool {
    logic_fn.name() == "view" && logic_fn.params().len() == 1 && logic_fn.return_sort().is_some()
}

/// Detect whether the contract expressions require quantifier-capable,
/// array-capable, or custom-sort (ALL) logic, returning
/// `(use_quantifiers, needs_array_theory, needs_custom_sorts)`.
pub(crate) fn detect_logic_requirements(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
    filtered_logic_fns: Option<&[LogicFnDef]>,
    filtered_type_invariants: Option<&[TypeInvariantDef]>,
    adt_decls: Option<&AdtDecls>,
) -> (bool, bool, bool) {
    let has_logic_fns = filtered_logic_fns.is_some_and(|fns| !fns.is_empty());
    let needs_quantifiers =
        any_expr_matches(requires, ensures, context_exprs, expr_needs_quantifiers);
    let has_closure_specs = any_expr_matches(
        requires,
        ensures,
        context_exprs,
        expr_has_closure_spec_method,
    );
    let has_tuple_fns = any_expr_matches(requires, ensures, context_exprs, expr_has_tuple_fn);
    let has_datatype_specs = any_expr_matches(
        requires,
        ensures,
        context_exprs,
        expr_has_datatype_spec_method,
    );
    // Match expressions with Constructor patterns (Some/None/Ok/Err) trigger
    // native ay datatype declarations which require a logic beyond QF_LIA. (#1055)
    let has_match_constructors = any_expr_matches(
        requires,
        ensures,
        context_exprs,
        expr_has_match_constructor_pattern,
    );
    let has_type_invariants = filtered_type_invariants.is_some_and(|invs| !invs.is_empty());
    let logic_fn_custom_sorts = logic_fns_need_custom_sorts(filtered_logic_fns);
    let type_invariant_custom_sorts = type_invariants_need_custom_sorts(filtered_type_invariants);
    // Seq methods (push_back, push_front, reverse, contains, etc.) trigger
    // quantified axioms and require Array theory. Parity with loop path
    // in loops/mod.rs. (#1919)
    let has_seq_methods = any_expr_matches(
        requires,
        ensures,
        context_exprs,
        expr_has_seq_method_needing_quantifiers,
    );
    // Bitwise operators (Shl/Shr/BitAnd/BitXor/BitOr) are encoded via
    // `encode_int_binop_uf` which declares UFs and `assert_bitwise_axioms`
    // which injects forall-quantified axioms. (#1922)
    let has_bitwise_ops = any_expr_matches(requires, ensures, context_exprs, expr_has_bitwise_ops);
    // FSet/FMap methods, ext_eq, produces, deep_model, etc. inject UFs
    // during encoding without being caught by other detection predicates. (#1923)
    let has_uf_methods =
        any_expr_matches(requires, ensures, context_exprs, expr_has_uf_method_call);
    let has_mut_ref_carriers =
        any_expr_matches(requires, ensures, context_exprs, expr_has_mut_ref_carrier);

    // IndexMut postconditions with Seq index on Final receivers will trigger
    // SeqValue synthesis (store/select), requiring Array theory. (#1317)
    // Seq methods also need Array theory for store/select shape constraints. (#1581, #1919)
    let needs_array_theory = has_seq_methods
        || any_expr_matches(
            requires,
            ensures,
            context_exprs,
            expr_has_seq_index_on_final,
        );
    let has_logic_fn_calls = any_goal_expr_has_logic_fn_call(requires, ensures, context_exprs);
    // QF_AUFLIA already supports uninterpreted functions. A bare method/logic
    // call only needs the quantifier-capable UFLIA fallback when no array logic
    // is otherwise selected. Registered logic functions still force
    // quantifier-capable logic through `has_logic_fns` for their defining
    // axioms. (#1596, #2520)
    let has_logic_fn_calls_requiring_uflia = has_logic_fn_calls && !needs_array_theory;

    // Bool-sorted context expressions (final_values, return_expr) previously
    // forced UFLIA to work around ay-dpll's `try_assert_named` breaking Bool
    // SAT model generation (#2141). The axiom-free probe now uses
    // AssertionPhase::Other (unnamed assertions) to avoid that ay-dpll
    // limitation, making the logic-level upgrade unnecessary. (#2141, #2520)

    let use_quantifiers = has_logic_fns
        || needs_quantifiers
        || has_closure_specs
        || has_tuple_fns
        || has_datatype_specs
        || has_match_constructors
        || has_type_invariants
        || has_seq_methods
        || has_bitwise_ops
        || has_uf_methods
        || has_logic_fn_calls_requiring_uflia
        || has_mut_ref_carriers;

    // Custom sorts (datatypes) require Logic::All for ay's auto-theory
    // detection. AUFLIA/UFLIA lack native datatype theory support and may
    // return Unknown when datatype constructors interact with quantifier
    // instantiation. This applies both to the goal expressions themselves and
    // to the filtered logic-function/type-invariant definitions that bootstrap
    // will register before solving. (#994, #1944)
    let needs_custom_sorts = has_match_constructors
        || has_datatype_specs
        || logic_fn_custom_sorts
        || type_invariant_custom_sorts
        || adt_decls.is_some_and(|decls| !decls.is_empty());

    (use_quantifiers, needs_array_theory, needs_custom_sorts)
}

#[allow(clippy::type_complexity)]
pub(crate) fn filter_logic_functions_for_goal(
    logic_fns: Option<&[LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
) -> Result<(Option<Vec<LogicFnDef>>, Option<Vec<LogicMode>>), EncodingError> {
    match logic_fns {
        Some(fns) => {
            // Silently drop mode_overrides when lengths don't match (#2316, #2700).
            // mode_overrides is computed from the full logic_fn_defs set, but
            // logic_fns may be a filtered subset from the driver. Rather than
            // returning an encoding error (which aborts verification entirely),
            // drop the overrides and fall back to default mode scoping. The loss
            // of scoping is preferable to a hard failure.
            let effective_modes = match mode_overrides {
                Some(modes) if modes.len() != fns.len() => {
                    tracing::debug!(
                        modes_len = modes.len(),
                        fns_len = fns.len(),
                        "mode_overrides length mismatch — dropping overrides (#2316)"
                    );
                    None
                }
                other => other,
            };

            let mut names = HashSet::new();
            for req in requires {
                collect_logic_fn_names(req, &mut names);
            }
            for ens in ensures {
                collect_logic_fn_names(ens, &mut names);
            }
            for expr in context_exprs {
                collect_logic_fn_names(expr, &mut names);
            }

            let mut indices = filter_logic_fn_indices_for_goal(fns, &names);
            if any_goal_expr_has_view_operator(requires, ensures, context_exprs) {
                for (i, logic_fn) in fns.iter().enumerate() {
                    let mode = effective_modes
                        .and_then(|modes| modes.get(i).copied())
                        .unwrap_or_else(|| logic_fn.mode());
                    if is_direct_view_filter_candidate(logic_fn, mode)
                        || is_view_return_sort_filter_candidate(logic_fn)
                    {
                        indices.push(i);
                    }
                }
                indices.sort_unstable();
                indices.dedup();
            }
            let filtered: Vec<_> = indices
                .iter()
                .map(|&i| {
                    let mut logic_fn = fns[i].clone();
                    if let Some(modes) = effective_modes {
                        logic_fn.set_mode(modes[i]);
                    }
                    logic_fn
                })
                .collect();
            let filtered_modes =
                effective_modes.map(|modes| indices.iter().map(|&i| modes[i]).collect());
            Ok((Some(filtered), filtered_modes))
        }
        None => Ok((None, None)),
    }
}

pub(crate) fn formula_exprs_with_type_invariant_bodies(
    formula_exprs: &[PureExpr],
    filtered_type_invariants: Option<&[TypeInvariantDef]>,
) -> Vec<PureExpr> {
    let extra = filtered_type_invariants.map_or(0, <[TypeInvariantDef]>::len);
    let mut exprs = Vec::with_capacity(formula_exprs.len() + extra);
    exprs.extend_from_slice(formula_exprs);
    if let Some(invariants) = filtered_type_invariants {
        exprs.extend(invariants.iter().map(|inv| inv.body().clone()));
    }
    exprs
}

pub(crate) fn filter_type_invariants_for_goal(
    type_invariants: Option<&[TypeInvariantDef]>,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
) -> Option<Vec<TypeInvariantDef>> {
    let invariants = type_invariants?;

    let mut needed_method_names = HashSet::new();
    for req in requires {
        collect_logic_fn_names(req, &mut needed_method_names);
    }
    for ens in ensures {
        collect_logic_fn_names(ens, &mut needed_method_names);
    }
    for expr in context_exprs {
        collect_logic_fn_names(expr, &mut needed_method_names);
    }

    // When the unqualified name "invariant" appears, keep every available
    // type-invariant definition. The encoder can later resolve the call to a
    // type-qualified `__trust_wp_invariant_<Type>` UF from receiver sort context;
    // filtering nontrivial definitions here leaves that resolved UF
    // unconstrained and can turn missing axioms into spurious counterexamples.
    // Registering extra definitions is sound: unused qualified UFs do not add
    // facts about program values, and used UFs receive their actual bodies.
    let retain_all = needed_method_names.contains("invariant");

    let mut selected: Vec<TypeInvariantDef> = invariants
        .iter()
        .filter(|inv| {
            retain_all || needed_method_names.contains(&type_invariant_method_name(inv.type_name()))
        })
        .cloned()
        .collect();

    if selected.is_empty() {
        return Some(Vec::new());
    }

    // Keep element-invariant dependencies closed so container invariants that
    // reference element invariants can still be expanded in the same query.
    let mut selected_methods: HashSet<String> = selected
        .iter()
        .map(|inv| type_invariant_method_name(inv.type_name()))
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        let deps: Vec<String> = selected
            .iter()
            .filter_map(|inv| inv.element_invariant_method().map(str::to_string))
            .collect();
        for dep in deps {
            if !selected_methods.insert(dep.clone()) {
                continue;
            }
            if let Some(dep_inv) = invariants
                .iter()
                .find(|inv| type_invariant_method_name(inv.type_name()) == dep)
            {
                selected.push(dep_inv.clone());
                changed = true;
            }
        }
    }

    Some(selected)
}
