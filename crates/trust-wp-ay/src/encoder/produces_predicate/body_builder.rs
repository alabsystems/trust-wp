// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PureExpr body builder for logical FMapIter `produces` decomposition.
//!
//! Contains:
//! - PureExpr helper constructors (method_call, logic_fn_call, etc.)
//! - FMapIter sort detection helpers
//! - [`build_logical_fmap_iter_body`]: constructs the partition predicate body

use std::sync::Arc;

use trust_wp_core::formula::{
    intern_sort_name, internal::tuple_lowering::tuple_field_logic_fn_name, resolve_sort_name,
    BinOp, ExprSort, PureExpr, UnOp,
};

pub(super) const FMAP_ITER_VIEW_LOGIC_FN: &str = "__trust_wp_fmap_iter_view";
pub(super) const LOGICAL_FMAP_ITER_SORT_NAMES: &[&str] = &[
    "trust_wp_std::logic::fmap::FMapIter",
    "creusot_std::logic::fmap::Iter",
    "logic::fmap::Iter",
];

// ── PureExpr constructors ──────────────────────────────────────────

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn logic_fn_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

fn view_projector(receiver: PureExpr) -> PureExpr {
    logic_fn_call(FMAP_ITER_VIEW_LOGIC_FN, vec![receiver])
}

fn tuple_get(index: usize, tuple: PureExpr) -> PureExpr {
    logic_fn_call(&tuple_field_logic_fn_name(index), vec![tuple])
}

fn contains(receiver: PureExpr, arg: PureExpr) -> PureExpr {
    method_call(receiver, "contains", vec![arg])
}

fn lookup(receiver: PureExpr, key: PureExpr) -> PureExpr {
    method_call(receiver, "lookup", vec![key])
}

fn len(receiver: PureExpr) -> PureExpr {
    method_call(receiver, "len", vec![])
}

fn deep_model(receiver: PureExpr) -> PureExpr {
    method_call(receiver, "deep_model", vec![])
}

fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
}

fn or(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs))
}

fn add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs))
}

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn implies(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
}

fn not(expr: PureExpr) -> PureExpr {
    PureExpr::UnOp(UnOp::Not, Arc::new(expr))
}

fn fold_and(mut clauses: Vec<PureExpr>) -> PureExpr {
    let first = clauses
        .drain(..1)
        .next()
        .expect("fold_and requires at least one clause");
    clauses.into_iter().fold(first, and)
}

// ── FMapIter sort detection ────────────────────────────────────────

fn root_datatype_sort_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(_, Some(ExprSort::Datatype(id))) => Some(resolve_sort_name(*id)),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => root_datatype_sort_name(inner),
        _ => None,
    }
}

fn logical_fmap_iter_sort_name(expr: &PureExpr) -> Option<String> {
    let sort_name = root_datatype_sort_name(expr)?;
    LOGICAL_FMAP_ITER_SORT_NAMES
        .contains(&sort_name.as_str())
        .then_some(sort_name)
}

pub(crate) fn is_logical_fmap_iter_receiver(expr: &PureExpr) -> bool {
    logical_fmap_iter_sort_name(expr).is_some()
}

pub(super) fn logical_fmap_iter_expr_sort(expr: &PureExpr) -> Option<ExprSort> {
    logical_fmap_iter_sort_name(expr).map(|name| ExprSort::Datatype(intern_sort_name(&name)))
}

// ── Witness helpers ────────────────────────────────────────────────

fn visited_key_witness_exists(visited: &PureExpr, key: PureExpr, witness_name: &str) -> PureExpr {
    let witness = PureExpr::Var(witness_name.to_string(), Some(ExprSort::Tuple(2)));
    PureExpr::Exists {
        var: witness_name.to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(and(
            contains((*visited).clone(), witness.clone()),
            eq(deep_model(tuple_get(0, witness)), key),
        )),
        triggers: vec![],
    }
}

fn visited_entry_witness_exists(
    visited: &PureExpr,
    key: PureExpr,
    value: PureExpr,
    witness_name: &str,
) -> PureExpr {
    let witness = PureExpr::Var(witness_name.to_string(), Some(ExprSort::Tuple(2)));
    PureExpr::Exists {
        var: witness_name.to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(and(
            and(
                contains((*visited).clone(), witness.clone()),
                eq(deep_model(tuple_get(0, witness.clone())), key),
            ),
            eq(tuple_get(1, witness), value),
        )),
        triggers: vec![],
    }
}

// ── Main body builder ──────────────────────────────────────────────

/// Build the quantified partition predicate body for logical FMapIter.
///
/// Produces 5 conjunctive clauses:
/// 1. **Length partition:** `len(view(self)) == len(visited) + len(view(next))`
/// 2. **Visited membership:** visited entries exist in self's view
/// 3. **Next membership:** next entries exist in self's view, not in visited
/// 4. **Receiver coverage:** every self entry is in either visited or next
/// 5. **Key uniqueness:** visited entries have unique keys (by deep_model)
#[allow(clippy::too_many_lines)] // Cohesive predicate body construction
pub(super) fn build_logical_fmap_iter_body(
    iter_sort: ExprSort,
    self_name: &str,
    visited_name: &str,
    next_name: &str,
) -> PureExpr {
    let self_var = PureExpr::Var(self_name.to_string(), Some(iter_sort.clone()));
    let visited = PureExpr::Var(visited_name.to_string(), Some(ExprSort::Seq));
    let next_var = PureExpr::Var(next_name.to_string(), Some(iter_sort));

    let self_view = view_projector(self_var.clone());
    let next_view = view_projector(next_var.clone());

    let len_clause = eq(
        len(self_view.clone()),
        add(len(visited.clone()), len(next_view.clone())),
    );

    let visited_entry = PureExpr::Var(
        "__logical_fmap_visited_entry".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let visited_key = tuple_get(0, visited_entry.clone());
    let visited_value = tuple_get(1, visited_entry.clone());
    let visited_trigger = contains(visited.clone(), visited_entry.clone());
    let visited_key_dm = deep_model(visited_key.clone());
    let visited_clause = PureExpr::Forall {
        var: "__logical_fmap_visited_entry".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            visited_trigger.clone(),
            and(
                and(
                    contains(self_view.clone(), visited_key_dm.clone()),
                    eq(
                        lookup(self_view.clone(), visited_key_dm.clone()),
                        visited_value,
                    ),
                ),
                not(contains(next_view.clone(), visited_key_dm)),
            ),
        )),
        triggers: vec![vec![visited_trigger]],
    };

    let next_entry = PureExpr::Var(
        "__logical_fmap_next_entry".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let next_key = tuple_get(0, next_entry.clone());
    let next_value = tuple_get(1, next_entry.clone());
    let next_contains = contains(next_view.clone(), next_key.clone());
    let next_lookup = lookup(next_view.clone(), next_key.clone());
    let next_membership = and(
        next_contains.clone(),
        eq(next_lookup.clone(), next_value.clone()),
    );
    let next_clause = PureExpr::Forall {
        var: "__logical_fmap_next_entry".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            next_membership,
            and(
                and(
                    contains(self_view.clone(), next_key.clone()),
                    eq(lookup(self_view.clone(), next_key.clone()), next_value),
                ),
                not(visited_key_witness_exists(
                    &visited,
                    next_key,
                    "__logical_fmap_next_witness",
                )),
            ),
        )),
        triggers: vec![vec![next_contains, next_lookup]],
    };

    let receiver_entry = PureExpr::Var(
        "__logical_fmap_receiver_entry".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let receiver_key = tuple_get(0, receiver_entry.clone());
    let receiver_value = tuple_get(1, receiver_entry.clone());
    let receiver_contains = contains(self_view.clone(), receiver_key.clone());
    let receiver_lookup = lookup(self_view.clone(), receiver_key.clone());
    let receiver_membership = and(
        receiver_contains.clone(),
        eq(receiver_lookup.clone(), receiver_value.clone()),
    );
    let receiver_clause = PureExpr::Forall {
        var: "__logical_fmap_receiver_entry".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            receiver_membership,
            or(
                visited_entry_witness_exists(
                    &visited,
                    receiver_key.clone(),
                    receiver_value.clone(),
                    "__logical_fmap_receiver_witness",
                ),
                and(
                    contains(next_view.clone(), receiver_key.clone()),
                    eq(lookup(next_view.clone(), receiver_key), receiver_value),
                ),
            ),
        )),
        triggers: vec![vec![receiver_contains, receiver_lookup]],
    };

    let visited_entry_1 = PureExpr::Var(
        "__logical_fmap_visited_entry_1".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let visited_entry_2 = PureExpr::Var(
        "__logical_fmap_visited_entry_2".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let visited_contains_1 = contains(visited.clone(), visited_entry_1.clone());
    let visited_contains_2 = contains(visited, visited_entry_2.clone());
    let uniqueness_inner = PureExpr::Forall {
        var: "__logical_fmap_visited_entry_2".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            and(
                and(visited_contains_1.clone(), visited_contains_2.clone()),
                eq(
                    deep_model(tuple_get(0, visited_entry_1.clone())),
                    deep_model(tuple_get(0, visited_entry_2.clone())),
                ),
            ),
            eq(visited_entry_1.clone(), visited_entry_2.clone()),
        )),
        triggers: vec![vec![visited_contains_2]],
    };
    let uniqueness_clause = PureExpr::Forall {
        var: "__logical_fmap_visited_entry_1".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(uniqueness_inner),
        triggers: vec![vec![visited_contains_1]],
    };

    fold_and(vec![
        len_clause,
        visited_clause,
        next_clause,
        receiver_clause,
        uniqueness_clause,
    ])
}
