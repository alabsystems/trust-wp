// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Collection iterator rewrites backed by `FMap` views.
//!
//! For `HashMap::{IntoIter, Iter, IterMut}`, rewrites:
//! - `it.produces(visited, next)` → FMap partition/coverage formula
//! - `it.completed()` → `it@.is_empty()`
//!
//! Logical `FMapIter.produces(...)` is intentionally left alone so the encoder
//! can attach the transparent predicate decomposition lazily at the produces
//! UF boundary instead of eagerly expanding the full partition formula here.
//! `completed()` still lowers to `it@.is_empty()` because that rewrite is cheap.

use std::sync::Arc;

use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, ExprSort, PureExpr, UnOp,
};

use super::{
    helpers::{
        receiver_datatype_id, sort_matches_any, FMAP_ITER_SORT_NAMES,
        HASH_MAP_INTO_ITER_SORT_NAMES, HASH_MAP_ITER_MUT_SORT_NAMES, HASH_MAP_ITER_SORT_NAMES,
        HASH_SET_DIFFERENCE_SORT_NAMES, HASH_SET_INTERSECTION_SORT_NAMES,
        HASH_SET_INTO_ITER_SORT_NAMES, HASH_SET_ITER_SORT_NAMES,
    },
    rewrite_expr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HashMapIteratorKind {
    IntoIter,
    Iter,
    IterMut,
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn zero_arg_method(receiver: PureExpr, method: &str) -> PureExpr {
    method_call(receiver, method, vec![])
}

fn view(expr: &PureExpr) -> PureExpr {
    PureExpr::View(Arc::new(rewrite_expr(expr)))
}

fn len(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "len")
}

fn contains(receiver: PureExpr, arg: PureExpr) -> PureExpr {
    method_call(receiver, "contains", vec![arg])
}

fn lookup(receiver: PureExpr, key: PureExpr) -> PureExpr {
    method_call(receiver, "lookup", vec![key])
}

fn deep_model(receiver: PureExpr) -> PureExpr {
    zero_arg_method(receiver, "deep_model")
}

fn tuple_get(index: usize, tuple: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(index),
        args: vec![tuple],
    }
}

fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
}

fn or(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs))
}

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs))
}

fn implies(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
}

fn not(expr: PureExpr) -> PureExpr {
    PureExpr::UnOp(UnOp::Not, Arc::new(expr))
}

fn maybe_deref(expr: PureExpr, should_deref: bool) -> PureExpr {
    if should_deref {
        PureExpr::Deref(Arc::new(expr))
    } else {
        expr
    }
}

fn fold_and(mut clauses: Vec<PureExpr>) -> PureExpr {
    let first = clauses
        .drain(..1)
        .next()
        .expect("fold_and requires at least one clause");
    clauses.into_iter().fold(first, and)
}

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
    value_needs_deref: bool,
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
            eq(maybe_deref(tuple_get(1, witness), value_needs_deref), value),
        )),
        triggers: vec![],
    }
}

fn rewrite_hash_map_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }
    let kind = hash_map_iterator_kind(receiver).or_else(|| hash_map_iterator_kind(&args[1]))?;
    let visited_value_needs_deref = matches!(
        kind,
        HashMapIteratorKind::Iter | HashMapIteratorKind::IterMut
    );

    let receiver_view = view(receiver);
    let visited = rewrite_expr(&args[0]);
    let next_view = view(&args[1]);

    let len_clause = eq(
        len(receiver_view.clone()),
        add(len(visited.clone()), len(next_view.clone())),
    );

    let visited_entry = PureExpr::Var(
        "__hash_map_visited_entry".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let visited_key = tuple_get(0, visited_entry.clone());
    let visited_value = tuple_get(1, visited_entry.clone());
    let visited_trigger = contains(visited.clone(), visited_entry.clone());
    let visited_key_dm = deep_model(visited_key.clone());
    let visited_value_for_view = maybe_deref(visited_value, visited_value_needs_deref);
    let visited_clause = PureExpr::Forall {
        var: "__hash_map_visited_entry".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            visited_trigger.clone(),
            and(
                and(
                    contains(receiver_view.clone(), visited_key_dm.clone()),
                    eq(
                        lookup(receiver_view.clone(), visited_key_dm.clone()),
                        visited_value_for_view,
                    ),
                ),
                not(contains(next_view.clone(), visited_key_dm)),
            ),
        )),
        triggers: vec![vec![visited_trigger]],
    };

    let next_entry = PureExpr::Var(
        "__hash_map_next_entry".to_string(),
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
        var: "__hash_map_next_entry".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            next_membership,
            and(
                and(
                    contains(receiver_view.clone(), next_key.clone()),
                    eq(lookup(receiver_view.clone(), next_key.clone()), next_value),
                ),
                not(visited_key_witness_exists(
                    &visited,
                    next_key,
                    "__hash_map_next_witness",
                )),
            ),
        )),
        triggers: vec![vec![next_contains, next_lookup]],
    };

    let receiver_entry = PureExpr::Var(
        "__hash_map_receiver_entry".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let receiver_key = tuple_get(0, receiver_entry.clone());
    let receiver_value = tuple_get(1, receiver_entry.clone());
    let receiver_contains = contains(receiver_view.clone(), receiver_key.clone());
    let receiver_lookup = lookup(receiver_view.clone(), receiver_key.clone());
    let receiver_membership = and(
        receiver_contains.clone(),
        eq(receiver_lookup.clone(), receiver_value.clone()),
    );
    let receiver_clause = PureExpr::Forall {
        var: "__hash_map_receiver_entry".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(implies(
            receiver_membership,
            or(
                visited_entry_witness_exists(
                    &visited,
                    receiver_key.clone(),
                    receiver_value.clone(),
                    "__hash_map_receiver_witness",
                    visited_value_needs_deref,
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
        "__hash_map_visited_entry_1".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let visited_entry_2 = PureExpr::Var(
        "__hash_map_visited_entry_2".to_string(),
        Some(ExprSort::Tuple(2)),
    );
    let visited_contains_1 = contains(visited.clone(), visited_entry_1.clone());
    let visited_contains_2 = contains(visited.clone(), visited_entry_2.clone());
    let uniqueness_inner = PureExpr::Forall {
        var: "__hash_map_visited_entry_2".to_string(),
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
        var: "__hash_map_visited_entry_1".to_string(),
        var_sort: Some(ExprSort::Tuple(2)),
        body: Arc::new(uniqueness_inner),
        triggers: vec![vec![visited_contains_1]],
    };

    Some(fold_and(vec![
        len_clause,
        visited_clause,
        next_clause,
        receiver_clause,
        uniqueness_clause,
    ]))
}

fn rewrite_hash_map_completed(receiver: &PureExpr) -> PureExpr {
    zero_arg_method(view(receiver), "is_empty")
}

fn is_logical_fmap_iter(receiver: &PureExpr) -> bool {
    receiver_datatype_id(receiver)
        .is_some_and(|dt_id| sort_matches_any(dt_id, FMAP_ITER_SORT_NAMES))
}

fn hash_map_iterator_kind(receiver: &PureExpr) -> Option<HashMapIteratorKind> {
    let dt_id = receiver_datatype_id(receiver)?;
    if sort_matches_any(dt_id, HASH_MAP_INTO_ITER_SORT_NAMES) {
        Some(HashMapIteratorKind::IntoIter)
    } else if sort_matches_any(dt_id, HASH_MAP_ITER_SORT_NAMES) {
        Some(HashMapIteratorKind::Iter)
    } else if sort_matches_any(dt_id, HASH_MAP_ITER_MUT_SORT_NAMES) {
        Some(HashMapIteratorKind::IterMut)
    } else {
        None
    }
}

// --- HashSet iterator rewrite ---

fn is_hash_set_iterator(receiver: &PureExpr) -> bool {
    let Some(dt_id) = receiver_datatype_id(receiver) else {
        return false;
    };
    sort_matches_any(dt_id, HASH_SET_INTO_ITER_SORT_NAMES)
        || sort_matches_any(dt_id, HASH_SET_ITER_SORT_NAMES)
        || sort_matches_any(dt_id, HASH_SET_INTERSECTION_SORT_NAMES)
        || sort_matches_any(dt_id, HASH_SET_DIFFERENCE_SORT_NAMES)
}

fn is_hash_set_produces_call(receiver: &PureExpr, args: &[PureExpr]) -> bool {
    is_hash_set_iterator(receiver) || args.get(1).is_some_and(is_hash_set_iterator)
}

/// Rewrite `it.produces(visited, next)` for `HashSet::{IntoIter, Iter}` to
/// an FSet partition formula following Creusot's `set_produces` pattern.
///
/// The formula asserts:
/// 1. `it@.len() == visited.len() + next@.len()` (cardinality partition)
/// 2. Every visited element's deep_model is in `it@` and absent from `next@`
/// 3. Every element of `next@` is in `it@` and not witnessed in visited
/// 4. Every element of `it@` is either in `next@` or witnessed in visited
/// 5. Visited elements are unique by deep_model
fn rewrite_hash_set_produces(receiver: &PureExpr, args: &[PureExpr]) -> Option<PureExpr> {
    if args.len() != 2 {
        return None;
    }

    let receiver_view = view(receiver);
    let visited = rewrite_expr(&args[0]);
    let next_view = view(&args[1]);

    // 1. Cardinality partition: it@.len() == visited.len() + next@.len()
    let len_clause = eq(
        len(receiver_view.clone()),
        add(len(visited.clone()), len(next_view.clone())),
    );

    // 2. Visited elements are in receiver and absent from next:
    //    forall e: contains(visited, e) ==>
    //      contains(it@, deep_model(e)) && !contains(next@, deep_model(e))
    let visited_elem = PureExpr::Var("__hash_set_visited_elem".to_string(), None);
    let visited_trigger = contains(visited.clone(), visited_elem.clone());
    let visited_dm = deep_model(visited_elem);
    let visited_clause = PureExpr::Forall {
        var: "__hash_set_visited_elem".to_string(),
        var_sort: None,
        body: Arc::new(implies(
            visited_trigger.clone(),
            and(
                contains(receiver_view.clone(), visited_dm.clone()),
                not(contains(next_view.clone(), visited_dm)),
            ),
        )),
        triggers: vec![vec![visited_trigger]],
    };

    // 3. Next elements are in receiver and not witnessed in visited:
    //    forall dm: contains(next@, dm) ==>
    //      contains(it@, dm) && !exists w: contains(visited, w) && deep_model(w) == dm
    let next_dm = PureExpr::Var("__hash_set_next_dm".to_string(), None);
    let next_trigger = contains(next_view.clone(), next_dm.clone());
    let next_witness = PureExpr::Var("__hash_set_next_witness".to_string(), None);
    let next_witness_exists = PureExpr::Exists {
        var: "__hash_set_next_witness".to_string(),
        var_sort: None,
        body: Arc::new(and(
            contains(visited.clone(), next_witness.clone()),
            eq(deep_model(next_witness), next_dm.clone()),
        )),
        triggers: vec![],
    };
    let next_clause = PureExpr::Forall {
        var: "__hash_set_next_dm".to_string(),
        var_sort: None,
        body: Arc::new(implies(
            next_trigger.clone(),
            and(
                contains(receiver_view.clone(), next_dm),
                not(next_witness_exists),
            ),
        )),
        triggers: vec![vec![next_trigger]],
    };

    // 4. Coverage: every element of receiver is either in next or witnessed in visited:
    //    forall dm: contains(it@, dm) ==>
    //      contains(next@, dm) || exists w: contains(visited, w) && deep_model(w) == dm
    let receiver_dm = PureExpr::Var("__hash_set_receiver_dm".to_string(), None);
    let receiver_trigger = contains(receiver_view.clone(), receiver_dm.clone());
    let cover_witness = PureExpr::Var("__hash_set_cover_witness".to_string(), None);
    let cover_witness_exists = PureExpr::Exists {
        var: "__hash_set_cover_witness".to_string(),
        var_sort: None,
        body: Arc::new(and(
            contains(visited.clone(), cover_witness.clone()),
            eq(deep_model(cover_witness), receiver_dm.clone()),
        )),
        triggers: vec![],
    };
    let receiver_clause = PureExpr::Forall {
        var: "__hash_set_receiver_dm".to_string(),
        var_sort: None,
        body: Arc::new(implies(
            receiver_trigger.clone(),
            or(
                contains(next_view.clone(), receiver_dm),
                cover_witness_exists,
            ),
        )),
        triggers: vec![vec![receiver_trigger]],
    };

    // 5. Uniqueness: visited elements are unique by deep_model:
    //    forall e1: contains(visited, e1) ==>
    //      forall e2: contains(visited, e1) && contains(visited, e2)
    //        && deep_model(e1) == deep_model(e2) ==> e1 == e2
    let visited_elem_1 = PureExpr::Var("__hash_set_visited_elem_1".to_string(), None);
    let visited_elem_2 = PureExpr::Var("__hash_set_visited_elem_2".to_string(), None);
    let visited_contains_1 = contains(visited.clone(), visited_elem_1.clone());
    let visited_contains_2 = contains(visited, visited_elem_2.clone());
    let uniqueness_inner = PureExpr::Forall {
        var: "__hash_set_visited_elem_2".to_string(),
        var_sort: None,
        body: Arc::new(implies(
            and(
                and(visited_contains_1.clone(), visited_contains_2.clone()),
                eq(
                    deep_model(visited_elem_1.clone()),
                    deep_model(visited_elem_2.clone()),
                ),
            ),
            eq(visited_elem_1.clone(), visited_elem_2),
        )),
        triggers: vec![vec![visited_contains_2]],
    };
    let uniqueness_clause = PureExpr::Forall {
        var: "__hash_set_visited_elem_1".to_string(),
        var_sort: None,
        body: Arc::new(uniqueness_inner),
        triggers: vec![vec![visited_contains_1]],
    };

    Some(fold_and(vec![
        len_clause,
        visited_clause,
        next_clause,
        receiver_clause,
        uniqueness_clause,
    ]))
}

fn rewrite_hash_set_completed(receiver: &PureExpr) -> PureExpr {
    zero_arg_method(view(receiver), "is_empty")
}

pub(super) fn try_rewrite_collection_iter_method(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
) -> Option<PureExpr> {
    if is_logical_fmap_iter(receiver) {
        return match method {
            "produces" => None,
            "completed" => Some(rewrite_hash_map_completed(receiver)),
            _ => None,
        };
    }

    match method {
        "produces"
            if hash_map_iterator_kind(receiver).is_some()
                || args.get(1).and_then(hash_map_iterator_kind).is_some() =>
        {
            return rewrite_hash_map_produces(receiver, args);
        }
        "completed" if hash_map_iterator_kind(receiver).is_some() => {
            return Some(rewrite_hash_map_completed(receiver));
        }
        _ => {}
    }

    match method {
        "produces" if is_hash_set_produces_call(receiver, args) => {
            return rewrite_hash_set_produces(receiver, args);
        }
        "completed" if is_hash_set_iterator(receiver) => {
            return Some(rewrite_hash_set_completed(receiver));
        }
        _ => {}
    }

    None
}
