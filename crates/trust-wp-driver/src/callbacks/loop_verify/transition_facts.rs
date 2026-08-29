// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Transition-fact helpers for structural loop verification.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, TUPLE_FIELD_LOGIC_FN_PREFIX},
    BinOp, ExprSort, PureExpr,
};

use super::for_loop_facts::{
    build_for_loop_literal_start_element_index_fact, build_for_loop_produced_len_step_fact,
    build_for_loop_range_element_current_fact, build_for_loop_transition_end_fact,
    build_for_loop_transition_fact, build_for_loop_transition_guard_fact,
    build_for_loop_transition_step_fact, build_for_loop_zero_start_element_index_fact,
};
use crate::mir_analysis::ForLoopGhostState;

/// Whether `expr` is the canonical empty-`FMap` constructor
/// (`fmap_empty()` / `fmap_new()` logic call, or `FMap::empty()` / `FMap::new()`).
///
/// A `true` result is a PROOF the map is empty: `FMap::new()`/`empty()` carry the
/// `EMPTY` spec (`len == 0`, `forall k. !contains(k)`), which the encoder's
/// emptiness axioms realize. Used to justify the single-entry FMap identity
/// bridge. (cc/fmap layer c)
fn is_fmap_empty_ctor(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } if args.is_empty() => {
            matches!(name.as_str(), "fmap_empty" | "fmap_new" | "FMap::empty")
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty() && matches!(method.as_str(), "empty" | "new") => {
            matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "FMap")
        }
        _ => false,
    }
}

/// If `expr` is EXACTLY a single insert into a provably-empty `FMap` —
/// `FMap::new()/empty().insert(Var(k), Var(v))` — return `(k, v)`.
///
/// This is the sound single-entry justification for the FMap identity bridge:
/// the map has provably exactly one entry `(k, v)`, so the sole yielded
/// iteration element's key/value references ARE `k`/`v`. For any other shape
/// (multiple inserts, a non-empty/unknown base, non-`Var` insert args) the
/// bridge must NOT fire, because the yielded entry need not be the inserted one.
/// (cc/fmap layer c)
pub(super) fn single_insert_into_empty_fmap(expr: &PureExpr) -> Option<(String, String)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "insert" || args.len() != 2 {
        return None;
    }
    let (PureExpr::Var(key_name, _), PureExpr::Var(val_name, _)) = (&args[0], &args[1]) else {
        return None;
    };
    if !is_fmap_empty_ctor(receiver) {
        return None;
    }
    Some((key_name.clone(), val_name.clone()))
}

/// Build FMap identity bridge transition facts (#2116).
///
/// For consuming FMap iteration where the FMap was built with known `insert_ghost`
/// calls, the yielded entry is the same mutable reference that was inserted.
/// Generate `Final(borrow_var) == Final(insert_var)` facts to bridge the
/// prophecy variables.
///
/// `borrow_var_by_position` maps tuple position (0=key, 1=value) to the
/// destructured loop variable name (e.g., 0→"k2", 1→"v2").
pub(super) fn build_fmap_identity_bridge_facts(
    insert_pairs: &[(String, String)],
    borrow_var_by_position: &HashMap<usize, String>,
) -> Vec<PureExpr> {
    let mut facts = Vec::new();
    for (insert_key, insert_val) in insert_pairs {
        if let Some(key_borrow_var) = borrow_var_by_position.get(&0) {
            facts.push(PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    key_borrow_var.clone(),
                    None,
                )))),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    insert_key.clone(),
                    None,
                )))),
            ));
        }
        if let Some(val_borrow_var) = borrow_var_by_position.get(&1) {
            facts.push(PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    val_borrow_var.clone(),
                    None,
                )))),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    insert_val.clone(),
                    None,
                )))),
            ));
        }
    }
    facts
}

/// Map borrow variable names to their tuple positions (0=key, 1=value) by
/// inspecting direct body effects for `TupleGet(idx, _)` patterns (#2116).
///
/// For `for (k2, v2) in fmap`, the direct body effects contain:
/// - `k2 → TupleGet(0, Var("loop_elem"))` — position 0 (key)
/// - `v2 → TupleGet(1, Var("loop_elem"))` — position 1 (value)
pub(super) fn build_tuple_position_map(
    borrow_vars: &[String],
    body_effect: &HashMap<String, PureExpr>,
) -> HashMap<usize, String> {
    let mut pos_map = HashMap::new();
    for var in borrow_vars {
        if let Some(PureExpr::LogicFnCall { name, .. }) = body_effect.get(var) {
            if let Some(idx_str) = name.strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX) {
                if let Ok(idx) = idx_str.parse::<usize>() {
                    pos_map.insert(idx, var.clone());
                }
            }
        }
    }
    pos_map
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
    PureExpr::View(Arc::new(expr.clone()))
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

/// Determine whether the structural produces invariant should be auto-injected
/// into the loop VC for this for-loop.
///
/// Normally true: the structural invariant is auto-injected for all for-loop
/// iterator types, including FMap iterators. The previous FMap guard that
/// required the user to have written an invariant referencing `produced`
/// defeated auto-injection (#2171). The structural invariant is needed for
/// sound inductive reasoning regardless of whether the user explicitly
/// references `produced`.
///
/// EXCEPTION — provable-singleton FMap iteration (cc/fmap): the generic
/// `iter_old.produces(produced, iter_state)` form (used for FMap, unlike the
/// seq path's directly-preservable `concat`+anchor form) has NO structural
/// direct-prover, so its PRESERVATION slice
/// (`produces(iter_old, produced', iter_state')`) reduces to a quantifier-heavy
/// produces-composition VC that ay cannot complete (returns
/// `quantifier-ematching-exists-incomplete`). For the provably-singleton map
/// (exactly one insert of `(bor_k, bor_v)` into a provably-empty base — the
/// sound gate the whole cc/fmap cascade uses) the invariant is REDUNDANT: the
/// singleton cardinality-conservation transition facts (see
/// `build_transition_facts_for_loop_state`) discharge the user `produced.len()`
/// invariants directly, and the exhausted-iterator completion facts (see
/// `build_for_loop_completion_facts`) supply the postcondition's
/// `produced.len() == iterable.len()`. Suppressing it here is SOUND (it only
/// DROPS a premise — no new fact — and removes an unprovable slice); it does
/// not weaken any other obligation because both roles are covered by the
/// (gated, true) cardinality/completion facts. Kept for every non-singleton
/// FMap loop, where the produces invariant remains load-bearing.
pub(super) fn include_structural_invariant_in_loop_vc(
    state: &ForLoopGhostState,
    _invariants: &[PureExpr],
    _ensures: &[PureExpr],
    _loop_condition: Option<&PureExpr>,
    _variant: Option<&PureExpr>,
) -> bool {
    if let Some(iterable) = state.iterable.as_ref() {
        if single_insert_into_empty_fmap(iterable).is_some() {
            return false;
        }
    }
    true
}

pub(in crate::callbacks) fn build_transition_facts_for_loop_state(
    state: &ForLoopGhostState,
) -> Vec<PureExpr> {
    if let Some(range_end) = build_for_loop_transition_end_fact(state) {
        let mut facts = vec![range_end];
        if let Some(range_guard) = build_for_loop_transition_guard_fact(state) {
            facts.push(range_guard);
        }
        if let Some(range_elem_current) = build_for_loop_range_element_current_fact(state) {
            facts.push(range_elem_current);
        }
        if let Some(zero_start_index) = build_for_loop_zero_start_element_index_fact(state) {
            facts.push(zero_start_index);
        }
        if let Some(literal_start_index) = build_for_loop_literal_start_element_index_fact(state) {
            if !facts.contains(&literal_start_index) {
                facts.push(literal_start_index);
            }
        }
        if let Some(range_step) = build_for_loop_transition_step_fact(state) {
            facts.push(range_step);
        }
        if let Some(produced_len_step) = build_for_loop_produced_len_step_fact(state) {
            facts.push(produced_len_step);
        }
        return facts;
    }

    if super::super::iterator_spec_rewrite::helpers::is_logical_fmap_iter(&state.iter_state) {
        let current_view = view(&state.iter_state);
        let next_view = view(&state.iter_state_next);
        let entry_key_dm = deep_model(tuple_get(0, state.loop_elem.clone()));
        let entry_value = tuple_get(1, state.loop_elem.clone());
        let other_key = PureExpr::Var("__fmap_iter_other_key".to_string(), None);
        let current_contains_other = contains(current_view.clone(), other_key.clone());
        let current_lookup_other = lookup(current_view.clone(), other_key.clone());
        let next_contains_other = contains(next_view.clone(), other_key.clone());
        let next_lookup_other = lookup(next_view.clone(), other_key.clone());

        let preserves_remaining_entries = PureExpr::Forall {
            var: "__fmap_iter_other_key".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(other_key.clone()),
                        BinOp::Ne,
                        Arc::new(entry_key_dm.clone()),
                    )),
                    BinOp::And,
                    Arc::new(current_contains_other.clone()),
                )),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(next_contains_other.clone()),
                    BinOp::And,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(next_lookup_other.clone()),
                        BinOp::Eq,
                        Arc::new(current_lookup_other.clone()),
                    )),
                )),
            )),
            triggers: vec![vec![
                current_contains_other.clone(),
                current_lookup_other.clone(),
            ]],
        };

        let next_entries_come_from_current = PureExpr::Forall {
            var: "__fmap_iter_other_key".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(next_contains_other.clone()),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(other_key.clone()),
                        BinOp::Ne,
                        Arc::new(entry_key_dm.clone()),
                    )),
                    BinOp::And,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(current_contains_other.clone()),
                        BinOp::And,
                        Arc::new(PureExpr::BinOp(
                            Arc::new(current_lookup_other.clone()),
                            BinOp::Eq,
                            Arc::new(next_lookup_other.clone()),
                        )),
                    )),
                )),
            )),
            triggers: vec![vec![next_contains_other.clone(), next_lookup_other.clone()]],
        };

        // Doubly-quantified get-form frame axioms (preserves_remaining_get_entries,
        // next_get_entries_come_from_current) and ground get-form facts
        // (entry_value_fact, entry_removed_fact) removed: they are redundant
        // with the singly-quantified contains/lookup frame axioms above.
        //
        // The encoder normalizes `get(m,k)==Some(v)` to `contains(m,k) && lookup(m,k)==v`
        // (see binop.rs:fmap_get_some_formula), so the singly-quantified facts
        // suffice. Removing the 4 redundant facts cuts the quantifier budget
        // the solver must handle per FMap iteration step, reducing timeout
        // risk for complex FMap loop proofs. (#2116)

        let mut facts = vec![
            PureExpr::BinOp(
                Arc::new(len(current_view.clone())),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(len(next_view.clone())),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                )),
            ),
            contains(current_view.clone(), entry_key_dm.clone()),
            PureExpr::BinOp(
                Arc::new(lookup(current_view.clone(), entry_key_dm.clone())),
                BinOp::Eq,
                Arc::new(entry_value),
            ),
            PureExpr::UnOp(
                trust_wp_core::formula::UnOp::Not,
                Arc::new(contains(next_view.clone(), entry_key_dm)),
            ),
            preserves_remaining_entries,
            next_entries_come_from_current,
        ];

        // cc/fmap: singleton cardinality-conservation for PRESERVATION.
        //
        // The per-step `len(current_view) == len(next_view) + 1` fact above is
        // dropped by the preservation slicer for the `produced.len()`-style
        // invariant slice, because it mentions only the iterator-state views —
        // not `produced` (preservation.rs filters transition facts to those
        // referencing the slice's own variables). Even kept, it lacks ANCHOR A
        // (`View(iter_old) == View(iterable)`) so it cannot bound `produced.len()`.
        //
        // When the iterated map is a PROVABLE singleton (exactly one insert of
        // `(bor_k, bor_v)` into a provably-empty base — the same sound gate the
        // rest of the cc/fmap cascade uses) we thread the cardinality directly:
        //   produced.len() + len(current_view) == 1   AND   len(current_view) >= 1
        // bundled as a SINGLE `And` fact so it mentions `produced` and survives
        // the slicer's per-slice variable filter (both conjuncts kept together).
        //
        // SOUNDNESS: `produces(iter_old, produced, iter_state)` (the auto-injected
        // structural invariant) plus `View(iter_old) == View(iterable)` give
        // `len(produced) + len(iter_state@) == len(iterable@)`; the singleton
        // gate proves `len(iterable@) == 1`, so `produced.len() + len(current_view)
        // == 1` is a theorem. `len(current_view) >= 1` holds because preservation
        // assumes the loop condition (the body executes ⟺ `next()` returned
        // `Some` ⟺ the pre-step remaining map is non-empty). Both are true facts;
        // premise ADDITION of a true fact is sound. z3 cross-checked: with these
        // two the slice goal is UNSAT for the right reason, and the premise set
        // stays SAT (non-vacuous).
        if let Some(iterable) = state.iterable.as_ref() {
            if single_insert_into_empty_fmap(iterable).is_some() {
                let produced_len = len(PureExpr::Var(
                    state.produced_name.clone(),
                    Some(ExprSort::Seq),
                ));
                let remaining_len = len(current_view.clone());
                let cardinality = PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::BinOp(
                            Arc::new(produced_len),
                            BinOp::Add,
                            Arc::new(remaining_len.clone()),
                        )),
                        BinOp::Eq,
                        Arc::new(PureExpr::Int(1)),
                    )),
                    BinOp::And,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(remaining_len),
                        BinOp::Ge,
                        Arc::new(PureExpr::Int(1)),
                    )),
                );
                facts.push(cardinality);
            }
        }
        return facts;
    }

    if super::super::iterator_spec_rewrite::helpers::is_seq_backed_iterator(&state.iter_state) {
        return vec![PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_next.clone()))),
                method: "push_front_ghost".to_string(),
                args: vec![state.loop_elem.clone()],
            }),
        )];
    }

    vec![
        super::super::iterator_spec_rewrite::rewrite_iterator_spec_expr(
            &build_for_loop_transition_fact(state),
        ),
    ]
}
