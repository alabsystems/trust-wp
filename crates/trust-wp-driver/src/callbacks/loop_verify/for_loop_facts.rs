// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! For-loop structural fact builders for loop verification.

use std::sync::Arc;

use trust_wp_core::formula::{resolve_sort_name, BinOp, ExprSort, PureExpr};

use super::expr_utils::expr_references_var;
use crate::mir_analysis::ForLoopGhostState;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RangeLoopKind {
    Exclusive,
    Inclusive,
}

/// Returns true for an inferred unsigned non-negativity invariant about the
/// current for-loop element. The loop element is only meaningful on an active
/// iteration, so this fact must stay out of raw initialization invariants.
pub(in crate::callbacks) fn is_for_loop_element_nonnegative_invariant(
    invariant: &PureExpr,
    state: Option<&ForLoopGhostState>,
) -> bool {
    let Some(state) = state else {
        return false;
    };

    match invariant {
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            lhs.as_ref() == &state.loop_elem && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && rhs.as_ref() == &state.loop_elem
        }
        _ => false,
    }
}

/// Build the structural invariant for a Creusot-style for-loop (#2171).
///
/// Synthesizes `iter_old.produces(produced, iter_state)` from the grouped
/// ghost state. This invariant relates the iterator snapshot at loop entry
/// to the current iterator state via the sequence of produced elements.
pub(in crate::callbacks) fn build_for_loop_structural_invariant(
    state: &ForLoopGhostState,
) -> PureExpr {
    if is_range_state_expr(&state.iter_state) {
        return PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(state.iter_old.clone()),
                    method: "end_log".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(state.iter_state.clone()),
                    method: "end_log".to_string(),
                    args: vec![],
                }),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::MethodCall {
                        receiver: Arc::new(state.iter_old.clone()),
                        method: "start_log".to_string(),
                        args: vec![],
                    }),
                    BinOp::Le,
                    Arc::new(PureExpr::MethodCall {
                        receiver: Arc::new(state.iter_state.clone()),
                        method: "start_log".to_string(),
                        args: vec![],
                    }),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::MethodCall {
                        receiver: Arc::new(PureExpr::Var(
                            state.produced_name.clone(),
                            Some(ExprSort::Seq),
                        )),
                        method: "len".to_string(),
                        args: vec![],
                    }),
                    BinOp::Eq,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(state.iter_state.clone()),
                            method: "start_log".to_string(),
                            args: vec![],
                        }),
                        BinOp::Sub,
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(state.iter_old.clone()),
                            method: "start_log".to_string(),
                            args: vec![],
                        }),
                    )),
                )),
            )),
        );
    }

    // For Seq-backed iterators (SeqIter, Vec::IntoIter), emit a direct
    // equality `View(iter_old) == produced.concat(View(iter_state))` instead
    // of the generic `iter_old.produces(produced, iter_state)` form. The
    // produces form gets rewritten to ext_eq+concat which introduces Tseitin
    // Boolean variables and quantifier overhead that overwhelms the solver.
    // Direct equality avoids this entirely. (#2116)
    if super::super::iterator_spec_rewrite::helpers::is_seq_backed_iterator(&state.iter_state) {
        let view_iter_old = PureExpr::View(Arc::new(state.iter_old.clone()));
        let view_iter_state = PureExpr::View(Arc::new(state.iter_state.clone()));
        let produced_seq = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));

        // Core structural invariant: View(iter_old) == produced.concat(View(iter_state)).
        //
        // The View-projector proxy vs. `__vec_to_seq_<Sort>` bridge-UF split for
        // `View(iter_state)` (the two representations were never made congruent,
        // so the structural invariant's `len(View(iter_state))` could not reach
        // the body's `len(View(iter_state)) >= 1`) is now resolved in the encoder:
        // `coerce_to_seq` anchors `__vec_to_seq_<Sort>(iter) == <iter>_view` for
        // iterator sorts (trust-wp-ay seq/coercion.rs). (#2116)
        let core = PureExpr::BinOp(
            Arc::new(view_iter_old.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(produced_seq.clone()),
                method: "concat".to_string(),
                args: vec![view_iter_state.clone()],
            }),
        );

        // ANCHOR A — connect View(iter_old) to the iterable's view (#2116).
        //
        // The variant's source length `len` is established as `len(View(iterable))`
        // (the loop-entry snapshot of the iterable's length). The structural
        // invariant only constrains `View(iter_old)`, leaving `len(View(iter_old))`
        // disconnected from `len`, so the concat-length relation
        // `len(View(iter_old)) == produced.len() + len(View(iter_state))` never
        // reaches the goal `produced.len() + 1 <= len`. `iter_old` is the
        // loop-entry snapshot of the iterator over `iterable`, so its view IS the
        // iterable's view by construction. Emit both the value equality and its
        // length form; the loop VC slicer keeps length facts even when it drops
        // the full Seq equality. SOUND: both sides denote the same sequence value
        // (iterator-at-entry over `iterable`).
        if let Some(iterable) = state.iterable.as_ref() {
            let view_iterable = PureExpr::View(Arc::new(iterable.clone()));
            let anchor_value = PureExpr::BinOp(
                Arc::new(view_iter_old.clone()),
                BinOp::Eq,
                Arc::new(view_iterable.clone()),
            );
            let anchor_len = PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(view_iter_old),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(view_iterable),
                    method: "len".to_string(),
                    args: vec![],
                }),
            );
            return PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(core),
                    BinOp::And,
                    Arc::new(anchor_value),
                )),
                BinOp::And,
                Arc::new(anchor_len),
            );
        }

        return core;
    }

    PureExpr::MethodCall {
        receiver: Arc::new(state.iter_old.clone()),
        method: "produces".to_string(),
        args: vec![
            PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq)),
            state.iter_state.clone(),
        ],
    }
}

/// Build the one-step iterator transition fact for a Creusot-style for-loop.
///
/// Synthesizes `iter_state.produces(seq![loop_elem], iter_state_next)` so the
/// preservation VC can compose the current structural invariant with the
/// current iterator step. (#2171 Slice E)
pub(in crate::callbacks) fn build_for_loop_transition_fact(state: &ForLoopGhostState) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(state.iter_state.clone()),
        method: "produces".to_string(),
        args: vec![
            PureExpr::LogicFnCall {
                name: "seq".to_string(),
                args: vec![state.loop_elem.clone()],
            },
            state.iter_state_next.clone(),
        ],
    }
}

fn sort_range_kind(sort: &ExprSort) -> Option<RangeLoopKind> {
    match sort {
        ExprSort::Datatype(id) => match resolve_sort_name(*id).as_str() {
            "core::ops::range::Range" | "std::ops::Range" | "core::ops::Range" => {
                Some(RangeLoopKind::Exclusive)
            }
            "core::ops::range::RangeInclusive"
            | "std::ops::RangeInclusive"
            | "core::ops::RangeInclusive" => Some(RangeLoopKind::Inclusive),
            _ => None,
        },
        ExprSort::MutRef(inner) => sort_range_kind(inner),
        _ => None,
    }
}

fn range_state_kind(expr: &PureExpr) -> Option<RangeLoopKind> {
    let PureExpr::Var(_, Some(sort)) = expr else {
        return None;
    };
    sort_range_kind(sort)
}

fn is_range_state_expr(expr: &PureExpr) -> bool {
    range_state_kind(expr).is_some()
}

fn inclusive_range_len_expr(start: PureExpr, end: PureExpr) -> PureExpr {
    let nonempty = PureExpr::BinOp(Arc::new(end.clone()), BinOp::Ge, Arc::new(start.clone()));
    let span = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(Arc::new(end), BinOp::Sub, Arc::new(start))),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    PureExpr::Ite(
        Arc::new(nonempty),
        Arc::new(span),
        Arc::new(PureExpr::Int(0)),
    )
}

/// Build a preservation-only end-bound fact for range iterators.
///
/// Range `Iterator::next` advances the start but keeps the end bound stable.
/// The direct equality avoids the quantified `produces` rewrite in the
/// preservation VC while preserving the exact step relation needed by the
/// length-based structural invariant. (#2171)
pub(in crate::callbacks) fn build_for_loop_transition_end_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    if !is_range_state_expr(&state.iter_state) {
        return None;
    }

    Some(PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_state.clone()),
            method: "end_log".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_state_next.clone()),
            method: "end_log".to_string(),
            args: vec![],
        }),
    ))
}

/// Build a preservation-only current-step guard for range iterators.
///
/// The shared loop condition stays as the produced-length bound so exit
/// reasoning remains precise. Range preservation still needs the current-step
/// upper bound `iter_state.start_log() < iter_old.end_log()` to relate the
/// inductive state to the one-step `produces(seq![x], next)` transition. (#2171)
pub(in crate::callbacks) fn build_for_loop_transition_guard_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    let range_kind = range_state_kind(&state.iter_state)?;

    Some(PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_state.clone()),
            method: "start_log".to_string(),
            args: vec![],
        }),
        match range_kind {
            RangeLoopKind::Exclusive => BinOp::Lt,
            RangeLoopKind::Inclusive => BinOp::Le,
        },
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_old.clone()),
            method: "end_log".to_string(),
            args: vec![],
        }),
    ))
}

/// Build a preservation-only fact connecting the yielded range element to the
/// range cursor for the active iteration.
pub(in crate::callbacks) fn build_for_loop_range_element_current_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    if !is_range_state_expr(&state.iter_state) {
        return None;
    }

    Some(PureExpr::BinOp(
        Arc::new(state.loop_elem.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_state.clone()),
            method: "start_log".to_string(),
            args: vec![],
        }),
    ))
}

/// Build a preservation-only fact for zero-start range loops:
/// `loop_elem == produced.len()`.
///
/// User invariants often quantify over the produced prefix index, as in
/// `forall j < produced.len() ==> v[j] == ...`. After one iteration, the new
/// element is written at the current range element. For `0..end` ranges that
/// element is exactly the old produced length. Emit the fact directly so the
/// sliced preservation VC keeps it with produced-related obligations instead
/// of dropping cursor-only range facts.
pub(in crate::callbacks) fn build_for_loop_zero_start_element_index_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    if !is_range_state_expr(&state.iter_state) {
        return None;
    }
    let Some((PureExpr::Int(0), _)) = state.range_bounds.as_ref() else {
        return None;
    };

    Some(PureExpr::BinOp(
        Arc::new(state.loop_elem.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                state.produced_name.clone(),
                Some(ExprSort::Seq),
            )),
            method: "len".to_string(),
            args: vec![],
        }),
    ))
}

/// Build a preservation-only fact for literal-start range loops:
/// `loop_elem == produced.len() + start`.
///
/// The zero-start helper above keeps the common `elem == produced.len()` shape
/// for existing proofs. This general form covers loops like `for i in 1..=n`,
/// where arithmetic invariants over the produced prefix need the yielded item
/// as a direct offset from the old produced length.
pub(in crate::callbacks) fn build_for_loop_literal_start_element_index_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    if !is_range_state_expr(&state.iter_state) {
        return None;
    }
    let Some((PureExpr::Int(start), _)) = state.range_bounds.as_ref() else {
        return None;
    };

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(
            state.produced_name.clone(),
            Some(ExprSort::Seq),
        )),
        method: "len".to_string(),
        args: vec![],
    };
    let rhs = if *start == 0 {
        produced_len
    } else {
        PureExpr::BinOp(
            Arc::new(produced_len),
            BinOp::Add,
            Arc::new(PureExpr::Int(*start)),
        )
    };

    Some(PureExpr::BinOp(
        Arc::new(state.loop_elem.clone()),
        BinOp::Eq,
        Arc::new(rhs),
    ))
}

/// Build a direct one-step range advance fact for preservation.
///
/// `produces(seq![x], next)` implies `next.start_log() == current.start_log() + 1`
/// for range iterators, but that requires the solver to recover singleton-seq
/// length facts. Assert the arithmetic step directly in preservation to keep
/// the range structural invariant inductive. (#2171)
pub(in crate::callbacks) fn build_for_loop_transition_step_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    if !is_range_state_expr(&state.iter_state) {
        return None;
    }

    Some(PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_state_next.clone()),
            method: "start_log".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(state.iter_state.clone()),
                method: "start_log".to_string(),
                args: vec![],
            }),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    ))
}

/// Build a direct produced-length step fact for range-loop preservation.
///
/// The loop body appends the current range element to `produced`, so the
/// primed invariant contains `produced.push_back(loop_elem).len()`. Assert the
/// arithmetic step directly so preservation does not depend on recovering the
/// singleton-sequence length axiom through `push_back` rewriting. (#2323)
pub(in crate::callbacks) fn build_for_loop_produced_len_step_fact(
    state: &ForLoopGhostState,
) -> Option<PureExpr> {
    if !is_range_state_expr(&state.iter_state) {
        return None;
    }

    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    let produced_next = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "push_back".to_string(),
        args: vec![state.loop_elem.clone()],
    };

    Some(PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(produced_next),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(produced),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    ))
}

/// Build initialization facts for a for-loop (#2171, #1295, #1581).
///
/// When `state` is provided (full ghost state), generates:
/// 1. `produced == seq_empty()` — axiom matching
/// 2. `produced.len() == 0` — numeric fact for bare sequence invariants
/// 3. `produced@.len() == 0` — numeric variant/view fact
/// 4. `iter_state == <mir iterator expr>` — binds the synthetic current-state
///    variable to the MIR iterator expression at loop entry
/// 5. `iter_old == iter_state` — turns the synthetic old variable into a snapshot
/// 6. `iter_old.produces(produced, iter_state)` — exact synthesized invariant
///    seeded at loop entry so initialization does not depend on the solver
///    reconstructing reflexivity through equality-only reasoning
///
/// When `state` is `None`, falls back to the legacy behavior: scans invariants
/// for references to `produced` and generates facts 1-3 only.
pub(in crate::callbacks) fn build_for_loop_init_facts(
    invariants: &[PureExpr],
    state: Option<&ForLoopGhostState>,
) -> Vec<PureExpr> {
    let produced_name = state.map_or("produced", |s| s.produced_name.as_str());

    let refs_produced = invariants
        .iter()
        .any(|inv| expr_references_var(inv, produced_name));

    // Also check if invariants reference the iterator variable directly
    // (e.g., `iter@.get(k)` in FMap iterator invariants). Without this,
    // iterator-state init facts are skipped for user invariants that use
    // `iter@` but not `produced`, causing initialization failures. (#2116)
    let iter_binding_name = state.and_then(|st| match &st.iter_state_binding {
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    });
    let refs_iter = iter_binding_name
        .is_some_and(|name| invariants.iter().any(|inv| expr_references_var(inv, name)));

    // When for-loop ghost state is available, unconditionally generate init
    // facts. The structural produces invariant is auto-injected (#2171), so
    // init facts must not gate on whether the *user* already wrote an
    // invariant referencing `produced` or the iterator binding. Without
    // state, fall back to the legacy guard requiring at least one invariant
    // that references produced or the iterator.
    if state.is_none() && !refs_produced && !refs_iter {
        return vec![];
    }

    let mut facts = Vec::new();

    // Produced-specific facts: generated when invariants reference `produced`
    // OR when state is present (auto-injection means produced will be used
    // even if the user did not write it explicitly).
    if refs_produced || state.is_some() {
        facts.push(
            // Primary: produced == seq_empty() — enables axiom matching
            PureExpr::BinOp(
                Arc::new(PureExpr::Var(
                    produced_name.to_string(),
                    Some(ExprSort::Seq),
                )),
                BinOp::Eq,
                Arc::new(PureExpr::LogicFnCall {
                    name: "seq_empty".to_string(),
                    args: vec![],
                }),
            ),
        );
        facts.push(
            // Secondary: produced.len() == 0 — numeric fact for user invariants
            // that mention the bare ghost sequence.
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var(
                        produced_name.to_string(),
                        Some(ExprSort::Seq),
                    )),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            ),
        );
        facts.push(
            // Tertiary: produced@.len() == 0 — numeric fact for variant checks.
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        produced_name.to_string(),
                        Some(ExprSort::Seq),
                    )))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            ),
        );
    }

    // When full ghost state is available, bind the synthetic iterator-state
    // variable back to the MIR iterator expression, seed iter_old from that
    // current-state variable, and assert the exact structural invariant.
    // This keeps loop-entry initialization on the fast path for auto-generated
    // for-loop invariants, especially for range iterators where solver-side
    // `produces` reflexivity reconstruction is otherwise expensive. (#2171)
    if let Some(st) = state {
        facts.push(PureExpr::BinOp(
            Arc::new(st.iter_state.clone()),
            BinOp::Eq,
            Arc::new(st.iter_state_binding.clone()),
        ));
        facts.push(PureExpr::BinOp(
            Arc::new(st.iter_old.clone()),
            BinOp::Eq,
            Arc::new(st.iter_state.clone()),
        ));

        // Connect the iterator's initial view to the original collection
        // so user invariants like `iter@.get(k) == m_snap.get(k)` can be
        // established at initialization. For Seq-backed iterators this is
        // redundant (derivable from the structural invariant), but for FMap
        // iterators the produces predicate is quantified and does not
        // directly establish the View equivalence. (#2116)
        if let Some(ref iterable) = st.iterable {
            facts.push(PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(st.iter_state.clone()))),
                BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(iterable.clone()))),
            ));
        }

        // Unconditionally seed the structural invariant at initialization.
        // The auto-injected structural invariant must hold at loop entry;
        // gating on `invariants.contains` required the user to have already
        // written the produces invariant manually, defeating auto-injection.
        // (#2171)
        let structural_fact = super::super::iterator_spec_rewrite::rewrite_iterator_spec_expr(
            &build_for_loop_structural_invariant(st),
        );
        facts.push(structural_fact);
    }

    facts
}

/// Build range element bounds for for-range loops (#1709).
///
/// For `for elem in start..end`, synthesizes the active-iteration facts
/// `elem >= start` and `elem < end`. Callers must only assume these facts on
/// paths where the loop condition is known to hold; empty ranges do not provide
/// unconditional element bounds.
///
/// Only produces bounds when `range_bounds` is `Some` and `loop_elem` is a
/// named variable (not a synthetic `start_log()` expression).
pub(in crate::callbacks) fn build_for_loop_range_element_bounds(
    state: &ForLoopGhostState,
) -> Vec<PureExpr> {
    let Some((ref start, ref end)) = state.range_bounds else {
        return vec![];
    };
    // Only synthesize bounds when the loop element is a named variable.
    // Synthetic `iter_state.start_log()` expressions are internal and not
    // useful as inherited invariants for nested loops.
    let PureExpr::Var(ref _name, _) = state.loop_elem else {
        return vec![];
    };
    let mut bounds = Vec::new();
    // elem >= start
    bounds.push(PureExpr::BinOp(
        Arc::new(state.loop_elem.clone()),
        BinOp::Ge,
        Arc::new(start.clone()),
    ));
    // elem < end for exclusive ranges, elem <= end for inclusive ranges.
    bounds.push(PureExpr::BinOp(
        Arc::new(state.loop_elem.clone()),
        match range_state_kind(&state.iter_state) {
            Some(RangeLoopKind::Inclusive) => BinOp::Le,
            _ => BinOp::Lt,
        },
        Arc::new(end.clone()),
    ));
    bounds
}

/// Build condition-guarded range element facts for loop call obligations.
///
/// These facts are intentionally not raw loop invariants: for an empty range,
/// `elem >= start` and `elem < end` are only meaningful under the active loop
/// condition. Returning no facts without an extracted condition avoids making
/// empty-range bounds unconditional.
pub(in crate::callbacks) fn build_guarded_for_loop_range_element_facts(
    state: &ForLoopGhostState,
    condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    let Some(condition) = condition else {
        return Vec::new();
    };

    build_for_loop_range_element_bounds(state)
        .into_iter()
        .map(|bound| PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Implies, Arc::new(bound)))
        .collect()
}

/// Build guarded range element facts keyed to the call-obligation group condition.
///
/// Loop call obligations are verified under `LoopObligationGroup::condition`,
/// which is extracted independently from the loop body used for structural
/// loop verification. Use that exact condition when available so the obligation
/// checker can expose `condition ==> bound` facts on the active loop path.
/// Falling back to the body condition preserves the existing behavior for
/// callers without per-loop obligation groups.
pub(in crate::callbacks) fn build_group_guarded_for_loop_range_element_facts(
    state: &ForLoopGhostState,
    body_condition: Option<&PureExpr>,
    group_condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    build_guarded_for_loop_range_element_facts(state, group_condition.or(body_condition))
}

/// Build the active-iteration `produced.len() < total` bound for a range loop.
///
/// On an active iteration of `for elem in start..end` the iterator has NOT yet
/// been exhausted, so the number of elements produced so far is strictly less
/// than the total range length (`produced.len() == elem - start < total`). This
/// is the same soundness basis as `build_for_loop_range_element_bounds` (which
/// emits `elem < end`): both are facts about the current element under the active
/// loop condition, never unconditional.
///
/// foo1 in `bug/1396.rs` needs this bound to discharge its call obligation: the
/// invariant `(*r)@ == 13 + produced.len()` plus this bound gives `(*r)@ < 42`,
/// the closure's `#[requires]`. The bound is only meaningful guarded by the
/// active loop condition, so it is returned ungated here and the group-guarded
/// wrapper attaches the obligation-group condition (peer of the range-element
/// helpers above).
///
/// Only emitted for a range iterator with `range_bounds == Some(_)`. For an
/// exclusive range the total is `end - start`; for an inclusive range it is the
/// guarded inclusive length. Outside that shape this is a no-op.
pub(in crate::callbacks) fn build_for_loop_produced_len_bound(
    state: &ForLoopGhostState,
) -> Vec<PureExpr> {
    let Some(range_kind) = range_state_kind(&state.iter_state) else {
        return Vec::new();
    };
    let Some((start, end)) = state.range_bounds.as_ref() else {
        return Vec::new();
    };

    let total = match range_kind {
        RangeLoopKind::Exclusive => {
            PureExpr::BinOp(Arc::new(end.clone()), BinOp::Sub, Arc::new(start.clone()))
        }
        RangeLoopKind::Inclusive => inclusive_range_len_expr(start.clone(), end.clone()),
    };

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(
            state.produced_name.clone(),
            Some(ExprSort::Seq),
        )),
        method: "len".to_string(),
        args: vec![],
    };

    vec![PureExpr::BinOp(
        Arc::new(produced_len),
        BinOp::Lt,
        Arc::new(total),
    )]
}

/// Build the produced-length bound keyed to the call-obligation group condition.
///
/// Peer of `build_group_guarded_for_loop_range_element_facts`: attaches the
/// obligation-group condition (falling back to the body condition) so the
/// `produced.len() < total` bound is only assumed on the active loop path.
pub(in crate::callbacks) fn build_group_guarded_for_loop_produced_len_bound(
    state: &ForLoopGhostState,
    body_condition: Option<&PureExpr>,
    group_condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    let Some(condition) = group_condition.or(body_condition) else {
        return Vec::new();
    };
    build_for_loop_produced_len_bound(state)
        .into_iter()
        .map(|bound| PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Implies, Arc::new(bound)))
        .collect()
}

fn strip_view(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::View(inner) => strip_view(inner),
        _ => expr,
    }
}

fn same_seq_source(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    strip_view(lhs) == strip_view(rhs)
}

fn is_var_named(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

fn is_index_method(method: &str) -> bool {
    matches!(method, "index" | "index_logic")
}

fn source_expr_candidates(state: &ForLoopGhostState) -> Vec<PureExpr> {
    let mut candidates = Vec::new();
    if let Some(iterable) = state.iterable.as_ref() {
        candidates.push(iterable.clone());
    }
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &state.iter_state_binding
    {
        if method == "into_iter" && args.is_empty() {
            candidates.push(receiver.as_ref().clone());
        }
    }
    candidates
}

fn is_len_of_source(expr: &PureExpr, source: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { receiver, method, args }
            if method == "len" && args.is_empty() && same_seq_source(receiver, source)
    )
}

fn source_len_equals_int(facts: &[PureExpr], source: &PureExpr, expected: i64) -> bool {
    facts.iter().any(|fact| match fact {
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            (is_len_of_source(lhs, source)
                && matches!(rhs.as_ref(), PureExpr::Int(n) if *n == expected))
                || (matches!(lhs.as_ref(), PureExpr::Int(n) if *n == expected)
                    && is_len_of_source(rhs, source))
        }
        _ => false,
    })
}

fn antecedent_covers_source_index(
    antecedent: &PureExpr,
    source: &PureExpr,
    index_var: &str,
    source_facts: &[PureExpr],
) -> bool {
    let has_nonnegative = antecedent.any_recursive(|node| match node {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && is_var_named(rhs, index_var)
        }
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            is_var_named(lhs, index_var) && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        _ => false,
    });
    if !has_nonnegative {
        return false;
    }

    antecedent.any_recursive(|node| {
        let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = node else {
            return false;
        };
        if !is_var_named(lhs, index_var) {
            return false;
        }
        is_len_of_source(rhs, source)
            || matches!(
                rhs.as_ref(),
                PureExpr::Int(n) if source_len_equals_int(source_facts, source, *n)
            )
    })
}

fn replace_source_index_with_loop_elem(
    expr: &PureExpr,
    source: &PureExpr,
    index_var: &str,
    loop_elem: &PureExpr,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if is_index_method(&method)
            && args.len() == 1
            && is_var_named(&args[0], index_var)
            && same_seq_source(&receiver, source) =>
        {
            loop_elem.clone()
        }
        _ => node,
    })
}

fn flatten_conjuncts(expr: PureExpr, out: &mut Vec<PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            flatten_conjuncts(lhs.as_ref().clone(), out);
            flatten_conjuncts(rhs.as_ref().clone(), out);
        }
        other => out.push(other),
    }
}

fn expr_references_loop_elem(expr: &PureExpr, loop_elem: &PureExpr) -> bool {
    match loop_elem {
        PureExpr::Var(name, _) => expr.free_vars().contains(name),
        _ => expr.any_recursive(|node| node == loop_elem),
    }
}

fn push_guarded_fact(facts: &mut Vec<PureExpr>, condition: &PureExpr, fact: PureExpr) {
    let guarded = PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Implies, Arc::new(fact));
    if !facts.contains(&guarded) {
        facts.push(guarded);
    }
}

/// Build condition-guarded facts for the active element of a Seq-backed for-loop.
///
/// Trusted iterator sources such as `for m in moves()` place the source
/// postconditions in `pre_loop_init_facts`. Loop-call obligations, however, are
/// checked separately from loop initialization, so they need cheap active-element
/// instances such as `-2 <= m.0@ && m.0@ <= 2`. This helper only instantiates
/// quantified source facts that are tied to this loop's iterable and whose index
/// range is covered by a matching source length fact.
pub(in crate::callbacks) fn build_guarded_seq_for_loop_yielded_element_facts(
    state: &ForLoopGhostState,
    source_facts: &[PureExpr],
    condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    let Some(condition) = condition else {
        return Vec::new();
    };
    if !super::super::iterator_spec_rewrite::helpers::is_seq_backed_iterator(&state.iter_state) {
        return Vec::new();
    }

    let source_candidates = source_expr_candidates(state);
    if source_candidates.is_empty() {
        return Vec::new();
    }

    let mut facts = Vec::new();
    for source_fact in source_facts {
        let PureExpr::Forall { var, body, .. } = source_fact else {
            continue;
        };
        let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
            continue;
        };

        for source in &source_candidates {
            if !antecedent_covers_source_index(antecedent, source, var, source_facts) {
                continue;
            }
            let instantiated =
                replace_source_index_with_loop_elem(consequent, source, var, &state.loop_elem);
            if instantiated.free_vars().contains(var) {
                continue;
            }

            let mut conjuncts = Vec::new();
            flatten_conjuncts(instantiated, &mut conjuncts);
            for conjunct in conjuncts {
                if expr_references_loop_elem(&conjunct, &state.loop_elem) {
                    push_guarded_fact(&mut facts, condition, conjunct);
                }
            }
            break;
        }
    }

    facts
}

/// Build active-element facts keyed to the call-obligation group condition.
pub(in crate::callbacks) fn build_group_guarded_seq_for_loop_yielded_element_facts(
    state: &ForLoopGhostState,
    source_facts: &[PureExpr],
    body_condition: Option<&PureExpr>,
    group_condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    build_guarded_seq_for_loop_yielded_element_facts(
        state,
        source_facts,
        group_condition.or(body_condition),
    )
}

/// Build condition-guarded sequence element facts for loop call obligations.
///
/// For active `for elem in iterable` iterations, the current element is the
/// item at the produced prefix length. These facts let call-site preconditions
/// use trusted iterable postconditions such as `forall<i> ... result[i] ...`
/// without importing raw iterator-state postconditions into the obligation VC.
pub(in crate::callbacks) fn build_group_guarded_for_loop_seq_element_facts(
    state: &ForLoopGhostState,
    body_condition: Option<&PureExpr>,
    group_condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    if is_range_state_expr(&state.iter_state) {
        return Vec::new();
    }

    let Some(condition) = group_condition.or(body_condition) else {
        return Vec::new();
    };
    let iterable = state.iterable.as_ref().unwrap_or(&state.iter_old);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(
            state.produced_name.clone(),
            Some(ExprSort::Seq),
        )),
        method: "len".to_string(),
        args: vec![],
    };
    let iterable_view = PureExpr::View(Arc::new(iterable.clone()));
    let current_index = PureExpr::MethodCall {
        receiver: Arc::new(iterable_view.clone()),
        method: "index_logic".to_string(),
        args: vec![produced_len.clone()],
    };

    vec![
        PureExpr::BinOp(
            Arc::new(condition.clone()),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(produced_len.clone()),
                BinOp::Lt,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(iterable_view),
                    method: "len".to_string(),
                    args: vec![],
                }),
            )),
        ),
        PureExpr::BinOp(
            Arc::new(condition.clone()),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(state.loop_elem.clone()),
                BinOp::Eq,
                Arc::new(current_index),
            )),
        ),
    ]
}

/// Build postcondition completion facts for a for-loop (#2171, #1581).
/// Generates `produced == iterable` and `produced@ == iterable@` when state/iterable available.
pub(in crate::callbacks) fn build_for_loop_completion_facts(
    invariants: &[PureExpr],
    state: Option<&ForLoopGhostState>,
) -> Vec<PureExpr> {
    let Some(st) = state else {
        return vec![];
    };
    // When for-loop ghost state is present, completion facts are generated
    // unconditionally — the structural produces invariant is auto-injected
    // (#2171), so the user need not have written an invariant referencing
    // `produced` or the iterator binding.
    let _ = invariants; // Kept in signature for API stability; unused with auto-injection.
    let produced_name = st.produced_name.as_str();

    if let Some(range_kind) = range_state_kind(&st.iter_state) {
        let Some((start, end)) = st.range_bounds.as_ref() else {
            return Vec::new();
        };
        let range_len = match range_kind {
            RangeLoopKind::Exclusive => {
                let PureExpr::Int(0) = start else {
                    return vec![];
                };
                end.clone()
            }
            RangeLoopKind::Inclusive => inclusive_range_len_expr(start.clone(), end.clone()),
        };
        let produced = PureExpr::Var(produced_name.to_string(), Some(ExprSort::Seq));
        return vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(produced.clone()),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(range_len.clone()),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(produced))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(range_len),
            ),
        ];
    }

    if super::super::iterator_spec_rewrite::helpers::is_fmap_backed_iterator(&st.iter_state) {
        let mut facts = vec![PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(st.iter_state.clone()))),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "fmap_new".to_string(),
                args: vec![],
            }),
        )];
        if let Some(iterable) = st.iterable.as_ref() {
            // `iter_old` is the loop-entry snapshot of the iterator. Carry its
            // view-to-iterable bridge into postcondition checking so the exit
            // facts can still connect the exhausted iterator state back to the
            // original collection. Without this, logical FMap iterator VCs can
            // satisfy the structural invariant with an unconstrained empty
            // `iter_old`, even when the pre-loop iterable was non-empty. (#2116)
            facts.push(PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(st.iter_old.clone()))),
                BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(iterable.clone()))),
            ));
            facts.push(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        produced_name.to_string(),
                        Some(ExprSort::Seq),
                    )))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(iterable.clone()))),
                    method: "len".to_string(),
                    args: vec![],
                }),
            ));
        }
        return facts;
    }

    let Some(iterable) = st.iterable.as_ref() else {
        return vec![];
    };

    vec![
        // Bare equality: produced == iterable
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                produced_name.to_string(),
                Some(ExprSort::Seq),
            )),
            BinOp::Eq,
            Arc::new(iterable.clone()),
        ),
        // View equality: produced@ == iterable@
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                produced_name.to_string(),
                Some(ExprSort::Seq),
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(iterable.clone()))),
        ),
    ]
}
