// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{
    intern_sort_name, internal::tuple_lowering::tuple_field_logic_fn_name, ExprSort,
};

use super::{
    build_fmap_identity_bridge_facts, build_for_loop_completion_facts, build_for_loop_init_facts,
    build_for_loop_literal_start_element_index_fact, build_for_loop_produced_len_bound,
    build_for_loop_produced_len_step_fact, build_for_loop_range_element_bounds,
    build_for_loop_range_element_current_fact, build_for_loop_structural_invariant,
    build_for_loop_transition_end_fact, build_for_loop_transition_fact,
    build_for_loop_transition_guard_fact, build_for_loop_transition_step_fact,
    build_for_loop_zero_start_element_index_fact, build_group_guarded_for_loop_produced_len_bound,
    build_group_guarded_for_loop_range_element_facts,
    build_group_guarded_for_loop_seq_element_facts, build_guarded_for_loop_range_element_facts,
    build_guarded_seq_for_loop_yielded_element_facts, build_transition_facts_for_loop_state,
    build_tuple_position_map, include_structural_invariant_in_loop_vc,
    is_for_loop_element_nonnegative_invariant, BinOp, ForLoopGhostState, PureExpr,
};

fn sample_for_loop_state() -> ForLoopGhostState {
    ForLoopGhostState {
        produced_name: "visited".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_7".to_string(), None),
        iter_state: PureExpr::Var("$for_iter_state_7".to_string(), None),
        iter_state_binding: PureExpr::Var("iter".to_string(), None),
        iter_state_next: PureExpr::Var("$for_iter_state_next_7".to_string(), None),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: Some(PureExpr::Old(Arc::new(PureExpr::Var(
            "input".to_string(),
            Some(ExprSort::Seq),
        )))),
        range_bounds: None,
    }
}

#[allow(clippy::unnecessary_wraps)] // Option return matches production API convention
fn mutref_range_sort() -> Option<ExprSort> {
    Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
        intern_sort_name("core::ops::range::Range"),
    ))))
}

fn sample_range_for_loop_state() -> ForLoopGhostState {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_8".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_8".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_8".to_string(), range_sort),
        loop_elem: PureExpr::Var("i".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: Some((
            PureExpr::Var("start".to_string(), Some(ExprSort::Int)),
            PureExpr::Var("end".to_string(), Some(ExprSort::Int)),
        )),
    }
}

fn sample_range_inclusive_for_loop_state() -> ForLoopGhostState {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::RangeInclusive",
    )));
    ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_8".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_8".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_8".to_string(), range_sort),
        loop_elem: PureExpr::Var("i".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: Some((
            PureExpr::Int(1),
            PureExpr::Var("end".to_string(), Some(ExprSort::Int)),
        )),
    }
}

#[test]
fn range_element_bounds_for_nested_loops_are_unguarded_active_facts() {
    let state = sample_range_for_loop_state();

    let facts = build_for_loop_range_element_bounds(&state);

    assert_eq!(
        facts,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Var("start".to_string(), Some(ExprSort::Int))),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
                BinOp::Lt,
                Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
            ),
        ],
        "a nested loop inside the for-loop body may assume active element bounds"
    );
}

#[test]
fn range_inclusive_element_bounds_use_closed_upper_bound() {
    let state = sample_range_inclusive_for_loop_state();

    let facts = build_for_loop_range_element_bounds(&state);

    assert_eq!(
        facts,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(1)),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
                BinOp::Le,
                Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
            ),
        ]
    );
}

#[test]
fn range_element_bounds_for_call_obligations_are_condition_guarded() {
    let state = sample_range_for_loop_state();
    let condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
        BinOp::Lt,
        Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
    );

    let facts = build_guarded_for_loop_range_element_facts(&state, Some(&condition));

    assert_eq!(
        facts,
        vec![
            PureExpr::BinOp(
                Arc::new(condition.clone()),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
                    BinOp::Ge,
                    Arc::new(PureExpr::Var("start".to_string(), Some(ExprSort::Int))),
                )),
            ),
            PureExpr::BinOp(
                Arc::new(condition),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
                    BinOp::Lt,
                    Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
                )),
            ),
        ],
        "range element bounds must be active-iteration implications"
    );
}

#[test]
fn inferred_nonnegative_fact_for_for_loop_element_is_not_raw_invariant() {
    let state = sample_range_for_loop_state();
    let elem_nonnegative = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let other_nonnegative = PureExpr::BinOp(
        Arc::new(PureExpr::Var("j".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    assert!(is_for_loop_element_nonnegative_invariant(
        &elem_nonnegative,
        Some(&state)
    ));
    assert!(!is_for_loop_element_nonnegative_invariant(
        &other_nonnegative,
        Some(&state)
    ));
    assert!(!is_for_loop_element_nonnegative_invariant(
        &elem_nonnegative,
        None
    ));
}

#[test]
fn range_element_bounds_for_call_obligations_absent_without_condition() {
    let state = sample_range_for_loop_state();

    assert!(
        build_guarded_for_loop_range_element_facts(&state, None).is_empty(),
        "missing loop condition must not produce unconditional range element bounds"
    );
}

#[test]
fn range_element_bounds_for_call_obligations_use_group_condition_when_available() {
    let state = sample_range_for_loop_state();
    let body_condition = PureExpr::Var("body_loop_active".to_string(), Some(ExprSort::Bool));
    let group_condition = PureExpr::Var("group_loop_active".to_string(), Some(ExprSort::Bool));

    let facts = build_group_guarded_for_loop_range_element_facts(
        &state,
        Some(&body_condition),
        Some(&group_condition),
    );

    assert!(
        facts.iter().all(|fact| matches!(
            fact,
            PureExpr::BinOp(lhs, BinOp::Implies, _) if lhs.as_ref() == &group_condition
        )),
        "call-obligation range facts must use the obligation group's exact condition: {facts:?}"
    );
    assert!(
        facts.iter().all(|fact| !matches!(
            fact,
            PureExpr::BinOp(lhs, BinOp::Implies, _) if lhs.as_ref() == &body_condition
        )),
        "body-extracted condition should not be used when a group condition is available: {facts:?}"
    );
}

#[test]
fn produced_len_bound_for_exclusive_range_is_strict_total_bound() {
    let state = sample_range_for_loop_state();

    let facts = build_for_loop_produced_len_bound(&state);

    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Lt,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
            BinOp::Sub,
            Arc::new(PureExpr::Var("start".to_string(), Some(ExprSort::Int))),
        )),
    );
    assert_eq!(
        facts,
        vec![expected],
        "an active iteration of `for _ in start..end` has produced fewer than `end - start` elements"
    );
}

#[test]
fn produced_len_bound_absent_for_non_range_loops() {
    // A non-range (sequence-backed) for-loop has no `range_bounds`, so no
    // produced-length bound is inferred.
    let state = sample_for_loop_state();
    assert!(
        build_for_loop_produced_len_bound(&state).is_empty(),
        "produced-length bound is only inferred for range iterators"
    );
}

#[test]
fn produced_len_bound_for_call_obligations_uses_group_condition() {
    let state = sample_range_for_loop_state();
    let body_condition = PureExpr::Var("body_loop_active".to_string(), Some(ExprSort::Bool));
    let group_condition = PureExpr::Var("group_loop_active".to_string(), Some(ExprSort::Bool));

    let facts = build_group_guarded_for_loop_produced_len_bound(
        &state,
        Some(&body_condition),
        Some(&group_condition),
    );

    assert_eq!(
        facts.len(),
        1,
        "exactly one guarded produced-length bound: {facts:?}"
    );
    assert!(
        matches!(
            &facts[0],
            PureExpr::BinOp(lhs, BinOp::Implies, _) if lhs.as_ref() == &group_condition
        ),
        "the produced-length bound must be guarded by the obligation group condition: {facts:?}"
    );
}

#[test]
fn produced_len_bound_for_call_obligations_absent_without_condition() {
    let state = sample_range_for_loop_state();
    assert!(
        build_group_guarded_for_loop_produced_len_bound(&state, None, None).is_empty(),
        "missing loop condition must not produce an unconditional produced-length bound"
    );
}

#[test]
fn seq_for_loop_yielded_element_facts_instantiate_source_bounds() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let source = PureExpr::Var(
        "moves_result".to_string(),
        Some(ExprSort::Datatype(intern_sort_name("alloc::vec::Vec"))),
    );
    let loop_elem = PureExpr::Var("m".to_string(), Some(ExprSort::Tuple(2)));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_17".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_17".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::MethodCall {
            receiver: Arc::new(source.clone()),
            method: "into_iter".to_string(),
            args: vec![],
        },
        iter_state_next: PureExpr::Var("$for_iter_next_17".to_string(), into_iter_sort),
        loop_elem: loop_elem.clone(),
        iterable: Some(source.clone()),
        range_bounds: None,
    };
    let source_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(source.clone()))),
        method: "len".to_string(),
        args: vec![],
    };
    let i = PureExpr::Var("i".to_string(), Some(ExprSort::Int));
    let indexed_source = PureExpr::MethodCall {
        receiver: Arc::new(source.clone()),
        method: "index_logic".to_string(),
        args: vec![i.clone()],
    };
    let indexed_dx = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![indexed_source],
    }));
    let source_facts = vec![
        PureExpr::BinOp(Arc::new(source_len), BinOp::Eq, Arc::new(PureExpr::Int(8))),
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::Int(0)),
                        BinOp::Le,
                        Arc::new(i.clone()),
                    )),
                    BinOp::And,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(i),
                        BinOp::Lt,
                        Arc::new(PureExpr::Int(8)),
                    )),
                )),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::Int(-2)),
                        BinOp::Le,
                        Arc::new(indexed_dx.clone()),
                    )),
                    BinOp::And,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(indexed_dx),
                        BinOp::Le,
                        Arc::new(PureExpr::Int(2)),
                    )),
                )),
            )),
            triggers: vec![],
        },
    ];
    let condition = PureExpr::Var("__iter_result_41_is_some".to_string(), Some(ExprSort::Bool));
    let yielded_dx = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![loop_elem],
    }));

    let facts =
        build_guarded_seq_for_loop_yielded_element_facts(&state, &source_facts, Some(&condition));

    assert_eq!(
        facts,
        vec![
            PureExpr::BinOp(
                Arc::new(condition.clone()),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(-2)),
                    BinOp::Le,
                    Arc::new(yielded_dx.clone()),
                )),
            ),
            PureExpr::BinOp(
                Arc::new(condition),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(yielded_dx),
                    BinOp::Le,
                    Arc::new(PureExpr::Int(2)),
                )),
            ),
        ],
        "trusted source element bounds should be instantiated onto the active yielded element"
    );
}

#[test]
fn seq_for_loop_yielded_element_facts_require_matching_source_len() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let source = PureExpr::Var("xs".to_string(), Some(ExprSort::Seq));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_9".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_9".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::MethodCall {
            receiver: Arc::new(source.clone()),
            method: "into_iter".to_string(),
            args: vec![],
        },
        iter_state_next: PureExpr::Var("$for_iter_next_9".to_string(), into_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: Some(source.clone()),
        range_bounds: None,
    };
    let i = PureExpr::Var("i".to_string(), Some(ExprSort::Int));
    let indexed_source = PureExpr::MethodCall {
        receiver: Arc::new(source),
        method: "index_logic".to_string(),
        args: vec![i.clone()],
    };
    let source_facts = vec![PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(i.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(i),
                    BinOp::Lt,
                    Arc::new(PureExpr::Int(8)),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(indexed_source),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
        )),
        triggers: vec![],
    }];
    let condition = PureExpr::Var("__iter_result_9_is_some".to_string(), Some(ExprSort::Bool));

    assert!(
        build_guarded_seq_for_loop_yielded_element_facts(&state, &source_facts, Some(&condition))
            .is_empty(),
        "literal-bounded source facts are not instantiated without a matching len fact"
    );
}

#[test]
fn for_loop_structural_invariant_uses_iter_old_produces_shape() {
    let state = sample_for_loop_state();

    let invariant = build_for_loop_structural_invariant(&state);

    assert_eq!(
        invariant,
        PureExpr::MethodCall {
            receiver: Arc::new(state.iter_old.clone()),
            method: "produces".to_string(),
            args: vec![
                PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq)),
                state.iter_state.clone(),
            ],
        }
    );
}

#[test]
fn for_loop_structural_invariant_uses_range_length_form_for_discarded_element() {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::Datatype(intern_sort_name(
                    "core::ops::range::Range",
                ))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    let invariant = build_for_loop_structural_invariant(&state);
    assert!(
        matches!(invariant, PureExpr::BinOp(_, BinOp::And, _)),
        "discarded-element range loops should use the length-form structural invariant: {invariant:?}"
    );
    assert!(
        !matches!(invariant, PureExpr::MethodCall { ref method, .. } if method == "produces"),
        "discarded-element range loops should not inject the full produces invariant: {invariant:?}"
    );
}

#[test]
fn for_loop_structural_invariant_uses_range_length_form_for_mutref_range_state() {
    let range_sort = mutref_range_sort();
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("core::ops::range::Range"),
                )))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    let invariant = build_for_loop_structural_invariant(&state);
    assert!(
        matches!(invariant, PureExpr::BinOp(_, BinOp::And, _)),
        "MutRef-wrapped range loops should still use the length-form structural invariant: {invariant:?}"
    );
    assert!(
        !matches!(invariant, PureExpr::MethodCall { ref method, .. } if method == "produces"),
        "MutRef-wrapped range loops should not fall back to the generic produces invariant: {invariant:?}"
    );
}

#[test]
fn range_inclusive_structural_invariant_uses_length_form_for_named_element() {
    let state = sample_range_inclusive_for_loop_state();

    let invariant = build_for_loop_structural_invariant(&state);

    assert!(
        matches!(invariant, PureExpr::BinOp(_, BinOp::And, _)),
        "RangeInclusive loops should use the direct length-form structural invariant: {invariant:?}"
    );
    assert!(
        !matches!(invariant, PureExpr::MethodCall { ref method, .. } if method == "produces"),
        "RangeInclusive loops should avoid generic produces preservation: {invariant:?}"
    );
}

/// SeqIter structural invariant uses direct equality `View(iter_old) ==
/// produced.concat(View(iter_state))` instead of `iter_old.produces(produced,
/// iter_state)`. This avoids the ext_eq Tseitin overhead that the produces
/// rewrite introduces. (#2116)
#[test]
fn seq_iter_structural_invariant_uses_direct_concat_equality() {
    let seq_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::seq::SeqIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_5".to_string(), seq_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_5".to_string(), seq_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), seq_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_5".to_string(), seq_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: None,
    };

    let invariant = build_for_loop_structural_invariant(&state);

    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(state.iter_old.clone()))),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
            method: "concat".to_string(),
            args: vec![PureExpr::View(Arc::new(state.iter_state.clone()))],
        }),
    );
    assert_eq!(
        invariant, expected,
        "SeqIter should use direct concat equality, not produces"
    );
}

/// Vec::IntoIter structural invariant also uses direct equality. (#2116)
#[test]
fn vec_into_iter_structural_invariant_uses_direct_concat_equality() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "visited".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_6".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_6".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), into_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_6".to_string(), into_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: None,
    };

    let invariant = build_for_loop_structural_invariant(&state);

    assert!(
        matches!(invariant, PureExpr::BinOp(_, BinOp::Eq, _)),
        "Vec::IntoIter should use direct equality, not produces: {invariant:?}"
    );
    assert!(
        !matches!(invariant, PureExpr::MethodCall { ref method, .. } if method == "produces"),
        "Vec::IntoIter should NOT produce a `produces` method call: {invariant:?}"
    );
}

#[test]
fn seq_for_loop_call_obligations_get_current_element_facts() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let condition = PureExpr::Var("__iter_result_9_is_some".to_string(), Some(ExprSort::Bool));
    let iterable = PureExpr::Var("moves_result".to_string(), None);
    let elem = PureExpr::Var("m".to_string(), None);
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_9".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_9".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), into_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_9".to_string(), into_iter_sort),
        loop_elem: elem.clone(),
        iterable: Some(iterable.clone()),
        range_bounds: None,
    };

    let facts = build_group_guarded_for_loop_seq_element_facts(&state, None, Some(&condition));

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
        method: "len".to_string(),
        args: vec![],
    };
    assert_eq!(facts.len(), 2, "expected active seq-loop element facts");
    assert!(facts.iter().all(|fact| {
        matches!(fact, PureExpr::BinOp(lhs, BinOp::Implies, _) if lhs.as_ref() == &condition)
    }));
    assert!(
        facts.iter().any(|fact| {
            matches!(
                fact,
                PureExpr::BinOp(_, BinOp::Implies, rhs)
                    if matches!(
                        rhs.as_ref(),
                        PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                            if lhs.as_ref() == &elem
                                && matches!(
                                    rhs.as_ref(),
                                    PureExpr::MethodCall { receiver, method, args }
                                        if method == "index_logic"
                                            && receiver.as_ref()
                                                == &PureExpr::View(Arc::new(iterable.clone()))
                                            && args == &vec![produced_len.clone()]
                                )
                    )
            )
        }),
        "expected current element to be tied to iterable[produced.len()], got {facts:?}"
    );
}

#[test]
fn for_loop_transition_fact_uses_synthetic_state_and_step_witness() {
    let state = sample_for_loop_state();

    let fact = build_for_loop_transition_fact(&state);

    assert_eq!(
        fact,
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
    );
}

#[test]
fn for_loop_transition_fact_rewrites_vec_into_iter_state() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "visited".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_9".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_9".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), into_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_9".to_string(), into_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: None,
    };

    let rewritten = super::super::super::iterator_spec_rewrite::rewrite_iterator_spec_expr(
        &build_for_loop_transition_fact(&state),
    );

    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = rewritten
    else {
        panic!("rewritten transition fact should be a method call");
    };
    assert_eq!(method, "ext_eq");
    assert!(matches!(receiver.as_ref(), PureExpr::View(_)));
    assert_eq!(args.len(), 1);
    assert!(
        matches!(&args[0], PureExpr::MethodCall { method, .. } if method == "concat"),
        "rewritten transition fact should concatenate the singleton step sequence with iter_state_next@: {:?}",
        args[0]
    );
}

#[test]
fn for_loop_transition_end_fact_keeps_range_end_constant() {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::Datatype(intern_sort_name(
                    "core::ops::range::Range",
                ))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    assert_eq!(
        build_for_loop_transition_end_fact(&state),
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
    );
}

#[test]
fn zero_start_range_transition_binds_element_to_produced_len() {
    let mut state = sample_range_for_loop_state();
    state.range_bounds = Some((
        PureExpr::Int(0),
        PureExpr::Var("end".to_string(), Some(ExprSort::Int)),
    ));

    assert_eq!(
        build_for_loop_zero_start_element_index_fact(&state),
        Some(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
                method: "len".to_string(),
                args: vec![],
            }),
        ))
    );
}

#[test]
fn nonzero_start_range_does_not_bind_element_to_produced_len() {
    let state = sample_range_for_loop_state();

    assert_eq!(
        build_for_loop_zero_start_element_index_fact(&state),
        None,
        "i == produced.len() is only sound for ranges whose recovered start is literal zero"
    );
}

#[test]
fn literal_start_range_binds_element_to_produced_len_plus_start() {
    let mut state = sample_range_for_loop_state();
    state.range_bounds = Some((
        PureExpr::Int(1),
        PureExpr::Var("end".to_string(), Some(ExprSort::Int)),
    ));

    assert_eq!(
        build_for_loop_literal_start_element_index_fact(&state),
        Some(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        ))
    );
}

#[test]
fn range_inclusive_transition_facts_include_literal_start_offset() {
    let state = sample_range_inclusive_for_loop_state();
    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced),
        method: "len".to_string(),
        args: vec![],
    };

    let facts = build_transition_facts_for_loop_state(&state);

    assert!(
        facts.contains(&PureExpr::BinOp(
            Arc::new(state.loop_elem.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(produced_len),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        )),
        "1..=end preservation needs i == produced.len() + 1, got {facts:?}"
    );
    assert!(
        facts.iter().any(|fact| matches!(
            fact,
            PureExpr::BinOp(_, BinOp::Le, rhs)
                if matches!(rhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "end_log")
        )),
        "inclusive range guard should use <= end_log, got {facts:?}"
    );
}

#[test]
fn range_loop_transition_facts_use_direct_arithmetic_form() {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::Datatype(intern_sort_name(
                    "core::ops::range::Range",
                ))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    assert_eq!(
        build_transition_facts_for_loop_state(&state),
        vec![
            build_for_loop_transition_end_fact(&state)
                .expect("range loops should keep end bound stable"),
            build_for_loop_transition_guard_fact(&state)
                .expect("range loops should add current-step bound"),
            build_for_loop_range_element_current_fact(&state)
                .expect("range loops should bind loop element to current start"),
            build_for_loop_transition_step_fact(&state)
                .expect("range loops should add one-step start advance"),
            build_for_loop_produced_len_step_fact(&state)
                .expect("range loops should add produced-length progression"),
        ]
    );
}

#[test]
fn mutref_range_loop_transition_facts_use_direct_arithmetic_form() {
    let range_sort = mutref_range_sort();
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("core::ops::range::Range"),
                )))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    assert_eq!(
        build_transition_facts_for_loop_state(&state),
        vec![
            build_for_loop_transition_end_fact(&state)
                .expect("MutRef-wrapped range loops should keep end bound stable"),
            build_for_loop_transition_guard_fact(&state)
                .expect("MutRef-wrapped range loops should add current-step bound"),
            build_for_loop_range_element_current_fact(&state)
                .expect("MutRef-wrapped range loops should bind loop element to current start"),
            build_for_loop_transition_step_fact(&state)
                .expect("MutRef-wrapped range loops should add one-step start advance"),
            build_for_loop_produced_len_step_fact(&state)
                .expect("MutRef-wrapped range loops should add produced-length progression"),
        ]
    );
}

#[test]
fn non_range_loop_transition_facts_rewrite_generic_produces() {
    let state = sample_for_loop_state();

    assert_eq!(
        build_transition_facts_for_loop_state(&state),
        vec![
            super::super::super::iterator_spec_rewrite::rewrite_iterator_spec_expr(
                &build_for_loop_transition_fact(&state),
            )
        ]
    );
}

/// SeqIter transition facts use direct push_front equality instead of the
/// ext_eq+concat form. This avoids quantifier overhead from the ext_eq
/// Tseitin encoding and concat/singleton bridging axioms. (#2116)
#[test]
fn seq_iter_transition_facts_use_direct_push_front() {
    let seq_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::seq::SeqIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_3".to_string(), seq_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_3".to_string(), seq_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), seq_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_3".to_string(), seq_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: None,
    };

    let facts = build_transition_facts_for_loop_state(&state);
    assert_eq!(
        facts.len(),
        1,
        "SeqIter should produce exactly one transition fact"
    );

    // Expected: View(iter_state) == push_front_ghost(View(iter_state_next), elem)
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_next.clone()))),
            method: "push_front_ghost".to_string(),
            args: vec![state.loop_elem.clone()],
        }),
    );
    assert_eq!(facts[0], expected);
}

/// Vec::IntoIter is also a Seq-backed iterator and should use the same
/// direct push_front transition fact path. (#2116)
#[test]
fn vec_into_iter_transition_facts_use_direct_push_front() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_4".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_4".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), into_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_4".to_string(), into_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: None,
        range_bounds: None,
    };

    let facts = build_transition_facts_for_loop_state(&state);
    assert_eq!(
        facts.len(),
        1,
        "Vec::IntoIter should produce exactly one transition fact"
    );

    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_next.clone()))),
            method: "push_front_ghost".to_string(),
            args: vec![state.loop_elem.clone()],
        }),
    );
    assert_eq!(facts[0], expected);
}

#[test]
fn logical_fmap_iter_transition_facts_use_direct_map_delta() {
    let fmap_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::fmap::FMapIter",
    )));
    let entry = PureExpr::Var("entry".to_string(), Some(ExprSort::Tuple(2)));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_13".to_string(), fmap_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_13".to_string(), fmap_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), fmap_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_13".to_string(), fmap_iter_sort),
        loop_elem: entry.clone(),
        iterable: None,
        range_bounds: None,
    };

    let facts = build_transition_facts_for_loop_state(&state);
    assert_eq!(
        facts.len(),
        6,
        "logical FMapIter should use the six-fact contains/lookup delta encoding"
    );

    let key_dm = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![entry.clone()],
        }),
        method: "deep_model".to_string(),
        args: vec![],
    };
    assert_eq!(
        facts[0],
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_next.clone()))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        )
    );
    assert_eq!(
        facts[1],
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
            method: "contains".to_string(),
            args: vec![key_dm.clone()],
        }
    );
    assert_eq!(
        facts[2],
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
                method: "lookup".to_string(),
                args: vec![key_dm.clone()],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![entry],
            }),
        )
    );
    // facts[3]: !contains(next_view, entry_key)
    assert_eq!(
        facts[3],
        PureExpr::UnOp(
            trust_wp_core::formula::UnOp::Not,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_next.clone()))),
                method: "contains".to_string(),
                args: vec![key_dm],
            }),
        )
    );
    // facts[4]: singly-quantified forward frame (contains/lookup preserved)
    assert!(
        matches!(facts[4], PureExpr::Forall { .. }),
        "remaining-entry preservation should be quantified: {:?}",
        facts[4]
    );
    // facts[5]: singly-quantified reverse frame
    assert!(
        matches!(facts[5], PureExpr::Forall { .. }),
        "next-entry origin fact should be quantified: {:?}",
        facts[5]
    );
}

#[test]
fn fmap_identity_bridge_facts_follow_tuple_destructure_positions() {
    let borrow_vars = vec!["k2".to_string(), "v2".to_string()];
    let entry = PureExpr::Var("entry".to_string(), Some(ExprSort::Tuple(2)));
    let body_effect = std::collections::HashMap::from([
        (
            "k2".to_string(),
            PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![entry.clone()],
            },
        ),
        (
            "v2".to_string(),
            PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![entry],
            },
        ),
    ]);

    let pos_map = build_tuple_position_map(&borrow_vars, &body_effect);
    let facts =
        build_fmap_identity_bridge_facts(&[("bor_k".to_string(), "bor_v".to_string())], &pos_map);

    assert_eq!(
        facts,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "k2".to_string(),
                    None,
                )))),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "bor_k".to_string(),
                    None,
                )))),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "v2".to_string(),
                    None,
                )))),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "bor_v".to_string(),
                    None,
                )))),
            ),
        ],
        "FMap bridge facts should align tuple-field destructuring with the \
         inserted borrow finals"
    );
}

#[test]
fn logical_fmap_iter_structural_invariant_auto_injected_even_when_produced_unused() {
    let fmap_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::fmap::FMapIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_14".to_string(), fmap_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_14".to_string(), fmap_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), fmap_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_14".to_string(), fmap_iter_sort),
        loop_elem: PureExpr::Var("entry".to_string(), Some(ExprSort::Tuple(2))),
        iterable: None,
        range_bounds: None,
    };
    let iter_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_binding.clone()))),
        method: "len".to_string(),
        args: vec![],
    };
    let invariants = vec![PureExpr::BinOp(
        Arc::new(iter_len.clone()),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let variant = PureExpr::BinOp(Arc::new(iter_len), BinOp::Sub, Arc::new(PureExpr::Int(0)));

    // After #2171 auto-injection: the structural invariant is always included
    // for all for-loop iterator types, including FMap. Users should not need
    // to manually write `iter_old.produces(produced, iter)`.
    assert!(
        include_structural_invariant_in_loop_vc(&state, &invariants, &[], None, Some(&variant),),
        "structural invariant should be auto-injected for all for-loops including FMap (#2171)",
    );
}

#[test]
fn logical_fmap_iter_structural_invariant_stays_when_produced_is_used() {
    let fmap_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::fmap::FMapIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_15".to_string(), fmap_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_15".to_string(), fmap_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), fmap_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_15".to_string(), fmap_iter_sort),
        loop_elem: PureExpr::Var("entry".to_string(), Some(ExprSort::Tuple(2))),
        iterable: None,
        range_bounds: None,
    };
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            state.produced_name.clone(),
            Some(ExprSort::Seq),
        )))),
        method: "len".to_string(),
        args: vec![],
    };
    let invariants = vec![PureExpr::BinOp(
        Arc::new(produced_len),
        BinOp::Le,
        Arc::new(PureExpr::Int(1)),
    )];

    assert!(
        include_structural_invariant_in_loop_vc(&state, &invariants, &[], None, None),
        "produced-aware logical FMap invariants must keep the synthetic structural invariant in the loop VC",
    );
}

#[test]
fn for_loop_transition_guard_fact_bounds_range_current_state() {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::Datatype(intern_sort_name(
                    "core::ops::range::Range",
                ))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    assert_eq!(
        build_for_loop_transition_guard_fact(&state),
        Some(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(state.iter_state.clone()),
                method: "start_log".to_string(),
                args: vec![],
            }),
            BinOp::Lt,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(state.iter_old.clone()),
                method: "end_log".to_string(),
                args: vec![],
            }),
        ))
    );
}

#[test]
fn for_loop_transition_step_fact_advances_range_start_by_one() {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::Datatype(intern_sort_name(
                    "core::ops::range::Range",
                ))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    assert_eq!(
        build_for_loop_transition_step_fact(&state),
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
    );
}

#[test]
fn for_loop_produced_len_step_fact_advances_by_one() {
    let range_sort = Some(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_2".to_string(), range_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_2".to_string(), range_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), range_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_2".to_string(), range_sort),
        loop_elem: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "$for_iter_state_2".to_string(),
                Some(ExprSort::Datatype(intern_sort_name(
                    "core::ops::range::Range",
                ))),
            )),
            method: "start_log".to_string(),
            args: vec![],
        },
        iterable: None,
        range_bounds: None,
    };

    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    let produced_next = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "push_back".to_string(),
        args: vec![state.loop_elem.clone()],
    };

    assert_eq!(
        build_for_loop_produced_len_step_fact(&state),
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
    );
}

#[test]
fn for_loop_init_facts_include_seq_empty_len_zero_and_iter_snapshot_equality() {
    let state = sample_for_loop_state();
    let structural = build_for_loop_structural_invariant(&state);
    let invariants = vec![structural.clone()];

    let init_facts = build_for_loop_init_facts(&invariants, Some(&state));

    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    assert_eq!(
        init_facts.len(),
        7,
        "for-loop init facts should include bare/view produced length facts and the seeded structural invariant"
    );
    assert_eq!(
        init_facts[0],
        PureExpr::BinOp(
            Arc::new(produced.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "seq_empty".to_string(),
                args: vec![],
            }),
        )
    );
    assert_eq!(
        init_facts[1],
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(produced.clone()),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )
    );
    assert_eq!(
        init_facts[2],
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(produced.clone()))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )
    );
    assert_eq!(
        init_facts[3],
        PureExpr::BinOp(
            Arc::new(state.iter_state.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state_binding.clone()),
        )
    );
    assert_eq!(
        init_facts[4],
        PureExpr::BinOp(
            Arc::new(state.iter_old.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state.clone()),
        )
    );
    let iterable = state
        .iterable
        .as_ref()
        .expect("sample state should include iterable payload");
    assert_eq!(
        init_facts[5],
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(iterable.clone()))),
        )
    );
    assert_eq!(init_facts[6], structural);
}

#[test]
fn for_loop_init_facts_allow_non_var_iter_state_binding() {
    let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "alloc::vec::into_iter::IntoIter",
    )));
    let ghost_seq_sort = Some(ExprSort::Datatype(intern_sort_name("trust_wp::GhostSeq")));
    let state = ForLoopGhostState {
        produced_name: "visited".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_11".to_string(), into_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_11".to_string(), into_iter_sort.clone()),
        iter_state_binding: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("input".to_string(), ghost_seq_sort)),
            method: "into_inner".to_string(),
            args: vec![],
        },
        iter_state_next: PureExpr::Var("$for_iter_state_next_11".to_string(), into_iter_sort),
        loop_elem: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        iterable: Some(PureExpr::Old(Arc::new(PureExpr::Var(
            "input".to_string(),
            Some(ExprSort::Seq),
        )))),
        range_bounds: None,
    };
    let structural = super::super::super::iterator_spec_rewrite::rewrite_iterator_spec_expr(
        &build_for_loop_structural_invariant(&state),
    );
    let invariants = vec![structural.clone()];

    let init_facts = build_for_loop_init_facts(&invariants, Some(&state));

    assert_eq!(
        init_facts.len(),
        7,
        "non-Var iterator bindings should still seed the full for-loop init fact set"
    );
    assert_eq!(
        init_facts[3],
        PureExpr::BinOp(
            Arc::new(state.iter_state.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state_binding.clone()),
        )
    );
    assert_eq!(init_facts[6], structural);
}

#[test]
fn for_loop_init_facts_without_iterable_payload_skip_iter_snapshot_fact() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "produced".to_string(),
                Some(ExprSort::Seq),
            )))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let init_facts = build_for_loop_init_facts(&invariants, None);

    assert_eq!(
        init_facts.len(),
        3,
        "range-style for-loops should keep produced init facts without injecting iter snapshots"
    );
}

#[test]
fn for_loop_init_facts_with_range_style_state_keep_iter_snapshot_fact() {
    let mut state = sample_for_loop_state();
    state.iterable = None;
    let structural = build_for_loop_structural_invariant(&state);
    let invariants = vec![structural.clone()];

    let init_facts = build_for_loop_init_facts(&invariants, Some(&state));

    assert_eq!(
        init_facts.len(),
        6,
        "range-style for-loops should still seed iter_state/iter_old bindings and the structural invariant when ghost state exists"
    );
    assert_eq!(
        init_facts[3],
        PureExpr::BinOp(
            Arc::new(state.iter_state.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state_binding.clone()),
        )
    );
    assert_eq!(
        init_facts[4],
        PureExpr::BinOp(
            Arc::new(state.iter_old.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state.clone()),
        )
    );
    assert_eq!(init_facts[5], structural);
}

#[test]
fn for_loop_init_facts_seed_iter_snapshot_when_invariant_refs_iter_only() {
    let state = sample_for_loop_state();
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(state.iter_state_binding.clone()))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let init_facts = build_for_loop_init_facts(&invariants, Some(&state));

    // After #2171 auto-injection: when state is present, produced init facts
    // are always generated even if the user invariant only references the
    // iterator binding. This ensures the structural invariant can be checked
    // at initialization.
    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    assert_eq!(
        init_facts.len(),
        7,
        "for-loop state present: produced + iter snapshot + View + structural (#2171)",
    );
    assert_eq!(
        init_facts[0],
        PureExpr::BinOp(
            Arc::new(produced.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "seq_empty".to_string(),
                args: vec![],
            }),
        )
    );
    assert_eq!(
        init_facts[3],
        PureExpr::BinOp(
            Arc::new(state.iter_state.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state_binding.clone()),
        )
    );
    assert_eq!(
        init_facts[4],
        PureExpr::BinOp(
            Arc::new(state.iter_old.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state.clone()),
        )
    );
    let iterable = state
        .iterable
        .as_ref()
        .expect("sample state should include iterable payload");
    assert_eq!(
        init_facts[5],
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(iterable.clone()))),
        )
    );
}

#[test]
fn for_loop_completion_facts_reuse_for_loop_iterable_payload() {
    let state = sample_for_loop_state();
    let invariants = vec![build_for_loop_structural_invariant(&state)];

    let completion_facts = build_for_loop_completion_facts(&invariants, Some(&state));
    let iterable = state
        .iterable
        .clone()
        .expect("sample state should include iterable payload");

    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    assert_eq!(
        completion_facts,
        vec![
            PureExpr::BinOp(
                Arc::new(produced.clone()),
                BinOp::Eq,
                Arc::new(iterable.clone()),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(produced))),
                BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(iterable))),
            ),
        ]
    );
}

#[test]
fn for_loop_completion_facts_skip_non_sequence_iterables() {
    let mut state = sample_for_loop_state();
    state.iterable = None;
    let invariants = vec![build_for_loop_structural_invariant(&state)];

    let completion_facts = build_for_loop_completion_facts(&invariants, Some(&state));

    assert!(
        completion_facts.is_empty(),
        "range-style for-loops should skip completion facts when no iterable payload is available"
    );
}

#[test]
fn zero_start_range_completion_facts_bind_produced_len_to_end() {
    let mut state = sample_range_for_loop_state();
    state.range_bounds = Some((
        PureExpr::Int(0),
        PureExpr::Var("end".to_string(), Some(ExprSort::Int)),
    ));
    let invariants = vec![build_for_loop_structural_invariant(&state)];

    let completion_facts = build_for_loop_completion_facts(&invariants, Some(&state));
    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));

    assert_eq!(
        completion_facts,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(produced.clone()),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(produced))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::Var("end".to_string(), Some(ExprSort::Int))),
            ),
        ],
        "0..end loops should expose the exhausted produced prefix length to postconditions"
    );
}

#[test]
fn nonzero_range_completion_facts_do_not_bind_produced_len_to_end() {
    let state = sample_range_for_loop_state();
    let invariants = vec![build_for_loop_structural_invariant(&state)];

    assert!(
        build_for_loop_completion_facts(&invariants, Some(&state)).is_empty(),
        "produced.len() == end is only sound for literal zero-start ranges"
    );
}

#[test]
fn range_inclusive_completion_facts_use_piecewise_trip_count() {
    let state = sample_range_inclusive_for_loop_state();
    let invariants = vec![build_for_loop_structural_invariant(&state)];

    let completion_facts = build_for_loop_completion_facts(&invariants, Some(&state));
    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    let end = PureExpr::Var("end".to_string(), Some(ExprSort::Int));
    let trip_count = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(end.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::Int(1)),
        )),
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(end.clone()),
                BinOp::Sub,
                Arc::new(PureExpr::Int(1)),
            )),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
        Arc::new(PureExpr::Int(0)),
    );

    assert_eq!(
        completion_facts,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(produced.clone()),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(trip_count.clone()),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(produced))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(trip_count),
            ),
        ]
    );
}

#[test]
fn for_loop_completion_facts_use_empty_fmap_for_fmap_iterators() {
    let fmap_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::fmap::FMapIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_12".to_string(), fmap_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_12".to_string(), fmap_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), fmap_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_12".to_string(), fmap_iter_sort),
        loop_elem: PureExpr::Var("entry".to_string(), Some(ExprSort::Tuple(2))),
        iterable: Some(PureExpr::Old(Arc::new(PureExpr::Var(
            "m".to_string(),
            Some(ExprSort::FMap),
        )))),
        range_bounds: None,
    };
    let invariants = vec![build_for_loop_structural_invariant(&state)];

    let completion_facts = build_for_loop_completion_facts(&invariants, Some(&state));

    assert_eq!(
        completion_facts,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(state.iter_state.clone()))),
                BinOp::Eq,
                Arc::new(PureExpr::LogicFnCall {
                    name: "fmap_new".to_string(),
                    args: vec![],
                }),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(state.iter_old.clone()))),
                BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(
                    state
                        .iterable
                        .clone()
                        .expect("logical FMap test state should include iterable payload"),
                ))),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        state.produced_name.clone(),
                        Some(ExprSort::Seq),
                    )))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(
                        state
                            .iterable
                            .clone()
                            .expect("logical FMap test state should include iterable payload"),
                    ))),
                    method: "len".to_string(),
                    args: vec![],
                }),
            ),
        ],
        "FMap-backed iterators should carry exhaustion, entry-snapshot, and produced-length facts into postcondition checking"
    );
}

/// #2171: init facts are generated even when no user invariant references
/// `produced` or the iterator binding. The structural invariant is
/// auto-injected, so init facts must seed unconditionally when for-loop
/// ghost state is present.
#[test]
fn for_loop_init_facts_auto_inject_without_user_produced_invariant() {
    let state = sample_for_loop_state();
    // User wrote no invariant at all — empty invariants list.
    let invariants: Vec<PureExpr> = vec![];

    let init_facts = build_for_loop_init_facts(&invariants, Some(&state));

    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    // Even with no user invariants, all 7 init facts should be present:
    // [0] produced == seq_empty()
    // [1] produced.len() == 0
    // [2] produced@.len() == 0
    // [3] iter_state == iter (binding)
    // [4] iter_old == iter_state
    // [5] View(iter_state) == View(iterable)
    // [6] structural invariant seed
    assert_eq!(
        init_facts.len(),
        7,
        "auto-injection: for-loop init facts must fire even with no user invariants (#2171)"
    );
    assert_eq!(
        init_facts[0],
        PureExpr::BinOp(
            Arc::new(produced.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "seq_empty".to_string(),
                args: vec![],
            }),
        ),
        "produced == seq_empty() should be present"
    );
    assert_eq!(
        init_facts[3],
        PureExpr::BinOp(
            Arc::new(state.iter_state.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state_binding.clone()),
        ),
        "iter_state == iter binding should be present"
    );
    assert_eq!(
        init_facts[4],
        PureExpr::BinOp(
            Arc::new(state.iter_old.clone()),
            BinOp::Eq,
            Arc::new(state.iter_state.clone()),
        ),
        "iter_old == iter_state should be present"
    );
}

/// #2171: completion facts are generated even when no user invariant
/// references `produced`. The auto-injected structural invariant means
/// the postcondition path should always get completion facts for
/// iterator exhaustion.
#[test]
fn for_loop_completion_facts_auto_inject_without_user_produced_invariant() {
    let state = sample_for_loop_state();
    // User wrote no invariant referencing produced.
    let invariants: Vec<PureExpr> = vec![];

    let completion_facts = build_for_loop_completion_facts(&invariants, Some(&state));

    let iterable = state
        .iterable
        .clone()
        .expect("sample state should include iterable payload");
    let produced = PureExpr::Var(state.produced_name.clone(), Some(ExprSort::Seq));
    assert_eq!(
        completion_facts,
        vec![
            PureExpr::BinOp(
                Arc::new(produced.clone()),
                BinOp::Eq,
                Arc::new(iterable.clone()),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(produced))),
                BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(iterable))),
            ),
        ],
        "auto-injection: completion facts must fire even with no user invariants (#2171)"
    );
}

/// #2171: FMap structural invariant is auto-injected unconditionally.
/// Users should not need to manually reference `produced` for the
/// structural invariant to be included in the loop VC.
#[test]
fn for_loop_fmap_structural_invariant_always_auto_injected() {
    let fmap_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::logic::fmap::FMapIter",
    )));
    let state = ForLoopGhostState {
        produced_name: "produced".to_string(),
        iter_old: PureExpr::Var("$for_iter_old_20".to_string(), fmap_iter_sort.clone()),
        iter_state: PureExpr::Var("$for_iter_state_20".to_string(), fmap_iter_sort.clone()),
        iter_state_binding: PureExpr::Var("iter".to_string(), fmap_iter_sort.clone()),
        iter_state_next: PureExpr::Var("$for_iter_state_next_20".to_string(), fmap_iter_sort),
        loop_elem: PureExpr::Var("entry".to_string(), Some(ExprSort::Tuple(2))),
        iterable: None,
        range_bounds: None,
    };
    // No user invariants at all.
    let invariants: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![];

    assert!(
        include_structural_invariant_in_loop_vc(&state, &invariants, &ensures, None, None),
        "FMap structural invariant should be auto-injected even with no user invariants (#2171)"
    );
}
