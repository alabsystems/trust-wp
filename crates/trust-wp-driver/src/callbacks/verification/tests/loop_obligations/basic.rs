// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_ay::VerificationResult;
use trust_wp_core::{
    formula::{BinOp, PureExpr, UnOp},
    TrackLevel,
};

use crate::{
    callbacks::{
        indexed_write_synthesis::indexed_write_final_value_facts,
        parsing::LoopObligationGroup,
        verification::loop_contract::{verify_loop_call_obligations, LoopCallObligationContext},
    },
    mir_analysis::{IndexedWrite, MutBorrowBody},
};

fn is_len_call(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { method, args, .. } if method == "len" && args.is_empty()
    )
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn entry(name: &str) -> PureExpr {
    PureExpr::Deref(Arc::new(var(name)))
}

fn set(receiver: PureExpr, index: PureExpr, value: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(receiver))),
        method: "set".to_string(),
        args: vec![index, value],
    }
}

fn indexed_write(param: &str, index: PureExpr, value: PureExpr) -> IndexedWrite {
    IndexedWrite {
        param_name: param.to_string(),
        index,
        value,
    }
}

fn body_with(final_values: Vec<(&str, PureExpr)>, writes: Vec<IndexedWrite>) -> MutBorrowBody {
    MutBorrowBody {
        final_values: final_values
            .into_iter()
            .map(|(name, value)| (name.to_string(), value))
            .collect::<HashMap<_, _>>(),
        indexed_writes: writes,
        resolve_results: None,
        finality: HashMap::new(),
        borrow_id_origins: HashMap::new(),
        delayed_writeback_assumptions: vec![],
        mutation_continued_params: HashSet::new(),
        nested_slot_resolutions: vec![],
        nested_transfer_params: HashSet::new(),
        lent_path_resolutions: vec![],
    }
}

fn is_point_write(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(lhs, BinOp::Eq, _)
        if matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "index_logic")
    )
}

/// The antecedent of `guard ==> fact`, or `None` for an unconditional fact.
fn antecedent(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Implies, _) => Some(lhs.as_ref()),
        _ => None,
    }
}

fn consequent(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::BinOp(_, BinOp::Implies, rhs) => rhs.as_ref(),
        other => other,
    }
}

fn collect_frame_excluded_int_indices(expr: &PureExpr, out: &mut Vec<i64>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_frame_excluded_int_indices(lhs, out);
            collect_frame_excluded_int_indices(rhs, out);
        }
        PureExpr::BinOp(lhs, BinOp::Ne, rhs) => {
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "__iw_i") {
                if let PureExpr::Int(i) = rhs.as_ref() {
                    out.push(*i);
                }
            }
        }
        _ => {}
    }
}

/// Two writes on one path: the last write is stated as it is, the earlier one
/// only where the later write hits another index, and one frame excludes both.
#[test]
fn final_value_facts_state_a_write_only_where_no_later_write_may_overwrite_it() {
    let final_value = set(
        set(entry("a"), var("i"), PureExpr::Int(10)),
        var("j"),
        PureExpr::Int(20),
    );
    let body = body_with(
        vec![("a", final_value)],
        vec![
            indexed_write("a", var("i"), PureExpr::Int(10)),
            indexed_write("a", var("j"), PureExpr::Int(20)),
        ],
    );

    let facts = indexed_write_final_value_facts(&body, None, false);

    let point_writes: Vec<&PureExpr> = facts
        .iter()
        .filter(|fact| is_point_write(consequent(fact)))
        .collect();
    assert_eq!(point_writes.len(), 2);
    let last = point_writes
        .iter()
        .find(|fact| antecedent(fact).is_none())
        .expect("the last write holds on its whole path");
    assert!(
        matches!(consequent(last), PureExpr::BinOp(_, BinOp::Eq, value) if **value == PureExpr::Int(20))
    );
    let earlier = point_writes
        .iter()
        .find(|fact| antecedent(fact).is_some())
        .expect("the earlier write is guarded by the later write's index");
    assert_eq!(
        antecedent(earlier),
        Some(&PureExpr::BinOp(
            Arc::new(var("i")),
            BinOp::Ne,
            Arc::new(var("j"))
        ))
    );
    assert_eq!(
        facts
            .iter()
            .filter(|fact| matches!(fact, PureExpr::BinOp(lhs, BinOp::Eq, rhs) if is_len_call(lhs) && is_len_call(rhs)))
            .count(),
        1
    );
    let frame = facts
        .iter()
        .find(|fact| matches!(fact, PureExpr::Forall { .. }))
        .expect("the path over the entry value has a frame");
    let PureExpr::Forall { body, .. } = frame else {
        unreachable!()
    };
    let PureExpr::BinOp(frame_antecedent, BinOp::Implies, _) = body.as_ref() else {
        panic!("frame body should be an implication");
    };
    let mut excluded = Vec::new();
    collect_frame_excluded_int_indices(frame_antecedent, &mut excluded);
    assert!(
        excluded.is_empty(),
        "symbolic indices are excluded as terms, not literals"
    );
    assert!(format!("{frame_antecedent:?}").contains("\"j\""));
}

/// A write on one arm is a fact only under that arm's condition; the arm that
/// skips it keeps the whole entry value.
#[test]
fn final_value_facts_hold_only_on_the_writing_path() {
    let flag = PureExpr::Var("flag".to_string(), None);
    let final_value = PureExpr::Ite(
        Arc::new(flag.clone()),
        Arc::new(set(entry("a"), PureExpr::Int(0), PureExpr::Int(3))),
        Arc::new(entry("a")),
    );
    let body = body_with(
        vec![("a", final_value)],
        vec![indexed_write("a", PureExpr::Int(0), PureExpr::Int(3))],
    );

    let facts = indexed_write_final_value_facts(&body, None, false);

    let point_writes: Vec<&PureExpr> = facts
        .iter()
        .filter(|fact| is_point_write(consequent(fact)))
        .collect();
    assert_eq!(point_writes.len(), 1);
    assert_eq!(antecedent(point_writes[0]), Some(&flag));
    let not_flag = PureExpr::UnOp(UnOp::Not, Arc::new(flag.clone()));
    assert!(
        facts
            .iter()
            .all(|fact| !matches!(fact, PureExpr::Forall { .. })
                || format!("{fact:?}").contains("flag")),
        "every frame carries its path's condition"
    );
    assert!(facts.iter().any(|fact| antecedent(fact) == Some(&not_flag)));
    assert!(
        facts
            .iter()
            .all(|fact| antecedent(fact).is_some() || matches!(fact, PureExpr::Forall { .. })),
        "no fact about this final value holds on every path"
    );
}

/// A parameter the lane could not track exactly has no final value to read,
/// and one whose final value the dispatch replaces is not bound to the value
/// the facts would be read from.
#[test]
fn final_value_facts_skip_a_parameter_not_bound_to_its_final_value() {
    let mut body = body_with(
        vec![("a", set(entry("a"), PureExpr::Int(0), PureExpr::Int(3)))],
        vec![indexed_write("a", PureExpr::Int(0), PureExpr::Int(3))],
    );
    assert!(!indexed_write_final_value_facts(&body, None, false).is_empty());
    let overridden = HashMap::from([("a".to_string(), entry("a"))]);
    assert!(indexed_write_final_value_facts(&body, Some(&overridden), false).is_empty());
    body.mutation_continued_params.insert("a".to_string());
    assert!(indexed_write_final_value_facts(&body, None, false).is_empty());
    body.mutation_continued_params.clear();
    body.final_values.clear();
    assert!(indexed_write_final_value_facts(&body, None, false).is_empty());
}

/// Pre-loop obligation `i > 0` fails when invariant only gives `i >= 0`.
#[test]
fn loop_call_obligations_fail_when_not_implied_by_invariants() {
    let base_requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &obligations,
        loop_obligation_groups: &[],
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "expected failed loop call obligation, got {result:?}"
    );
}

/// A pre-loop obligation `i > 0` is NOT discharged by a loop invariant `i > 0`:
/// no loop invariant holds before the first loop runs
/// (`s40v5_preloop_call_later_invariant.rs`:
/// `need_pos(x); x = 5; #[invariant(x > 0)] loop {}` must not verify).
#[test]
fn pre_loop_obligations_do_not_assume_loop_invariants() {
    let base_requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &obligations,
        loop_obligation_groups: &[],
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "a pre-loop obligation must not assume a loop invariant, got {result:?}"
    );
}

/// In-loop obligation `i > 0` fails under `i >= 0` invariant even with loop
/// condition `i < n`, because `i >= 0 ∧ i < n` does not imply `i > 0` (i=0).
#[test]
fn in_loop_call_obligations_fail_when_not_implied_by_invariant_plus_condition() {
    let base_requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // In-loop obligation: i > 0
    let in_loop_obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    // Loop condition: i < n
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    let groups = [LoopObligationGroup {
        loop_index: Some(0),
        condition_unstated: None,
        pre_loop_stored_names: Default::default(),
        unstated_entry_values: Default::default(),
        injected_fail_closed: false,
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: Some(loop_condition),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &[],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    // i >= 0 ∧ i < n does NOT imply i > 0 (counterexample: i=0, n=1)
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "expected failed in-loop obligation (i=0 violates i > 0), got {result:?}"
    );
}

/// In-loop obligation `i >= 0` passes under invariant `i >= 0 ∧ i <= n`
/// with loop condition `i < n`.
#[test]
fn in_loop_call_obligations_verify_when_implied_by_invariant_plus_condition() {
    let base_requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Le,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        ),
    ];
    // In-loop obligation: i >= 0 (trivially implied by invariant)
    let in_loop_obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // Loop condition: i < n
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    let groups = [LoopObligationGroup {
        loop_index: Some(0),
        condition_unstated: None,
        pre_loop_stored_names: Default::default(),
        unstated_entry_values: Default::default(),
        injected_fail_closed: false,
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: Some(loop_condition),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &[],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected verified in-loop call obligations, got {result:?}"
    );
}

/// When pre-loop obligation fails, in-loop obligations should still be checked (#2010).
/// Both groups return Failed; the overall result should be Failed.
#[test]
fn loop_call_obligations_no_short_circuit_on_pre_loop_failure() {
    let base_requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // Pre-loop obligation: i > 0 (fails: counterexample i=0)
    let pre_loop_obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    // In-loop obligation: n < 0 (fails: counterexample n=0)
    let in_loop_obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(0)),
    )];

    let groups = [LoopObligationGroup {
        loop_index: Some(0),
        condition_unstated: None,
        pre_loop_stored_names: Default::default(),
        unstated_entry_values: Default::default(),
        injected_fail_closed: false,
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: None,
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &pre_loop_obligations,
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    // Both groups fail — overall result should be Failed, not just pre-loop's result.
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "expected Failed when both obligation groups fail, got {result:?}"
    );
}

/// When pre-loop obligation fails and in-loop verifies, the overall result
/// should still be Failed (worst-of aggregation, #2010).
#[test]
fn loop_call_obligations_pre_loop_fail_in_loop_verify() {
    let base_requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // Pre-loop obligation: i > 0 (fails: counterexample i=0)
    let pre_loop_obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    // In-loop obligation: i >= 0 (verifies under invariant i >= 0)
    let in_loop_obligations = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    let groups = [LoopObligationGroup {
        loop_index: Some(0),
        condition_unstated: None,
        pre_loop_stored_names: Default::default(),
        unstated_entry_values: Default::default(),
        injected_fail_closed: false,
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: Some(loop_condition),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &pre_loop_obligations,
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "expected Failed from pre-loop even when in-loop verifies, got {result:?}"
    );
}

/// Guarded in-loop obligation `(i < len) ==> (i < len)` verifies even when
/// the invariant alone (`i <= 10`) does not imply `i < len`. The guard
/// provides exactly the needed precondition. (#1295)
#[test]
fn guarded_in_loop_obligation_verifies_with_guard_providing_precondition() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Int(10)),
    )];
    // The obligation is guarded: `(i < len) ==> (i < len)` — trivially true.
    let guard = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("len".to_string(), None)),
    );
    let obligation = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("len".to_string(), None)),
    );
    let guarded_obligation = PureExpr::BinOp(Arc::new(guard), BinOp::Implies, Arc::new(obligation));
    let in_loop_obligations = vec![guarded_obligation];

    let groups = [LoopObligationGroup {
        loop_index: Some(0),
        condition_unstated: None,
        pre_loop_stored_names: Default::default(),
        unstated_entry_values: Default::default(),
        injected_fail_closed: false,
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: None,
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        per_loop_invariants: std::slice::from_ref(&invariants),
        pre_loop_obligations: &[],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        adt_field_ranges_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("guarded obligation verification should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected guarded obligation to verify, got {result:?}"
    );
}
