// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_ay::VerificationResult;
use trust_wp_core::{
    formula::{BinOp, PureExpr},
    TrackLevel,
};

use crate::{
    callbacks::{
        indexed_write_synthesis::synthesize_indexed_write_postconditions,
        parsing::LoopObligationGroup,
        verification::loop_contract::{verify_loop_call_obligations, LoopCallObligationContext},
    },
    mir_analysis::IndexedWrite,
};

fn is_len_call(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { method, args, .. } if method == "len" && args.is_empty()
    )
}

fn count_top_level_point_writes(requires: &[PureExpr]) -> usize {
    requires
        .iter()
        .filter(|expr| {
            matches!(
                expr,
                PureExpr::BinOp(lhs, BinOp::Eq, _)
                if matches!(
                    lhs.as_ref(),
                    PureExpr::MethodCall { method, .. } if method == "index_logic"
                )
            )
        })
        .count()
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

#[test]
fn indexed_write_synthesis_combines_frame_for_same_parameter() {
    let indexed_writes = vec![
        IndexedWrite {
            param_name: "a".to_string(),
            index: PureExpr::Int(0),
            value: PureExpr::Int(10),
        },
        IndexedWrite {
            param_name: "a".to_string(),
            index: PureExpr::Int(1),
            value: PureExpr::Int(20),
        },
    ];
    let mut requires = Vec::new();

    synthesize_indexed_write_postconditions(&indexed_writes, &mut requires, false);

    assert_eq!(count_top_level_point_writes(&requires), 2);
    assert_eq!(
        requires
            .iter()
            .filter(|expr| matches!(expr, PureExpr::Forall { .. }))
            .count(),
        1,
        "multiple writes to same parameter should produce one combined frame"
    );
    assert_eq!(
        requires
            .iter()
            .filter(|expr| {
                matches!(expr, PureExpr::BinOp(lhs, BinOp::Eq, rhs) if is_len_call(lhs) && is_len_call(rhs))
            })
            .count(),
        1,
        "multiple writes to same parameter should produce one length preservation fact"
    );

    let frame = requires
        .iter()
        .find(|expr| matches!(expr, PureExpr::Forall { .. }))
        .expect("combined frame should exist");
    let mut excluded = Vec::new();
    if let PureExpr::Forall { body, .. } = frame {
        if let PureExpr::BinOp(antecedent, BinOp::Implies, _) = body.as_ref() {
            collect_frame_excluded_int_indices(antecedent, &mut excluded);
        } else {
            panic!("frame body should be implication");
        }
    }
    excluded.sort_unstable();
    assert_eq!(
        excluded,
        vec![0, 1],
        "combined frame should exclude every written index"
    );
}

#[test]
fn indexed_write_synthesis_keeps_frames_separate_per_parameter() {
    let indexed_writes = vec![
        IndexedWrite {
            param_name: "a".to_string(),
            index: PureExpr::Int(0),
            value: PureExpr::Int(10),
        },
        IndexedWrite {
            param_name: "b".to_string(),
            index: PureExpr::Int(1),
            value: PureExpr::Int(20),
        },
    ];
    let mut requires = Vec::new();

    synthesize_indexed_write_postconditions(&indexed_writes, &mut requires, false);

    assert_eq!(count_top_level_point_writes(&requires), 2);
    assert_eq!(
        requires
            .iter()
            .filter(|expr| matches!(expr, PureExpr::Forall { .. }))
            .count(),
        2,
        "distinct parameters should each get their own frame"
    );
    assert_eq!(
        requires
            .iter()
            .filter(|expr| {
                matches!(expr, PureExpr::BinOp(lhs, BinOp::Eq, rhs) if is_len_call(lhs) && is_len_call(rhs))
            })
            .count(),
        2,
        "distinct parameters should each get their own length preservation fact"
    );
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
        invariants: &invariants,
        pre_loop_obligations: &obligations,
        loop_obligation_groups: &[],
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
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

/// Pre-loop obligation `i > 0` passes when invariant gives `i > 0`.
#[test]
fn loop_call_obligations_verify_when_implied_by_invariants() {
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
        invariants: &invariants,
        pre_loop_obligations: &obligations,
        loop_obligation_groups: &[],
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result =
        verify_loop_call_obligations(&ctx).expect("loop obligation verification should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected verified loop call obligations, got {result:?}"
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
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: Some(loop_condition),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
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
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: Some(loop_condition),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
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
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: None,
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &pre_loop_obligations,
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
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
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: Some(loop_condition),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &base_requires,
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &pre_loop_obligations,
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
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
        assumptions: Vec::new(),
        obligations: in_loop_obligations,
        condition: None,
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
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
