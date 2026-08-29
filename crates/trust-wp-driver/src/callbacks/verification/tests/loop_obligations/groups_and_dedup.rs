// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_ay::VerificationResult;
use trust_wp_core::{
    formula::{BinOp, PureExpr},
    TrackLevel,
};

use crate::callbacks::{
    parsing::LoopObligationGroup,
    verification::loop_contract::{verify_loop_call_obligations, LoopCallObligationContext},
};

#[test]
fn multi_loop_per_group_condition_both_verify() {
    let base_requires = vec![];
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("j".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let groups = [
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )],
            condition: Some(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Var("n".to_string(), None)),
            )),
        },
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![PureExpr::BinOp(
                Arc::new(PureExpr::Var("j".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )],
            condition: Some(PureExpr::BinOp(
                Arc::new(PureExpr::Var("j".to_string(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Var("m".to_string(), None)),
            )),
        },
    ];
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
    let result = verify_loop_call_obligations(&ctx)
        .expect("multi-loop obligation verification should encode");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected multi-loop obligations to verify with per-group conditions, got {result:?}"
    );
}

/// Multi-loop: second loop's obligation fails despite first loop's condition
/// being sufficient for its own obligations (#752).
/// Loop 1: condition `i > 0`, obligation `i > 0` (verifies).
/// Loop 2: no condition, obligation `j > 0` under invariant `j >= 0` (fails: j=0).
#[test]
fn multi_loop_second_group_fails_independently() {
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("j".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let groups = [
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )],
            condition: Some(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
        },
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![PureExpr::BinOp(
                Arc::new(PureExpr::Var("j".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )],
            condition: None,
        },
    ];
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
    let result = verify_loop_call_obligations(&ctx)
        .expect("multi-loop obligation verification should encode");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "expected Failed from second loop group (j=0 violates j > 0), got {result:?}"
    );
}

/// Empty obligation groups are skipped, producing Verified (#752).
#[test]
fn multi_loop_empty_groups_verify() {
    let groups = [
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![],
            condition: Some(PureExpr::Var("cond".to_string(), None)),
        },
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![],
            condition: None,
        },
    ];
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        invariants: &[],
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
    let result = verify_loop_call_obligations(&ctx).expect("empty groups should encode");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected Verified for empty obligation groups, got {result:?}"
    );
}

/// Single-loop backward compatibility: one group with condition produces
/// identical results to the old flat in_loop_obligations + loop_condition (#752).
#[test]
fn single_loop_backward_compat_with_condition() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // Obligation: i >= 0 (trivially implied by invariant, verified with or without condition)
    let groups = [LoopObligationGroup {
        assumptions: Vec::new(),
        obligations: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )],
        condition: Some(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        )),
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
        verify_loop_call_obligations(&ctx).expect("single-loop backward compat should encode");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected Verified for single-loop backward compat, got {result:?}"
    );
}

// =========================================================================
// Dedup logic: nested loop coverage (#2095)
// =========================================================================

/// Pre-loop obligation that exactly matches a loop group obligation should be
/// filtered out by the dedup logic, preventing double-checking.
#[test]
fn pre_loop_dedup_filters_exact_match_from_loop_group() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // Same obligation appears in both pre-loop and loop group.
    let shared_obl = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let groups = [LoopObligationGroup {
        assumptions: Vec::new(),
        obligations: vec![shared_obl.clone()],
        condition: Some(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        )),
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[shared_obl],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result = verify_loop_call_obligations(&ctx).expect("dedup exact-match should encode");
    // The shared obligation verifies under the loop group's invariant+condition.
    // Pre-loop copy is deduped, so no pre-loop check fires.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "dedup exact-match: obligation should verify via loop group, got {result:?}"
    );
}

/// Pre-loop obligation that matches the RHS of a guarded `Implies` in a loop
/// group should be filtered by the dedup logic.
#[test]
fn pre_loop_dedup_filters_implies_rhs_match() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let raw_obl = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    // Loop group has a guarded version: guard => raw_obl
    let guarded_obl = PureExpr::BinOp(
        Arc::new(PureExpr::Var("flag".to_string(), None)),
        BinOp::Implies,
        Arc::new(raw_obl.clone()),
    );
    let groups = [LoopObligationGroup {
        assumptions: Vec::new(),
        obligations: vec![guarded_obl],
        condition: None,
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[raw_obl],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result = verify_loop_call_obligations(&ctx).expect("dedup implies-RHS should encode");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "dedup implies-RHS: obligation should verify via loop group, got {result:?}"
    );
}

/// Nested loops: two groups with structurally identical obligations.
/// Simulates inner+outer loop both calling `v[i]` with precondition `i >= 0`.
/// The pre-loop copy is deduped, but each group independently verifies its own.
#[test]
fn nested_loop_identical_obligations_dedup_preserves_coverage() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let shared_obl = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    // Outer loop group and inner loop group both have the same obligation.
    let groups = [
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![shared_obl.clone()],
            condition: Some(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Var("n".to_string(), None)),
            )),
        },
        LoopObligationGroup {
            assumptions: Vec::new(),
            obligations: vec![shared_obl.clone()],
            condition: Some(PureExpr::BinOp(
                Arc::new(PureExpr::Var("j".to_string(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Var("m".to_string(), None)),
            )),
        },
    ];
    // Pre-loop also has the same obligation (from function-level walk).
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[shared_obl],
        loop_obligation_groups: &groups,
        logic_fns_opt: None,
        mode_overrides_opt: None,
        type_invariants_opt: None,
        type_constants_opt: None,
        adt_decls_opt: None,
        track_level: TrackLevel::Auto,
        timeout: None,
    };
    let result = verify_loop_call_obligations(&ctx)
        .expect("nested-loop identical obligations should encode");
    // Pre-loop deduped; both groups verify independently under invariant.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "nested-loop identical obligations should all verify, got {result:?}"
    );
}

/// Genuinely pre-loop obligation (not in any group) must NOT be filtered.
/// Pre-loop: `x > 0` (fails under empty invariants).
/// Loop group: `i >= 0` (different obligation, verifies under invariant).
#[test]
fn pre_loop_dedup_preserves_genuinely_pre_loop_obligations() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let pre_only_obl = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let in_loop_obl = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let groups = [LoopObligationGroup {
        assumptions: Vec::new(),
        obligations: vec![in_loop_obl],
        condition: None,
    }];
    let ctx = LoopCallObligationContext {
        base_requires: &[],
        pre_loop_assumptions: &[],
        invariants: &invariants,
        pre_loop_obligations: &[pre_only_obl],
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
        verify_loop_call_obligations(&ctx).expect("genuinely pre-loop obligation should encode");
    // x > 0 has no supporting assumption, so it fails.
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "genuinely pre-loop obligation should NOT be deduped, got {result:?}"
    );
}
