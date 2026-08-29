// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{MatchArm, Pattern};

use super::{expr_referenced_vars, expr_references_var, find_loop_invariants, BinOp, PureExpr};

// --- find_loop_invariants tests (#1112) ---

fn inv_gt_zero() -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )
}

fn inv_lt_ten() -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(10)),
    )
}

#[test]
fn find_loop_invariants_no_match_returns_empty() {
    let per_loop = vec![(10, 50, vec![inv_gt_zero()])];
    let all_spans = vec![(10, 50)];
    // Header at position 100 is outside the only span (10..50)
    let result = find_loop_invariants(&per_loop, &all_spans, 100);
    assert!(
        result.is_empty(),
        "header outside all spans should return empty"
    );
}

#[test]
fn find_loop_invariants_single_match() {
    let invs = vec![inv_gt_zero()];
    let per_loop = vec![(10, 50, invs.clone())];
    let all_spans = vec![(10, 50)];
    let result = find_loop_invariants(&per_loop, &all_spans, 20);
    assert_eq!(
        result, invs,
        "header inside the span should return its invariants"
    );
}

/// AC-1: Tightest invariant-bearing span wins on nested annotated loops.
///
/// Outer loop: span 10..100 with inv_gt_zero
/// Inner loop: span 30..60 with inv_lt_ten
/// Header at position 40 is inside both; the inner (tighter) span wins.
#[test]
fn find_loop_invariants_tightest_annotated_span_wins() {
    let outer_invs = vec![inv_gt_zero()];
    let inner_invs = vec![inv_lt_ten()];
    let per_loop = vec![
        (10, 100, outer_invs.clone()), // outer: size 90
        (30, 60, inner_invs.clone()),  // inner: size 30
    ];
    let all_spans = vec![(10, 100), (30, 60)];
    let result = find_loop_invariants(&per_loop, &all_spans, 40);
    assert_eq!(
        result, inner_invs,
        "tightest invariant-bearing span should win for nested annotated loops"
    );
}

/// AC-2: Tighter non-annotated loop suppresses outer invariant inheritance.
///
/// Outer loop: span 10..100 with inv_gt_zero (annotated)
/// Inner loop: span 30..60 with NO invariants (not in per_loop_invariants)
/// all_loop_spans includes both (10..100) and (30..60).
/// Header at position 40: the inner loop (30..60) is tighter than the best
/// invariant-bearing span (10..100), so the result should be empty.
#[test]
fn find_loop_invariants_non_annotated_inner_suppresses_inheritance() {
    let outer_invs = vec![inv_gt_zero()];
    // Only the outer loop has invariants
    let per_loop = vec![(10, 100, outer_invs)];
    // But both loops exist in the all_loop_spans
    let all_spans = vec![(10, 100), (30, 60)];
    let result = find_loop_invariants(&per_loop, &all_spans, 40);
    assert!(
        result.is_empty(),
        "non-annotated inner loop should suppress inheritance from outer invariant"
    );
}

/// AC-3: Deterministic behavior when multiple invariant spans have equal size.
///
/// Two spans of equal size (both size 40) both contain the header.
/// The function picks the first match it encounters in iteration order
/// (since `span_size < best_size` uses strict less-than, the first one wins).
/// Either result is acceptable as long as it's deterministic.
#[test]
fn find_loop_invariants_equal_size_spans_deterministic() {
    let invs_a = vec![inv_gt_zero()];
    let invs_b = vec![inv_lt_ten()];
    let per_loop = vec![
        (10, 50, invs_a.clone()), // size 40
        (20, 60, invs_b.clone()), // size 40
    ];
    let all_spans = vec![(10, 50), (20, 60)];
    // Header at 25 is inside both equal-size spans
    let result = find_loop_invariants(&per_loop, &all_spans, 25);
    // With strict less-than comparison, the first encountered span wins
    assert_eq!(
        result, invs_a,
        "equal-size spans should deterministically select the first match"
    );

    // Verify it's truly deterministic by running again
    let result2 = find_loop_invariants(&per_loop, &all_spans, 25);
    assert_eq!(
        result, result2,
        "repeated calls must return the same result"
    );
}

/// Boundary: header exactly at span start (inclusive).
#[test]
fn find_loop_invariants_header_at_span_start() {
    let invs = vec![inv_gt_zero()];
    let per_loop = vec![(10, 50, invs.clone())];
    let all_spans = vec![(10, 50)];
    let result = find_loop_invariants(&per_loop, &all_spans, 10);
    assert_eq!(
        result, invs,
        "start is inclusive: header == start should match"
    );
}

/// Boundary: header exactly at span end (exclusive — should NOT match).
#[test]
fn find_loop_invariants_header_at_span_end() {
    let per_loop = vec![(10, 50, vec![inv_gt_zero()])];
    let all_spans = vec![(10, 50)];
    let result = find_loop_invariants(&per_loop, &all_spans, 50);
    assert!(
        result.is_empty(),
        "end is exclusive: header == end should not match"
    );
}

/// Non-annotated inner loop exactly matches invariant span size — does NOT suppress.
/// The suppression check is `tightest_loop_size < inv_span_size` (strict less-than),
/// so equal sizes mean the invariant is preserved.
#[test]
fn find_loop_invariants_equal_tightest_loop_does_not_suppress() {
    let invs = vec![inv_gt_zero()];
    // Invariant-bearing span: 10..50 (size 40)
    let per_loop = vec![(10, 50, invs.clone())];
    // all_loop_spans has the exact same span — size 40 matches inv_span_size
    let all_spans = vec![(10, 50)];
    let result = find_loop_invariants(&per_loop, &all_spans, 20);
    assert_eq!(
        result, invs,
        "loop of equal span size should NOT suppress invariant (strict less-than check)"
    );
}

#[test]
fn expr_referenced_vars_excludes_bound_quantifier_var() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        )),
        triggers: vec![],
    };
    let vars = expr_referenced_vars(&expr);
    assert!(
        vars.contains("n"),
        "free variable n should be retained: {vars:?}"
    );
    assert!(
        !vars.contains("i"),
        "bound quantifier variable i must be excluded: {vars:?}"
    );
}

#[test]
fn expr_references_var_respects_binder_shadowing() {
    let forall_shadowed = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    assert!(
        !expr_references_var(&forall_shadowed, "x"),
        "forall binder should shadow x in body"
    );

    let match_shadowed = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("scrut".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("x".to_string()),
            body: PureExpr::Var("x".to_string(), None),
        }],
    };
    assert!(
        !expr_references_var(&match_shadowed, "x"),
        "match pattern binding should shadow x in arm body"
    );
    assert!(
        expr_references_var(&match_shadowed, "scrut"),
        "scrutinee variables remain visible"
    );

    let let_shadowed = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(0)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        !expr_references_var(&let_shadowed, "x"),
        "let binder should shadow x in body"
    );

    let closure_shadowed = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        !expr_references_var(&closure_shadowed, "x"),
        "closure params should shadow x in body"
    );
}

#[test]
fn expr_referenced_vars_excludes_match_arm_bound_var() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("input".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("x".to_string()),
            body: PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            ),
        }],
    };

    let vars = expr_referenced_vars(&expr);
    assert!(
        vars.contains("input"),
        "match scrutinee var should be retained: {vars:?}"
    );
    assert!(
        vars.contains("y"),
        "free var from arm body should be retained: {vars:?}"
    );
    assert!(
        !vars.contains("x"),
        "pattern-bound x must be excluded from collected vars: {vars:?}"
    );
}
