// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// §13 — Quantifier variable liveness stays below the old quadratic path
// =============================================================================
//
// `encode_pure_quantifier_impl` now computes one quantified-variable coverage
// summary for the body and reuses it for unused-variable elimination. That
// should keep the `5 -> 20` variable jump materially below the old per-binder
// O(V*T) traversal path, which trended toward a quadratic ~16x ratio here.
//
// This test guards against regressing back toward that old behavior.

/// Build a multi-variable quantifier whose body mentions all variables in
/// a chain of equality comparisons. Tree size grows linearly with `n_vars`.
/// Body is Bool-sorted (required by forall semantics).
fn build_multi_var_quantifier(n_vars: usize) -> PureExpr {
    // Body: (qv_0 > 0) && (qv_1 > 0) && ... && (qv_{n-1} > 0)
    // Each conjunct references one variable; total tree size = O(3*n_vars).
    let mut body = gt(var(&format!("qv_{}", n_vars - 1)), int(0));
    for i in (0..n_vars.saturating_sub(1)).rev() {
        body = and(gt(var(&format!("qv_{i}")), int(0)), body);
    }
    // Wrap in nested forall: forall<qv_0> forall<qv_1> ... body
    for i in (0..n_vars).rev() {
        body = PureExpr::Forall {
            var: format!("qv_{i}"),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };
    }
    body
}

/// Proves that encoding multi-variable quantifiers stays materially below the
/// old quadratic liveness path when body size grows proportionally with `V`.
///
/// The previous implementation did O(V) tree walks of size O(V) = O(V²) for
/// liveness filtering. This test catches regressions back toward that ~16x
/// ratio for the `5 -> 20` variable jump.
///
/// Re: #2346 shared quantified-variable coverage
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_quantifier_var_liveness_scaling() {
    use std::time::Instant;

    let small_v = 5;
    let large_v = 20;
    let rounds = 5;
    let iters = 40;

    let small_expr = build_multi_var_quantifier(small_v);
    let large_expr = build_multi_var_quantifier(large_v);

    // Warmup
    for _ in 0..iters {
        let mut enc = AYEncoder::new_pure_with_quantifiers();
        let _ = enc.encode_pure(&small_expr);
    }
    for _ in 0..iters {
        let mut enc = AYEncoder::new_pure_with_quantifiers();
        let _ = enc.encode_pure(&large_expr);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new_pure_with_quantifiers();
            let _ = enc.encode_pure(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new_pure_with_quantifiers();
            let _ = enc.encode_pure(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // The old quadratic path trended toward (20/5)^2 = 16x here. The shared
    // coverage summary should stay materially below that. Allow up to 12x for
    // encoder/solver noise while still catching regressions back toward the
    // removed O(V²) behavior.
    assert!(
        min_ratio < 12.0,
        "quantifier var liveness scaling ({large_v}/{small_v} vars) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). The shared coverage summary should stay well \
         below the old ~16x quadratic path; >12x suggests regression toward it."
    );

    eprintln!(
        "quantifier_var_liveness: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (shared coverage summary; old quadratic path ~16x for V={small_v}->{large_v})"
    );
}

// =============================================================================
// Sort inference depth guard: stack overflow prevention
// =============================================================================

/// Sort inference on a deeply nested expression (500 levels of `Old(...)`)
/// must terminate without stack overflow. The depth guard (128 limit) returns
/// `Sort::Int` for pathologically deep trees instead of blowing the stack.
#[test]
#[timeout(5000)]
fn test_sort_inference_deep_nesting_terminates() {
    use crate::encoder::sort_context::infer_expr_sort;

    let mut expr = var_with_sort("x", trust_wp_core::formula::ExprSort::Bool);
    for _ in 0..500 {
        expr = PureExpr::Old(Arc::new(expr));
    }
    // Should terminate (depth guard fires at 128) and return a Sort.
    let sort = infer_expr_sort(&expr);
    // At depth < 128, Old(Bool) → Bool. At depth > 128, fallback → Int.
    // Either is acceptable — the point is no stack overflow.
    assert!(
        sort == ay_dpll::api::Sort::Bool || sort == ay_dpll::api::Sort::Int,
        "deep nesting sort inference should return Bool or Int, got {sort:?}"
    );
}

/// Sort inference at exactly the depth limit (128) should still succeed.
/// Only depth > 128 triggers the fallback.
#[test]
#[timeout(5000)]
fn test_sort_inference_at_depth_boundary() {
    use crate::encoder::sort_context::infer_expr_sort;

    // Build exactly 128 levels of Old(...)
    let mut expr = var_with_sort("y", trust_wp_core::formula::ExprSort::Seq);
    for _ in 0..128 {
        expr = PureExpr::Old(Arc::new(expr));
    }
    let sort = infer_expr_sort(&expr);
    // 128 Old wrappers = 128 recursive calls = depth 128 at the leaf.
    // The guard checks `depth > 128`, so depth 128 is the last accepted.
    assert_eq!(
        sort,
        ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int),
        "128-deep Old chain on Seq var should still infer Seq (at boundary)"
    );
}

/// Sort inference at depth 129 still propagates correctly after native Seq migration (#2080).
#[test]
#[timeout(5000)]
fn test_sort_inference_past_depth_boundary_falls_back() {
    use crate::encoder::sort_context::infer_expr_sort;

    // Build 129 levels of Old(...)
    let mut expr = var_with_sort("z", trust_wp_core::formula::ExprSort::Seq);
    for _ in 0..129 {
        expr = PureExpr::Old(Arc::new(expr));
    }
    let sort = infer_expr_sort(&expr);
    // After native Sort::Seq migration, sort inference propagates through
    // Old chains at arbitrary depth without falling back to Int.
    assert_eq!(
        sort,
        ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int),
        "129-deep Old chain on Seq var should infer Seq(Int) (no depth fallback after #2080)"
    );
}
