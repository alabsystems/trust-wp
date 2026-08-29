// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// try_match_expr: bound_vars linear scan vs expression tree size
// =============================================================================

/// Verifies that `try_match_expr` scales linearly with expression tree depth
/// for a fixed `bound_vars` size, despite `bound_vars: &[String]` using O(V)
/// linear scan at each `Var` node.
///
/// The matching function at `matching.rs:348` calls `bound_vars.contains(name)`
/// which is O(V) per node. For N nodes and V bound vars, total cost is O(N*V).
/// With fixed V, scaling in N should be linear.
///
/// Re: performance_proofs phase — try_match_expr bound_vars lookup
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_try_match_expr_scales_linearly_with_tree_depth() {
    use std::time::Instant;

    use crate::verify::try_match_expr;

    /// Build a tree of nested BinOp(Add) with `depth` leaves, each a Var.
    fn build_var_tree(depth: usize) -> PureExpr {
        if depth <= 1 {
            return var("leaf_0");
        }
        let mut expr = var("leaf_0");
        for i in 1..depth {
            expr = add(expr, var(&format!("leaf_{i}")));
        }
        expr
    }

    let bound_vars: Vec<String> = (0..10).map(|i| format!("bv_{i}")).collect();

    let small_n = 20;
    let large_n = 80;
    let rounds = 5;
    let iters = 500;

    let small_body = build_var_tree(small_n);
    let large_body = build_var_tree(large_n);
    let ground_tree_small = build_var_tree(small_n);
    let ground_tree_large = build_var_tree(large_n);

    let binding = std::collections::HashMap::new();

    // Warmup
    for _ in 0..iters {
        let mut nb = Vec::new();
        let _ = try_match_expr(
            &small_body,
            &ground_tree_small,
            &bound_vars,
            &binding,
            &mut nb,
        );
        let mut nb = Vec::new();
        let _ = try_match_expr(
            &large_body,
            &ground_tree_large,
            &bound_vars,
            &binding,
            &mut nb,
        );
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let mut nb = Vec::new();
            let _ = try_match_expr(
                &small_body,
                &ground_tree_small,
                &bound_vars,
                &binding,
                &mut nb,
            );
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let mut nb = Vec::new();
            let _ = try_match_expr(
                &large_body,
                &ground_tree_large,
                &bound_vars,
                &binding,
                &mut nb,
            );
        }
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    let size_ratio = large_n as f64 / small_n as f64; // 4.0

    // Linear: ratio ≈ 4x. Quadratic (if bound_vars grew with N) would be 16x.
    // With fixed bound_vars=10, should be linear in tree size.
    assert!(
        median < 15.0,
        "try_match_expr scaling ({large_n}/{small_n}) median = {median:.1}x \
         (rounds: {ratios:.1?}). Expected linear (<15x for {size_ratio}x size \
         ratio) with fixed bound_vars=10. If >15x, the &[String].contains() \
         linear scan at matching.rs:348 may compound with tree traversal."
    );

    eprintln!(
        "try_match_expr tree depth: median={median:.1}x, rounds={ratios:.1?} \
         (linear ideal: ~{size_ratio}x)"
    );
}

/// Verifies that `try_match_expr` degrades gracefully (at most linearly) when
/// bound_vars count increases, for a fixed expression tree size.
///
/// This isolates the O(V) per-node `bound_vars.contains()` cost: matching a
/// fixed-size tree should scale at most O(N*V), i.e., linearly in V for
/// fixed N.
///
/// Re: performance_proofs phase — try_match_expr bound_vars size scaling
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_try_match_expr_bound_vars_count_scaling() {
    use std::time::Instant;

    use crate::verify::try_match_expr;

    // Fixed tree: 40 Var leaves
    let tree_size = 40;
    let mut body = var("leaf_0");
    for i in 1..tree_size {
        body = add(body, var(&format!("leaf_{i}")));
    }
    let ground = body.clone();

    let small_v = 10;
    let large_v = 40;
    let rounds = 5;
    let iters = 500;

    let small_bv: Vec<String> = (0..small_v).map(|i| format!("bv_{i}")).collect();
    let large_bv: Vec<String> = (0..large_v).map(|i| format!("bv_{i}")).collect();
    let binding = std::collections::HashMap::new();

    // Warmup
    for _ in 0..iters {
        let mut nb = Vec::new();
        let _ = try_match_expr(&body, &ground, &small_bv, &binding, &mut nb);
        let mut nb = Vec::new();
        let _ = try_match_expr(&body, &ground, &large_bv, &binding, &mut nb);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let mut nb = Vec::new();
            let _ = try_match_expr(&body, &ground, &small_bv, &binding, &mut nb);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let mut nb = Vec::new();
            let _ = try_match_expr(&body, &ground, &large_bv, &binding, &mut nb);
        }
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    let size_ratio = large_v as f64 / small_v as f64; // 4.0

    // O(N*V) with fixed N: ratio should be ~V_ratio = 4x.
    // The &[String] linear scan means each node pays O(V).
    // If someone upgraded to HashSet, this would be ~1x (O(1) per lookup).
    // Threshold 10x catches worse-than-linear regression.
    assert!(
        median < 10.0,
        "try_match_expr bound_vars scaling ({large_v}/{small_v}) median = \
         {median:.1}x (rounds: {ratios:.1?}). Expected ~{size_ratio}x with \
         O(N*V) for fixed N=40. If >10x, the bound_vars.contains() linear \
         scan has compounded beyond O(V) per node."
    );

    eprintln!(
        "try_match_expr bound_vars count: median={median:.1}x, \
         rounds={ratios:.1?} (O(V) expect ~{size_ratio}x for {small_v}→{large_v})"
    );
}
