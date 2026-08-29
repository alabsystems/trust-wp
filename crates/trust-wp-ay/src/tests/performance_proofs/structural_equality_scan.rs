// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// substitute_constants: linear const_map scan per node
// =============================================================================

/// Verifies that the structural equality scan pattern used by
/// `substitute_constants` in ghost flattening scales linearly with
/// expression tree size for a fixed const_map.
///
/// `shared_constraints.rs:193` does `const_map.iter().find(|(k, _)| k == &expr)`
/// at every recursive node — O(C*T) per node where C = const_map size and
/// T = structural equality cost. For fixed C, total should be O(N*C*T) = O(N).
///
/// Re: performance_proofs phase — substitute_constants linear scan
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_structural_equality_scan_scaling_linear() {
    use std::time::Instant;

    /// Build a chain of BinOp(Add) with `n` distinct method_call leaves.
    #[allow(clippy::cast_possible_wrap)]
    fn build_chain(n: usize) -> PureExpr {
        let mut expr = method_call(var("obj"), "get", vec![int(0)]);
        for i in 1..n {
            expr = add(expr, method_call(var("obj"), "get", vec![int(i as i64)]));
        }
        expr
    }

    /// Count nodes in a PureExpr tree.
    fn count_nodes(expr: &PureExpr) -> usize {
        match expr {
            PureExpr::BinOp(l, _, r) => 1 + count_nodes(l) + count_nodes(r),
            PureExpr::MethodCall { receiver, args, .. } => {
                1 + count_nodes(receiver) + args.iter().map(count_nodes).sum::<usize>()
            }
            _ => 1,
        }
    }

    /// Simulate the substitute_constants pattern: scan const_map at every node.
    fn scan_const_map(expr: &PureExpr, const_map: &[(&PureExpr, &PureExpr)]) -> usize {
        let mut scans = 0;
        for (k, _) in const_map {
            scans += 1;
            if *k == expr {
                return scans;
            }
        }
        match expr {
            PureExpr::BinOp(l, _, r) => {
                scans += scan_const_map(l, const_map);
                scans += scan_const_map(r, const_map);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                scans += scan_const_map(receiver, const_map);
                for a in args {
                    scans += scan_const_map(a, const_map);
                }
            }
            _ => {}
        }
        scans
    }

    let small_n = 10;
    let large_n = 40;
    let const_map_size = 5;

    let small_tree = build_chain(small_n);
    let large_tree = build_chain(large_n);

    let const_keys: Vec<PureExpr> = (0..const_map_size)
        .map(|i| method_call(var("obj"), "get", vec![int(100 + i as i64)]))
        .collect();
    let const_vals: Vec<PureExpr> = (0..const_map_size).map(|i| int(i as i64)).collect();
    let const_map: Vec<(&PureExpr, &PureExpr)> = const_keys.iter().zip(const_vals.iter()).collect();

    let small_nodes = count_nodes(&small_tree);
    let large_nodes = count_nodes(&large_tree);

    let small_scans = scan_const_map(&small_tree, &const_map);
    let large_scans = scan_const_map(&large_tree, &const_map);

    let scan_ratio = large_scans as f64 / small_scans as f64;
    let node_ratio = large_nodes as f64 / small_nodes as f64;

    // With fixed const_map, scans should grow linearly with nodes.
    assert!(
        scan_ratio < node_ratio * 2.0,
        "substitute_constants scan ratio ({large_scans}/{small_scans} = {scan_ratio:.1}x) \
         should be proportional to node ratio ({large_nodes}/{small_nodes} = {node_ratio:.1}x). \
         If >2x node ratio, the linear scan cost is compounding superlinearly."
    );

    // Time the actual scanning.
    let rounds = 5;
    let iters = 2000;

    for _ in 0..iters {
        let _ = scan_const_map(&small_tree, &const_map);
        let _ = scan_const_map(&large_tree, &const_map);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let _ = scan_const_map(&small_tree, &const_map);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let _ = scan_const_map(&large_tree, &const_map);
        }
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    assert!(
        median < 15.0,
        "structural equality scan time scaling ({large_n}/{small_n}) median = \
         {median:.1}x (rounds: {ratios:.1?}). Expected linear (<15x for ~{node_ratio:.1}x \
         node count). If >15x, PureExpr structural equality cost is compounding."
    );

    eprintln!(
        "structural equality scan: median={median:.1}x, scans={small_scans}->{large_scans}, \
         nodes={small_nodes}->{large_nodes} (linear ideal: ~{node_ratio:.1}x)"
    );
}
