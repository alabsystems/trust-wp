// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// §11 — Substitution binder-clone scaling (Finding #1 from memory blowup scan)
// =============================================================================
//
// `substitute_vars_in_expr` clones its entire `HashMap<String, PureExpr>` binding
// at every Forall/Exists/Let/Closure/Match binder node (expr_subst.rs:245, 291,
// 318, 415). This test verifies that runtime scales linearly with nesting depth
// (not quadratically), and that the MAX_ENCODING_DEPTH=128 guard correctly
// truncates deep recursion.

/// Build a chain of nested Forall quantifiers: forall<v_0> forall<v_1> ... body
fn build_nested_forall(depth: usize, body: PureExpr) -> PureExpr {
    let mut expr = body;
    for i in (0..depth).rev() {
        expr = PureExpr::Forall {
            var: format!("v_{i}"),
            var_sort: None,
            body: Arc::new(expr),
            triggers: vec![],
        };
    }
    expr
}

#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_substitute_vars_binder_depth_scales_linearly() {
    // Build nested Forall chains of increasing depth, substitute with a
    // fixed-size binding map, and verify time scaling is linear (not quadratic).
    //
    // `substitute_vars_in_expr` now delegates to the shared overlay-based
    // capture-avoiding substitution. With fixed K, depth scaling should still
    // remain linear in D rather than drifting toward quadratic behavior.
    let binding: HashMap<String, PureExpr> = (0..20)
        .map(|i| (format!("x_{i}"), PureExpr::Int(i)))
        .collect();

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_0".to_string(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let small_depth = 20;
    let large_depth = 80;

    let small_expr = build_nested_forall(small_depth, body.clone());
    let large_expr = build_nested_forall(large_depth, body);

    let warmup_iters = 40;

    // Warmup
    for _ in 0..warmup_iters {
        let _ = substitute_vars_in_expr(&small_expr, &binding);
        let _ = substitute_vars_in_expr(&large_expr, &binding);
    }

    let rounds = 5;
    let iters = 250;
    let mut ratios = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&small_expr, &binding);
        }
        let small_time = start.elapsed();

        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&large_expr, &binding);
        }
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    // Depth ratio is 80/20 = 4x. With linear scaling expect ~4x.
    // Allow up to 10x to account for runtime variance.
    assert!(
        median < 10.0,
        "substitute_vars binder depth scaling ({large_depth}/{small_depth}) \
         median={median:.1}x. Expected linear (~4x). If >10x, binder-depth \
         handling has regressed superlinearly."
    );

    eprintln!(
        "substitute_vars binder depth: median={median:.1}x \
         ({small_depth}->{large_depth} depth, 20-entry binding map)"
    );
}

#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_substitute_vars_binding_map_size_scales_linearly() {
    // Verify that scaling with binding map size K is linear for fixed depth.
    // The shared substitution engine uses overlay shadowing, but growth in K
    // should still remain materially linear for fixed depth.
    let depth = 30;

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y_0".to_string(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let expr = build_nested_forall(depth, body);

    let small_k = 10;
    let large_k = 80;

    let small_binding: HashMap<String, PureExpr> = (0..small_k)
        .map(|i| (format!("y_{i}"), PureExpr::Int(i)))
        .collect();
    let large_binding: HashMap<String, PureExpr> = (0..large_k)
        .map(|i| (format!("y_{i}"), PureExpr::Int(i)))
        .collect();

    let warmup_iters = 40;

    // Warmup
    for _ in 0..warmup_iters {
        let _ = substitute_vars_in_expr(&expr, &small_binding);
        let _ = substitute_vars_in_expr(&expr, &large_binding);
    }

    let rounds = 5;
    let iters = 250;
    let mut ratios = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&expr, &small_binding);
        }
        let small_time = start.elapsed();

        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&expr, &large_binding);
        }
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    // Map size ratio is 80/10 = 8x. Linear scaling expects ~8x.
    // Allow up to 20x for runtime variance.
    assert!(
        median < 20.0,
        "substitute_vars binding map size scaling ({large_k}/{small_k}) \
         median={median:.1}x. Expected linear (~8x). If >20x, binding-map \
         handling is compounding with map size."
    );

    eprintln!(
        "substitute_vars binding map size: median={median:.1}x \
         ({small_k}->{large_k} entries, depth={depth})"
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_vars_depth_guard_truncates_at_128() {
    // Verify MAX_ENCODING_DEPTH=128 guard: a 200-deep nesting should NOT
    // recurse beyond 128 levels. The inner body should be returned unmodified
    // below depth 128.
    //
    // This also documents that closure_inline::apply_substitution LACKS this
    // guard (Finding #6) — it has no depth limit at all.
    let leaf_var = "target_var".to_string();
    let binding: HashMap<String, PureExpr> = [(leaf_var.clone(), PureExpr::Int(999))]
        .into_iter()
        .collect();

    // Build a 200-deep Forall chain with the target variable at the bottom.
    // Binder names are disjoint from the target variable, so substitution
    // should reach the leaf IF recursion goes deep enough.
    let body = PureExpr::Var(leaf_var, None);
    let expr = build_nested_forall(200, body);

    let result = substitute_vars_in_expr(&expr, &binding);

    // Count how deep the result nests Forall before hitting a non-Forall.
    fn forall_depth(e: &PureExpr) -> usize {
        match e {
            PureExpr::Forall { body, .. } => 1 + forall_depth(body),
            _ => 0,
        }
    }

    let result_depth = forall_depth(&result);

    // The depth guard at 128 means the inner body beyond depth 128 is returned
    // as-is (the original Var, not substituted to Int(999)).
    // The result should still have all 200 Forall levels.
    assert_eq!(
        result_depth, 200,
        "Forall nesting depth should be preserved (200 levels)"
    );

    // Extract the leaf expression at depth 200
    fn extract_leaf(e: &PureExpr) -> &PureExpr {
        match e {
            PureExpr::Forall { body, .. } => extract_leaf(body),
            other => other,
        }
    }

    let leaf = extract_leaf(&result);

    // Beyond depth 128, substitute_vars_inner returns expr.clone() without
    // applying the binding. So the leaf should still be Var("target_var"),
    // NOT Int(999).
    match leaf {
        PureExpr::Var(name, _) => {
            assert_eq!(
                name, "target_var",
                "Leaf variable should be unsubstituted beyond depth 128"
            );
        }
        PureExpr::Int(999) => {
            panic!(
                "Leaf was substituted to Int(999) — depth guard did not truncate. \
                 MAX_ENCODING_DEPTH may have been raised above 200."
            );
        }
        other => {
            panic!("Unexpected leaf expression: {other:?}");
        }
    }

    eprintln!(
        "substitute_vars depth guard: 200-deep nesting truncated at 128, \
         leaf unsubstituted (depth guard working correctly)"
    );
}
