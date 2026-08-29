// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Ground pool axiom clone: O(A × G) deep-clone overhead bounded by caps
// =============================================================================

/// Verifies that `assert_ground_pool_instances` with many registered axioms
/// scales linearly in axiom count (for fixed ground entries per symbol).
///
/// The function at `ground_pool.rs:283-308` deep-clones every `AxiomEntry`
/// (including `PureExpr` body/requires) into a work Vec. With TRUST_WP_CAP_PER_SYMBOL=50,
/// the per-axiom matching is bounded. This test confirms the overall scaling
/// is O(A) not O(A^2).
///
/// Re: performance_proofs phase — ground pool clone overhead
#[test]
#[timeout(30000)]
#[serial(perf)]
#[allow(clippy::cast_precision_loss)]
fn test_ground_pool_axiom_clone_scaling_linear() {
    use std::time::Instant;

    use ay_dpll::api::Sort;

    use crate::encoder::ground_pool::AxiomKind;

    fn register_axioms_and_measure(axiom_count: usize, iters: usize) -> std::time::Duration {
        let start = Instant::now();
        for _ in 0..iters {
            let mut encoder = AYEncoder::new();

            let int_sort = Sort::Int;
            let func_decl = encoder.solver.declare_fun(
                "test_fn",
                std::slice::from_ref(&int_sort),
                int_sort.clone(),
            );

            // Register one ground entry so matching fires
            let arg = encoder.solver.int_const(42);
            let app = encoder.solver.apply(&func_decl, &[arg]);
            encoder.ground_pool_for_test_mut().register(
                "test_fn",
                app,
                vec![arg],
                vec![PureExpr::Int(42)],
            );

            // Register N axioms, all matching "test_fn"
            for i in 0..axiom_count {
                let body = add(var(&format!("p_{i}")), int(1));
                encoder.ground_pool_for_test_mut().register_axiom(
                    crate::encoder::ground_pool::AxiomEntry {
                        fn_symbol: "test_fn".to_string(),
                        params: vec![format!("p_{i}")],
                        body,
                        requires: vec![],
                        func_decl: func_decl.clone(),
                        return_sort: int_sort.clone(),
                        kind: AxiomKind::Defining,
                    },
                );
            }

            let _ = encoder.assert_ground_pool_instances();
        }
        start.elapsed()
    }

    let small_a = 5;
    let large_a = 20;
    let rounds = 5;
    let iters = 50;

    // Warmup
    register_axioms_and_measure(small_a, 2);
    register_axioms_and_measure(large_a, 2);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = register_axioms_and_measure(small_a, iters);
        let large_time = register_axioms_and_measure(large_a, iters);

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    let size_ratio = large_a as f64 / small_a as f64; // 4.0

    // Linear: ratio ≈ 4x. Include encoder setup overhead → allow 15x.
    assert!(
        median < 15.0,
        "ground_pool axiom clone scaling ({large_a}/{small_a}) median = \
         {median:.1}x (rounds: {ratios:.1?}). Expected linear (<15x for \
         {size_ratio}x axiom count). If >15x, the deep-clone pattern at \
         ground_pool.rs:283-308 may be superlinear."
    );

    eprintln!(
        "ground_pool axiom clone: median={median:.1}x, rounds={ratios:.1?} \
         (linear ideal: ~{size_ratio}x)"
    );
}

/// Verifies that `TRUST_WP_CAP_PER_SYMBOL` effectively bounds ground entry growth.
///
/// After registering `TRUST_WP_CAP_PER_SYMBOL + 10` entries for one symbol, the pool
/// should contain exactly `TRUST_WP_CAP_PER_SYMBOL` entries (excess silently dropped).
///
/// Re: performance_proofs phase — ground pool cap enforcement
#[test]
#[timeout(30000)]
fn test_ground_pool_cap_per_symbol_enforcement() {
    use crate::encoder::ground_pool::GroundTermPool;

    let cap = 50; // TRUST_WP_CAP_PER_SYMBOL
    let mut pool = GroundTermPool::new();
    let mut encoder = AYEncoder::new();

    #[allow(clippy::cast_possible_wrap)]
    for i in 0..(cap + 10) {
        let term = encoder.solver.int_const(i as i64);
        pool.register("f", term, vec![term], vec![PureExpr::Int(i as i64)]);
    }

    let entries = pool.entries_for("f").expect("f should have entries");
    assert_eq!(
        entries.len(),
        cap,
        "TRUST_WP_CAP_PER_SYMBOL={cap} should limit entries to {cap}, got {}",
        entries.len()
    );
}
