// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// 1. Recheck loop scaling

/// Build an encoder with `n_constraints` constraint sets using Bool variables.
///
/// Each constraint set has a single left Bool variable and a single right Bool
/// variable, forming an all-pairs-distinct pigeonhole setup. Bool variables
/// allow fast SAT solving and recheck convergence.
///
/// Returns the encoder with revisions set so recheck fires on check_sat.
fn build_bool_recheck_encoder(n_constraints: usize, prefix: &str) -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let vars: Vec<_> = (0..n_constraints)
        .map(|i| {
            encoder
                .get_or_declare_var(&format!("{prefix}_b{i}"), Sort::Bool)
                .expect("bool var")
        })
        .collect();
    // Create all-pairs disjoint constraints: each pair (i, j) gets its own
    // constraint set with single-element sides.
    for i in 0..n_constraints {
        for j in (i + 1)..n_constraints {
            encoder
                .assertion_pipeline_mut_for_test()
                .push_active_disjoint_constraint_for_test(vec![vars[i]], vec![vars[j]]);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(vars[i]);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(vars[j]);
        }
    }
    encoder
        .assertion_pipeline_mut_for_test()
        .prime_recheck_for_test();
    encoder
}

/// Build an encoder with `n_groups` groups, each containing `terms_per_group`
/// Bool variables on the left and 1 Bool variable on the right, forming
/// constraint sets that exercise collision detection at scale.
fn build_multi_term_recheck_encoder(
    n_groups: usize,
    terms_per_group: usize,
    prefix: &str,
) -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_millis(25)));
    for g in 0..n_groups {
        let left_terms: Vec<_> = (0..terms_per_group)
            .map(|i| {
                encoder
                    .get_or_declare_var(&format!("{prefix}_l{g}_{i}"), Sort::Bool)
                    .expect("bool var")
            })
            .collect();
        let right = encoder
            .get_or_declare_var(&format!("{prefix}_r{g}"), Sort::Bool)
            .expect("bool var");
        for &lt in &left_terms {
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(lt);
        }
        encoder
            .assertion_pipeline_mut_for_test()
            .insert_disjoint_term_for_test(right);
        encoder
            .assertion_pipeline_mut_for_test()
            .push_active_disjoint_constraint_for_test(left_terms, vec![right]);
    }
    encoder
        .assertion_pipeline_mut_for_test()
        .prime_recheck_for_test();
    encoder
}

/// Measures time to build and solve a Bool pigeonhole encoder with `n` variables.
fn measure_bool_recheck_time(n: usize, prefix: &str, iters: usize) -> std::time::Duration {
    let start = Instant::now();
    for i in 0..iters {
        let mut encoder = build_bool_recheck_encoder(n, &format!("{prefix}{i}"));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "bool all-pairs recheck measurement should be Unsat for n={n}, iter={i}; got {result:?}"
        );
    }
    start.elapsed()
}

/// Measures time to build and solve multi-term constraint sets.
fn measure_multi_term_recheck_time(
    n_groups: usize,
    terms_per_group: usize,
    prefix: &str,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for i in 0..iters {
        let mut encoder =
            build_multi_term_recheck_encoder(n_groups, terms_per_group, &format!("{prefix}{i}"));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "multi-term recheck measurement should remain satisfiable for groups={n_groups}, \
             terms_per_group={terms_per_group}, iter={i}; got {result:?}"
        );
    }
    start.elapsed()
}

/// Proves that the recheck loop scales at most quadratically in the number of
/// Bool variables (constraint pairs grow as n*(n-1)/2).
///
/// The all-pairs-distinct pigeonhole setup creates O(n²) constraint sets for
/// n variables. Doubling n from 3 to 6 creates 3 → 15 constraint pairs (~5x).
/// Wall time should scale proportionally to constraint-pair count.
///
/// Re: #901 — solver refinement loop scaling (constraint count dimension)
#[test]
#[timeout(30000)]
#[serial(scaling)]
fn test_recheck_loop_scales_with_constraint_count() {
    let small_n = 3; // C(3,2) = 3 constraint pairs
    let large_n = 6; // C(6,2) = 15 constraint pairs
    let rounds = 5;
    let iters = 40;

    // Warm up.
    let _ = measure_bool_recheck_time(small_n, "__rsc_warm_c", iters);
    let _ = measure_bool_recheck_time(large_n, "__rsc_warm_cl", iters);

    let mut ratios = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let small_time = measure_bool_recheck_time(small_n, &format!("__rsc{round}s"), iters);
        let large_time = measure_bool_recheck_time(large_n, &format!("__rsc{round}l"), iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // Constraint pair count ratio = 15/3 = 5x. With solver overhead, allow up to 20x.
    // Cubic (n³) would give ~8x for the n ratio and ~40x for the pair-count ratio.
    assert!(
        min_ratio < 20.0,
        "recheck loop scaling (n={large_n}/n={small_n}, pairs=15/3) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 20x, recheck likely has superquadratic scaling."
    );

    eprintln!(
        "recheck_constraint_count: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(n²) pairs: 15/3 = ~5x for n={small_n}->{large_n})"
    );
}

/// Proves that the per-constraint-set collision detection scales linearly in
/// the number of left terms (the L dimension of O(L+R) hash-indexed lookup).
///
/// Uses single-right-term constraint sets with varying left counts.
///
/// Re: #901 — per-constraint-set collision detection scaling
#[test]
#[timeout(30000)]
#[serial(scaling)]
fn test_recheck_collision_detection_scales_linearly_in_left_terms() {
    let n_groups = 4;
    let small_t = 4;
    let large_t = 16;
    let rounds = 3;
    let iters = 8;

    // Warm up.
    let _ = measure_multi_term_recheck_time(n_groups, small_t, "__rmt_warm_s", iters);
    let _ = measure_multi_term_recheck_time(n_groups, large_t, "__rmt_warm_l", iters);

    let mut ratios = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let small_time =
            measure_multi_term_recheck_time(n_groups, small_t, &format!("__rmt{round}s"), iters);
        let large_time =
            measure_multi_term_recheck_time(n_groups, large_t, &format!("__rmt{round}l"), iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(L+R): ratio(16/4) ~= 4x. Quadratic O(L*R) would give ~16x.
    // Threshold 14x catches quadratic regression.
    assert!(
        min_ratio < 14.0,
        "collision detection scaling (L={large_t}/L={small_t}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 14x, collision detection likely regressed to quadratic."
    );

    eprintln!(
        "recheck_left_terms: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(L+R) expect ~4x for L={small_t}->{large_t})"
    );
}

/// Boundary-proof: once recheck has converged and no new assertions are added,
/// repeated `check_sat` calls must remain at fixpoint.
///
/// This guards the revision-sync boundary (`quantified_pairs_revision` ==
/// `assertion_revision`) and ensures we don't keep materializing duplicate neq
/// constraints or return spurious Sat on a stable state.
///
/// Re: #901 — solver refinement loop fixpoint boundary
#[test]
#[timeout(30000)]
fn test_recheck_many_constraints_reaches_fixpoint_without_new_pairs() {
    let mut encoder = build_bool_recheck_encoder(6, "__rfix");

    let first_result = encoder.check_sat();
    assert!(
        matches!(first_result, SolveResult::Unsat(_)),
        "6-bool all-pairs disjoint setup should be Unsat on first check, got {first_result:?}"
    );

    let first_pairs = encoder
        .assertion_pipeline_for_test()
        .asserted_neq_pairs_len();
    assert!(
        first_pairs > 0,
        "first recheck pass should materialize at least one neq pair"
    );

    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .quantified_pairs_revision(),
        encoder.assertion_pipeline_for_test().assertion_revision(),
        "first check should sync quantified_pairs_revision to assertion_revision"
    );

    // No new assertions between checks: second call should stay at fixpoint.
    let second_result = encoder.check_sat();
    assert!(
        matches!(second_result, SolveResult::Unsat(_)),
        "second check at fixpoint should remain Unsat, got {second_result:?}"
    );

    let second_pairs = encoder
        .assertion_pipeline_for_test()
        .asserted_neq_pairs_len();
    assert_eq!(
        second_pairs, first_pairs,
        "no new assertions were added, so neq pair count should remain stable"
    );
    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .quantified_pairs_revision(),
        encoder.assertion_pipeline_for_test().assertion_revision(),
        "second check should preserve revision sync at fixpoint"
    );
}

/// Re: #901 — moderate-size Bool pigeonhole constraints should converge to Unsat.
#[test]
#[timeout(30000)]
fn test_recheck_convergence_moderate_sizes_return_unsat() {
    for n in [3, 4, 5, 6] {
        let mut encoder = build_bool_recheck_encoder(n, &format!("__conv{n}"));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "recheck for {n} Bool vars should prove Unsat \
             (pigeonhole: {n} values into 2 bins with all-pairs-distinct), got {result:?}"
        );
    }
}

/// Re: #901 — high-cardinality all-pairs recheck must never produce spurious Sat.
#[test]
#[timeout(30000)]
fn test_recheck_high_cardinality_all_pairs_never_spurious_sat() {
    let mut saw_unsat = false;
    for n in [8, 10, 12] {
        let mut encoder = build_bool_recheck_encoder(n, &format!("__many{n}"));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "high-cardinality all-pairs recheck for {n} Bool vars \
             should prove Unsat; got {result:?}"
        );
        if matches!(result, SolveResult::Unsat(_)) {
            saw_unsat = true;
        }
    }
    assert!(
        saw_unsat,
        "high-cardinality all-pairs recheck returned Unknown for all tested sizes \
         [8, 10, 12]; expected at least one concrete Unsat proof"
    );
}
