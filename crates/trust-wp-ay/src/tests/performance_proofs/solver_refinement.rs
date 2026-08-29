// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Solver refinement loop: recheck loop materialization bound
// =============================================================================

/// Verify that the recheck loop materializes exactly the colliding pairs
/// and that the neq_pairs count scales linearly with K constraint sets.
///
/// With K constraint sets each containing 1 forced collision, the recheck
/// should materialize exactly K neq pairs (one per collision). This proves
/// the recheck iteration is O(K), not O(K²), in terms of pairs asserted.
///
/// Re: #901 — solver refinement loop linear materialization proof
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss, clippy::cast_possible_wrap)]
fn test_recheck_materialization_linear_in_constraint_sets() {
    use ay_dpll::api::{SolveResult, Sort};

    for k in [5, 10, 20, 40] {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let anchor = encoder
            .get_or_declare_var("__mat_anchor", Sort::Int)
            .expect("anchor");

        for set_idx in 0..k {
            let other = encoder
                .get_or_declare_var(&format!("__mat_v{set_idx}"), Sort::Int)
                .expect("other var");

            encoder
                .assertion_pipeline_mut_for_test()
                .push_active_disjoint_constraint_for_test(vec![anchor], vec![other]);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(anchor);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(other);

            // Force collision: anchor == other
            let eq = encoder.solver.eq(anchor, other);
            encoder.solver.assert_term(eq);
        }

        encoder
            .assertion_pipeline_mut_for_test()
            .prime_recheck_for_test();

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "K={k}: expected UNSAT, got {result:?}"
        );

        let pair_count = encoder
            .assertion_pipeline_for_test()
            .asserted_neq_pairs_len();

        // Each of K constraint sets has exactly 1 collision → at most K pairs.
        // The recheck may discover all in one pass or need cascading, but
        // total materialized pairs should be O(K), not O(K²).
        assert!(
            pair_count <= k * 2,
            "K={k}: materialized {pair_count} pairs, expected <= {k_bound}. \
             Superlinear pair accumulation detected.",
            k_bound = k * 2,
        );
        assert!(
            pair_count >= k,
            "K={k}: materialized only {pair_count} pairs, expected >= {k}. \
             Not enough collisions detected."
        );

        eprintln!(
            "recheck_materialization K={k}: {pair_count} pairs \
             (expected ~{k}, bound {k_bound}, result={result:?})",
            k_bound = k * 2,
        );
    }
}

// =============================================================================
// Soundness: ground disjoint neq preserved through conjunction assertion path
// =============================================================================

/// Verify that ground `loc_0 != loc_1` from an inner SepConj boundary (below
/// the quantified threshold) is preserved when the SepConj chain term is
/// asserted through the conjunction path (bundled with quantified foralls).
///
/// Regression test: the original `test_quantified_recheck_check_sat_scaling`
/// forced `loc_0 == loc_1` and expected UNSAT, but got SAT. The root cause
/// was that `loc_0` and `loc_1` are on the same side of all quantified
/// boundaries, so their disjointness is enforced only by a ground `neq`
/// constraint embedded in the chain term. If the conjunction bundling path
/// (`and_many` in `assert_term`) loses this constraint, the forced equality
/// becomes satisfiable.
///
/// This test directly checks whether the ground constraint survives.
///
/// Re: #901 — ground disjoint soundness through conjunction path
#[test]
#[timeout(30000)]
fn test_ground_disjoint_neq_survives_conjunction_path() {
    use ay_dpll::api::SolveResult;

    // Use a 16-element chain: inner SepConj(pt(loc_0), pt(loc_1)) creates
    // ground neq(loc_0, loc_1). The chain term + quantified foralls go
    // through the conjunction assertion path.
    let mut encoder = AYEncoder::new_with_quantifiers();
    let chain = build_sep_conj_chain_with_prefix(16, "gnd_");
    let chain_term = encoder.encode(&chain).unwrap();
    encoder.assert_term(chain_term);

    // Assert loc_0 == loc_1 — should contradict the ground neq.
    let overlap = eq(var("gnd_loc_0"), var("gnd_loc_1"));
    encoder.register_sort_hints(std::slice::from_ref(&overlap));
    let overlap_term = encoder.encode_pure(&overlap).unwrap();
    encoder.assert_term(overlap_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ground neq(loc_0, loc_1) from inner SepConj should make loc_0 == loc_1 \
         unsatisfiable, but got {result:?}. The conjunction assertion path may be \
         losing ground disjoint constraints."
    );
}

// =============================================================================
// Solver refinement loop: per-set O(L+R) collision detection
// =============================================================================

/// Verify that collision detection within a single constraint set scales as
/// O(L+R), not O(L*R).
///
/// `recheck_one_constraint_set_cached` in
/// `encoder::solver::quantified_disjoint` indexes left terms by model value
/// for O(1) lookup, making collision detection O(L+R) per set. This test
/// compares small (L=R=10) vs large (L=R=40) sets.
///
/// Re: #901, #668 — value-indexed collision detection scaling
#[test]
#[timeout(60000)]
#[allow(clippy::cast_precision_loss, clippy::cast_possible_wrap)]
#[serial(perf)]
fn test_recheck_collision_detection_linear_in_terms_per_set() {
    use std::time::Instant;

    use ay_dpll::api::{SolveResult, Sort};

    let n_small = 10; // L=R=10
    let n_large = 40; // L=R=40
    let rounds = 3;
    let iters = 10;

    fn run_recheck_sized(n: usize, iters: usize) -> std::time::Duration {
        let start = Instant::now();
        for iter_idx in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();

            let mut lefts = Vec::with_capacity(n);
            let mut rights = Vec::with_capacity(n);

            for i in 0..n {
                let left = encoder
                    .get_or_declare_var(&format!("__rn_{iter_idx}_l{i}"), Sort::Int)
                    .expect("left var");
                let right = encoder
                    .get_or_declare_var(&format!("__rn_{iter_idx}_r{i}"), Sort::Int)
                    .expect("right var");
                lefts.push(left);
                rights.push(right);

                // Force collision: left_i == right_i
                let eq = encoder.solver.eq(left, right);
                encoder.solver.assert_term(eq);
            }

            encoder
                .assertion_pipeline_mut_for_test()
                .push_active_disjoint_constraint_for_test(lefts.clone(), rights.clone());
            for &t in lefts.iter().chain(rights.iter()) {
                encoder
                    .assertion_pipeline_mut_for_test()
                    .insert_disjoint_term_for_test(t);
            }

            encoder
                .assertion_pipeline_mut_for_test()
                .prime_recheck_for_test();

            let result = encoder.check_sat();
            assert!(
                matches!(result, SolveResult::Unsat(_)),
                "N={n} iter={iter_idx}: expected UNSAT, got {result:?}"
            );
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_recheck_sized(n_small, iters);
    let _ = run_recheck_sized(n_large, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let t_small = run_recheck_sized(n_small, iters);
        let t_large = run_recheck_sized(n_large, iters);
        let small_secs = t_small.as_secs_f64().max(1e-12);
        ratios.push(t_large.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // O(L+R): ratio(80/20) ~= 4x. O(L*R): ratio ~= 16x.
    assert!(
        min_ratio < 14.0,
        "per-set collision detection should be O(L+R). \
         Ratio(N={n_large}/N={n_small}) = {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 14x, value-indexed collision detection is superlinear."
    );

    eprintln!(
        "recheck_collision_detection_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(L+R) expect ~4x for N={n_small}→{n_large})"
    );
}
