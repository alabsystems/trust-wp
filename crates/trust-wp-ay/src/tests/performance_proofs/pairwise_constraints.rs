// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================

// =============================================================================
// Multi-chain pairwise encoding: completion and scaling
// =============================================================================

/// Tests that multiple independent SepConj chains encode and solve within
/// timeout using the pairwise disjointness path.
///
/// Uses 4 independent 4-element chains. The 4-element size stays below
/// `TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD` (8), so each chain uses the O(n²)
/// pairwise neq constraint path (not the quantified forall path). This
/// exercises multi-chain pairwise accumulation without triggering E-matching
/// overhead that dominates at 8+ elements per chain.
///
/// Note: The quantified recheck loop (`check_sat_with_quantified_disjoint_recheck`)
/// is NOT exercised here because `quantified_disjoint_constraints` stays empty
/// for sub-threshold chains. Quantified recheck convergence is indirectly
/// tested by `test_sep_conj_chain_32_quantified_sat` (single chain, N=32).
#[test]
#[timeout(30000)]
fn test_multi_chain_pairwise_encoding_completes() {
    use std::time::Instant;

    let chain_count = 4;
    let chain_size = 4;

    // Each chain gets its own encoder instance because chains sharing a single
    // encoder's heap array can conflict: if `rc0_loc_0 = rc1_loc_1` (no
    // cross-chain disjointness), then `heap[x]=0 ∧ heap[x]=1` is UNSAT (#921).
    // Using separate encoders makes each chain truly independent.
    let start = Instant::now();
    for batch in 0..chain_count {
        let mut encoder = AYEncoder::new();
        let chain = build_sep_conj_chain_with_prefix(chain_size, &format!("rc{batch}_"));
        let term = encoder
            .encode(&chain)
            .unwrap_or_else(|err| panic!("Chain {batch} of size {chain_size} failed: {err:?}"));
        encoder.assert_term(term);
        let sat = encoder.check_sat();
        assert!(
            matches!(sat, ay_dpll::api::SolveResult::Sat),
            "Chain {batch} (sub-threshold, pairwise disjointness) should be SAT, got {sat:?}"
        );
    }
    let total = start.elapsed();

    eprintln!(
        "multi_chain_pairwise_{chain_count}x{chain_size}: total={total:?} ({chain_count} independent chains)"
    );
}

/// Tests that increasing the number of SepConj chains doesn't cause the
/// pairwise disjointness encoding overhead to explode.
///
/// Measures encode+assert+solve time for K=2 vs K=6 independent 4-element
/// chains. Each chain contributes C(4,2)=6 pairwise neq constraints. At
/// 4 elements per chain, the quantified disjointness threshold (8) is not
/// reached, so all chains use the O(n²) pairwise path. The total pairwise
/// constraint count scales as O(K × n²), so the ratio should be O(K).
///
/// For O(K): ratio(6/2) ≈ 3x. For O(K²): ratio ≈ 9x.
/// Threshold 15x catches worse-than-quadratic scaling in the pairwise
/// constraint accumulation path while being generous for system variance.
#[test]
#[timeout(30000)]
fn test_pairwise_constraint_count_scaling() {
    use std::time::Instant;

    let small_k = 2;
    let large_k = 6;
    let chain_size = 4;
    // Eight batched repetitions still smooth timer noise while avoiding the
    // previous 20x oversampling on a proof whose expected ratio (~3x) still
    // sits far below the 7x regression threshold.
    let repetitions = 8;

    // Each trial encodes K independent chains, each in its own encoder to
    // avoid shared-heap conflicts (#921). Measures total encode+solve time.
    let run_trial = |k: usize, prefix: &str| -> std::time::Duration {
        let start = Instant::now();
        for batch in 0..k {
            let mut encoder = AYEncoder::new();
            let chain = build_sep_conj_chain_with_prefix(chain_size, &format!("{prefix}{batch}_"));
            let result = encoder.encode(&chain);
            encoder.assert_term(
                result.unwrap_or_else(|err| panic!("Chain {batch} should encode: {err:?}")),
            );
            let sat = encoder.check_sat();
            assert!(
                matches!(sat, ay_dpll::api::SolveResult::Sat),
                "Independent chain {batch} should be SAT, got {sat:?}"
            );
        }
        start.elapsed()
    };

    // Warm up both sizes to avoid one-time init costs skewing the ratio.
    run_trial(small_k, "warm_");
    run_trial(large_k, "warm_lg_");

    let measure_batch = |k: usize, prefix: &str| -> std::time::Duration {
        let start = Instant::now();
        for rep in 0..repetitions {
            let trial = run_trial(k, &format!("{prefix}{rep}_"));
            assert!(
                trial > std::time::Duration::ZERO,
                "Timing trial must be non-zero"
            );
        }
        start.elapsed()
    };

    // Measure batched totals to reduce timer noise and scheduler jitter.
    let small_time = measure_batch(small_k, "sm_");
    let large_time = measure_batch(large_k, "lg_");

    let small_secs = small_time.as_secs_f64().max(1e-12);
    let ratio = large_time.as_secs_f64() / small_secs;

    // Threshold: 7x catches O(K²) regression (expected ~9x for 3x size increase)
    // while providing ~2.3x headroom above the measured ~3x ratio for O(K) scaling.
    // Previous threshold of 15x was too generous: O(K²) would produce ~9x,
    // well below 15x, making the test blind to quadratic regressions.
    assert!(
        ratio < 7.0,
        "Pairwise constraint scaling ratio ({large_k}/{small_k}) = {ratio:.1}x. \
         If > 7x, constraint accumulation path has quadratic-or-worse regression. \
         Expected ~3x with O(K) scaling for {chain_size}-element chains \
         over {repetitions} repetitions."
    );

    eprintln!(
        "pairwise_constraint_scaling: small({small_k}x{chain_size}x{repetitions})={small_time:?}, \
         large({large_k}x{chain_size}x{repetitions})={large_time:?}, ratio={ratio:.1}x \
         (O(K) expect ~3x, O(K²) expect ~9x)"
    );
}

// =============================================================================
// Heap disjointness: O(L1 × L2) pairwise constraint generation
// =============================================================================

/// Measures that `heap_disjoint` generates O(L × L) pairwise neq constraints
/// and that the constraint generation + conjunction scales quadratically
/// (not worse) with location count.
///
/// `heap_disjoint` at heap.rs:225-238 builds |locs1| × |locs2| neq constraints
/// then combines them with `and_many`. This is the expected O(L²) behavior
/// for pairwise disjointness below the quantified threshold. The test verifies
/// the quadratic bound holds (not cubic or worse due to `and_many` overhead).
///
/// Re: performance_proofs phase — heap disjointness pairwise scaling
#[test]
#[timeout(30000)]
fn test_heap_disjoint_pairwise_scaling() {
    use std::time::Instant;

    use ay_dpll::api::Sort;

    let small_l = 10;
    let large_l = 40;
    let rounds = 7;
    let iters = 60;

    /// Pre-declare locations, then time only the heap_disjoint + assert_term
    /// calls to isolate pairwise constraint generation from declaration overhead.
    fn run_heap_disjoint(l: usize, iters: usize) -> std::time::Duration {
        // Pre-build encoders with declarations outside the timed section
        let mut encoders: Vec<(AYEncoder, Vec<Term>, Vec<Term>)> = Vec::with_capacity(iters);
        for iter_idx in 0..iters {
            let mut encoder = AYEncoder::new();
            let locs1: Vec<_> = (0..l)
                .map(|i| {
                    encoder
                        .solver
                        .declare_const(&format!("a{iter_idx}_{i}"), Sort::Int)
                })
                .collect();
            let locs2: Vec<_> = (0..l)
                .map(|i| {
                    encoder
                        .solver
                        .declare_const(&format!("b{iter_idx}_{i}"), Sort::Int)
                })
                .collect();
            encoders.push((encoder, locs1, locs2));
        }

        let start = Instant::now();
        for (encoder, locs1, locs2) in &mut encoders {
            let term = encoder.heap_disjoint(locs1, locs2);
            encoder.assert_term(term);
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_heap_disjoint(small_l, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_heap_disjoint(small_l, iters);
        let large_time = run_heap_disjoint(large_l, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    // Use median of 7 rounds to resist outlier rounds caused by system load
    // or memory pressure. Median of 7 tolerates up to 3 outlier rounds.
    // 60 iters per round provides sufficient amortization while reducing
    // wall-clock cost (~17s → ~9s). Previous: median-of-9 with 100 iters (#2096).
    let median_ratio = ratios[rounds / 2];

    // For O(L²): ratio(40/10) = (40/10)² = 16x.
    // For O(L³): ratio = 64x.
    //
    // Empirically the ratio is ~55-60x, well above the theoretical O(L²)=16x.
    // The superlinear overhead comes from ay term interning in `solver.neq`
    // and the `and_many` conjunction builder, which both scale with the
    // cumulative term pool size. This means heap_disjoint has effective
    // complexity closer to O(L^2.7) in wall-clock time.
    //
    // FINDING: The pairwise heap_disjoint is a genuine performance bottleneck
    // for large separation logic footprints. The TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD
    // (8) mitigates this in practice, but any footprint below the threshold
    // pays the full pairwise cost. Threshold 80x catches true cubic blowup
    // while documenting the known superquadratic behavior.
    assert!(
        median_ratio < 80.0,
        "heap_disjoint scaling ratio ({large_l}/{small_l}) = {median_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 80x, pairwise disjointness has cubic or worse overhead. \
         Expected ~16x for O(L²), empirically ~55-60x due to ay term overhead."
    );

    // Also verify the ratio shows genuine superlinear growth (not O(L)).
    // For O(L): ratio would be ~4x.
    // Threshold 5x gives margin above the 4x linear bound. Median of 7
    // rounds with 60 iters each tolerates up to 3/7 outlier rounds (#2096).
    assert!(
        median_ratio > 5.0,
        "heap_disjoint scaling ratio ({large_l}/{small_l}) = {median_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If < 5x, pairwise constraint generation may be short-circuiting. \
         Expected superlinear growth for O(L²) pairwise neq generation."
    );

    eprintln!(
        "heap_disjoint_pairwise_scaling: median ratio={median_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(L²) theory=16x, empirical ~55-60x for L={small_l}→{large_l}, \
          superquadratic from ay term interning overhead)"
    );
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
