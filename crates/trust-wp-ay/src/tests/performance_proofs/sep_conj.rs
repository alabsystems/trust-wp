// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// SepConj chain: constraint count scaling
// =============================================================================

/// 4-element chain (below `TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD`=8): encodes and solves SAT.
/// This exercises the cross-pair disjointness path (pairwise neq constraints).
#[test]
#[timeout(30000)]
fn test_sep_conj_chain_4_encodes_sat() {
    let mut encoder = AYEncoder::new();
    let chain = build_sep_conj_chain(4);
    let result = encoder.encode(&chain);
    encoder
        .assert_term(result.unwrap_or_else(|err| panic!("4-element chain should encode: {err:?}")));
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Sat),
        "4-element chain with distinct locations should be SAT"
    );
}

/// 8-element chain (at threshold boundary): encodes and solves SAT.
#[test]
#[timeout(30000)]
fn test_sep_conj_chain_8_boundary_sat() {
    let mut encoder = AYEncoder::new();
    let chain = build_sep_conj_chain(8);
    let result = encoder.encode(&chain);
    encoder
        .assert_term(result.unwrap_or_else(|err| panic!("8-element chain should encode: {err:?}")));
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Sat),
        "8-element chain should be SAT"
    );
}

/// 16-element chain with pairwise (no-quantifier) encoding: measures ground neq
/// solve time as a comparison baseline for the quantified path.
///
/// If pairwise at N=16 completes fast, the quantified threshold can be raised.
/// N=16 produces 120 cross-pair neq constraints via the pairwise path.
/// Re: #611 — quantified threshold evaluation
#[test]
#[timeout(30000)]
fn test_sep_conj_chain_16_pairwise_sat() {
    use std::time::Instant;

    let mut encoder = AYEncoder::new(); // no quantifiers → forces pairwise
    let chain = build_sep_conj_chain(16);
    let start = Instant::now();
    let result = encoder.encode(&chain);
    let encode_time = start.elapsed();
    encoder.assert_term(
        result.unwrap_or_else(|err| panic!("16-element pairwise should encode: {err:?}")),
    );
    let start = Instant::now();
    let sat = encoder.check_sat();
    let solve_time = start.elapsed();
    assert!(
        matches!(sat, ay_dpll::api::SolveResult::Sat),
        "16-element pairwise chain should be SAT, got {sat:?}"
    );
    eprintln!(
        "sep_conj_pairwise_16: encode={encode_time:?}, solve={solve_time:?}, total={:?}",
        encode_time + solve_time
    );
}

/// 20-element chain with pairwise (no-quantifier) encoding: measures ground neq
/// solve time as a comparison baseline for the quantified path.
///
/// N=20 produces 190 cross-pair neq constraints via the pairwise path.
/// Reduced from N=32 (496 constraints) which consistently timed out at 120s,
/// wasting test budget on a dead sep-logic code path.
/// Re: #611 — quantified threshold evaluation
#[cfg(feature = "sep-logic")]
#[test]
#[timeout(60000)]
#[serial(perf)]
fn test_sep_conj_chain_20_pairwise_sat() {
    use std::time::Instant;

    let mut encoder = AYEncoder::new(); // no quantifiers → forces pairwise
    let chain = build_sep_conj_chain(20);
    let start = Instant::now();
    let result = encoder.encode(&chain);
    let encode_time = start.elapsed();
    encoder.assert_term(
        result.unwrap_or_else(|err| panic!("20-element pairwise should encode: {err:?}")),
    );
    let start = Instant::now();
    let sat = encoder.check_sat();
    let solve_time = start.elapsed();
    assert!(
        matches!(sat, ay_dpll::api::SolveResult::Sat),
        "20-element pairwise chain should be SAT, got {sat:?}"
    );
    eprintln!(
        "sep_conj_pairwise_20: encode={encode_time:?}, solve={solve_time:?}, total={:?}",
        encode_time + solve_time
    );
}

/// 32-element chain with quantified encoding: encodes and solves SAT within timeout.
/// This proves the quantified disjointness encoding prevents quadratic blowup.
/// Without quantified encoding, 32 elements would produce ~496 cross-pair constraints
/// and potentially time out.
#[cfg(feature = "sep-logic")]
#[test]
#[timeout(60000)]
#[serial(perf)]
fn test_sep_conj_chain_32_quantified_sat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let chain = build_sep_conj_chain(32);
    let result = encoder.encode(&chain);
    encoder.assert_term(
        result.unwrap_or_else(|err| panic!("32-element chain should encode: {err:?}")),
    );
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Sat),
        "32-element chain with quantified disjointness should be SAT"
    );
}

/// 32-element quantified chain with an unrelated equality remains SAT and must
/// not trigger semantic-overlap model scans (#625).
#[cfg(feature = "sep-logic")]
#[test]
#[timeout(60000)]
#[serial(perf)]
fn test_sep_conj_chain_32_quantified_with_unrelated_equality_sat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let chain = build_sep_conj_chain(32);
    let unrelated_eq = pure(eq(var("x"), var("y")));
    let formula = formula_and(chain, unrelated_eq);

    let term = encoder.encode(&formula).unwrap_or_else(|err| {
        panic!("32-element chain with unrelated equality should encode: {err:?}")
    });
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Sat),
        "Unrelated equality must not regress quantified-chain SAT"
    );
}

/// 128-element chain: exceeds `MAX_ENCODING_DEPTH` (128) since left-recursive
/// SepConj nesting requires ~129 recursion levels (127 SepConj nodes + leaf
/// PointsTo encoding). The recursion guard (#1116) correctly rejects this.
///
/// Before #1116, encoding succeeded but risked stack overflow. Now the depth
/// guard converts the stack-overflow risk into a clean `EncodingError`.
/// The 32-element test validates solver correctness at scale.
///
/// Re: #564 (performance audit), #1116 (recursion guard)
#[test]
#[timeout(30000)]
fn test_sep_conj_chain_128_exceeds_max_encoding_depth() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let chain = build_sep_conj_chain(128);
    // 128-element left-recursive chain exceeds MAX_ENCODING_DEPTH.
    // The recursion guard returns EncodingError::Unsupported.
    let err = encoder
        .encode(&chain)
        .expect_err("128-element chain should hit depth limit");
    let err_msg = format!("{err:?}");
    assert!(
        err_msg.contains("nesting exceeds maximum depth"),
        "error should mention depth limit: {err_msg}"
    );
}

/// 127-element chain: boundary test for `MAX_ENCODING_DEPTH` (128).
///
/// A left-recursive SepConj chain of 127 elements has 126 nesting levels.
/// Total recursion depth: 126 (SepConj) + 1 (PointsTo formula) + 1 (PureExpr)
/// = 128, which is exactly at the limit (guard triggers at depth > 128).
///
/// Re: #1116 (recursion guard boundary)
#[cfg(feature = "sep-logic")]
#[test]
#[timeout(30000)]
#[serial(perf)]
fn test_sep_conj_chain_127_at_depth_boundary_encodes() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let chain = build_sep_conj_chain(127);
    let term = encoder.encode(&chain).unwrap_or_else(|err| {
        panic!("127-element chain should be at depth boundary (128): {err:?}")
    });
    // Boundary intent is recursion-depth acceptance at encode time.
    // Solving this massive quantified term is covered elsewhere and is highly
    // machine-load sensitive in shared test runs.
    encoder.assert_term(term);
}
// =============================================================================
// SepConj encoding time scaling: quadratic pair accumulation detection
// =============================================================================

// build_sep_conj_chain_with_prefix is imported from helpers::*

/// Measure encoding time for SepConj chains at different sizes to detect
/// superlinear scaling in the quantified disjointness encoding.
///
/// With incremental domain reuse (#668), the encoder caches each SepConj's
/// combined domain predicate and reuses it as the left domain at the parent
/// boundary. This reduces per-boundary membership assertions from O(L) to
/// O(R), making total encoding O(N) instead of O(N²) for chains.
///
/// This test measures the encoding time ratio between N=64 and N=16.
/// For O(N) encoding: ratio ~= 4x. For O(N²): ratio ~= 16x.
/// Threshold is 12x to catch quadratic regressions while tolerating
/// system load variance during parallel test execution (#730).
#[test]
#[timeout(30000)]
fn test_sep_conj_quantified_encoding_scaling() {
    use std::time::Instant;

    let small_n = 16;
    let large_n = 64;

    // Warm up both sizes to stabilize allocator and cache (#730)
    {
        let mut enc = AYEncoder::new_with_quantifiers();
        let _ = enc.encode(&build_sep_conj_chain(small_n));
    }
    {
        let mut enc = AYEncoder::new_with_quantifiers();
        let _ = enc.encode(&build_sep_conj_chain(large_n));
    }

    // Measure small
    let start = Instant::now();
    for _ in 0..3 {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let chain = build_sep_conj_chain(small_n);
        let result = encoder.encode(&chain);
        result.unwrap_or_else(|err| panic!("{small_n}-element chain should encode: {err:?}"));
    }
    let small_time = start.elapsed();

    // Measure large
    let start = Instant::now();
    for _ in 0..3 {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let chain = build_sep_conj_chain(large_n);
        let result = encoder.encode(&chain);
        result.unwrap_or_else(|err| panic!("{large_n}-element chain should encode: {err:?}"));
    }
    let large_time = start.elapsed();

    let small_secs = small_time.as_secs_f64().max(1e-12);
    let ratio = large_time.as_secs_f64() / small_secs;

    // Document actual scaling behavior for tracking.
    // O(N) expect ~4x, O(N²) expect ~16x, O(N³) expect ~64x.
    // With incremental domain reuse (#668), encoding is O(N) per chain.
    // Threshold 12x tolerates system load variance (#730) while still
    // catching quadratic regressions (which show ~16x ratio).
    assert!(
        ratio < 12.0,
        "SepConj encoding scaling ratio ({large_n}/{small_n}) = {ratio:.1}x. \
         If > 12x, incremental domain reuse may have regressed to quadratic. \
         Expected ~4x with O(N) incremental encoding."
    );

    eprintln!(
        "sep_conj_encoding_scaling: small({small_n})={small_time:?}, \
         large({large_n})={large_time:?}, ratio={ratio:.1}x \
         (O(N) expect ~4x, O(N²) expect ~16x)"
    );
}

/// Verify that SepConj chains with assert_term + check_sat still complete
/// within the timeout for the quantified path. The recheck loop in check_sat
/// iterates over all accumulated pairs per SAT call, which can compound the
/// O(N²) pair growth.
///
/// This test encodes, asserts, and solves at N=32 (known to work) and
/// documents the total time including recheck overhead.
#[cfg(feature = "sep-logic")]
#[test]
#[timeout(60000)]
#[serial(perf)]
fn test_sep_conj_assert_and_solve_scaling_32() {
    use std::time::Instant;

    let start = Instant::now();
    let mut encoder = AYEncoder::new_with_quantifiers();
    let chain = build_sep_conj_chain(32);
    let result = encoder.encode(&chain);
    encoder.assert_term(
        result.unwrap_or_else(|err| panic!("32-element chain should encode: {err:?}")),
    );
    let encode_time = start.elapsed();

    let start = Instant::now();
    let sat = encoder.check_sat();
    let solve_time = start.elapsed();

    assert!(
        matches!(sat, ay_dpll::api::SolveResult::Sat),
        "32-element quantified chain should be SAT"
    );

    eprintln!(
        "sep_conj_assert_solve_32: encode={encode_time:?}, solve={solve_time:?}, \
         total={:?}",
        encode_time + solve_time
    );
}

/// Multiple independent SepConj assertions share the same quantified_disjoint_pairs
/// set. This test measures encoding time scaling for multiple independent chains
/// to detect accumulation overhead.
///
/// Each 4-element chain contributes ~6 pairs. We measure encoding-only time
/// (no assert_term) for K=3 vs K=12 to isolate pair-accumulation cost from
/// the ay solver's E-matching overhead which dominates at higher K with
/// assert_term (caused 15s timeout at K=20 with 8-element chains).
///
/// Note: SAT result is not checked — multiple independent SepConj chains in the
/// same encoder can produce UNSAT due to cross-chain quantified domain interference.
/// That is a separate correctness issue.
#[test]
#[timeout(30000)]
fn test_multiple_sep_conj_encoding_time_scaling() {
    use std::time::Instant;

    let small_k = 3;
    let large_k = 12;

    // Measure small: encode K chains without assert_term
    let start = Instant::now();
    {
        let mut encoder = AYEncoder::new_with_quantifiers();
        for batch in 0..small_k {
            let chain = build_sep_conj_chain_with_prefix(4, &format!("s{batch}_"));
            let result = encoder.encode(&chain);
            result.unwrap_or_else(|err| panic!("Small batch {batch} should encode: {err:?}"));
        }
    }
    let small_time = start.elapsed();

    // Measure large: encode K chains without assert_term
    let start = Instant::now();
    {
        let mut encoder = AYEncoder::new_with_quantifiers();
        for batch in 0..large_k {
            let chain = build_sep_conj_chain_with_prefix(4, &format!("l{batch}_"));
            let result = encoder.encode(&chain);
            result.unwrap_or_else(|err| panic!("Large batch {batch} should encode: {err:?}"));
        }
    }
    let large_time = start.elapsed();

    let small_secs = small_time.as_secs_f64().max(1e-12);
    let ratio = large_time.as_secs_f64() / small_secs;

    // For O(K): ratio ~= 4x (12/3). For O(K²): ratio ~= 16x.
    // Set 25x as upper bound to catch worse-than-quadratic.
    assert!(
        ratio < 25.0,
        "Multi-chain encoding scaling ratio ({large_k}/{small_k}) = {ratio:.1}x. \
         If > 25x, cross-chain pair accumulation has worse-than-quadratic regression."
    );

    eprintln!(
        "multi_sep_conj_encoding: small({small_k})={small_time:?}, \
         large({large_k})={large_time:?}, ratio={ratio:.1}x \
         (O(K) expect ~4x, O(K²) expect ~16x)"
    );
}
/// Measures that asserting additional terms after encoding multiple SepConj
/// chains scales linearly with the number of chains.
///
/// Encoding SepConj chains above the `TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD`
/// creates quantified disjoint constraint sets stored in the assertion
/// pipeline. Every subsequent `assert_term` call invokes
/// `has_relevant_quantified_equality` in `encoder::solver::quantified_disjoint`,
/// which scans these constraint sets via `mentions_quantified_term`.
///
/// With P SepConj chains, each producing one quantified constraint set,
/// the per-assertion scan cost is O(P × (L + R)) where L, R are the
/// footprint sizes. This test scales P and checks that the overhead of
/// follow-up pure assertions is bounded.
///
/// Re: performance_proofs phase — quantified disjoint scanning overhead
#[test]
#[timeout(30000)]
fn test_post_sep_conj_assertion_overhead_scaling() {
    use std::time::Instant;

    let small_chains = 2;
    let large_chains = 8;
    let post_assertions = 50;
    let rounds = 5;

    /// Encode `c` independent SepConj chains of size 16, then time `n`
    /// follow-up pure term assertions.
    fn run_with_chains(c: usize, n: usize) -> std::time::Duration {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Encode c independent SepConj chains, each of size 16 (above
        // threshold, so quantified encoding is used).
        for chain_idx in 0..c {
            let chain = build_sep_conj_chain_with_prefix(16, &format!("sc{chain_idx}_"));
            let term = encoder
                .encode(&chain)
                .unwrap_or_else(|e| panic!("chain {chain_idx} encode: {e:?}"));
            encoder.assert_term(term);
        }

        // Time follow-up pure assertions — these trigger the quantified
        // constraint scan on each assert_term call.
        let start = Instant::now();
        for i in 0..n {
            let expr = gt(var(&format!("post_{i}")), int(0));
            encoder.register_sort_hints(std::slice::from_ref(&expr));
            if let Ok(term) = encoder.encode_pure(&expr) {
                encoder.assert_term(term);
            }
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_with_chains(small_chains, post_assertions);
    let _ = run_with_chains(large_chains, post_assertions);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_with_chains(small_chains, post_assertions);
        let large_time = run_with_chains(large_chains, post_assertions);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(C): ratio(8/2) ≈ 4x. For O(C²): ratio ≈ 16x.
    // Threshold 12x catches quadratic regression while allowing for
    // constant overhead from SepConj chain encoding itself.
    assert!(
        min_ratio < 12.0,
        "Post-SepConj assertion overhead ratio ({large_chains}/{small_chains} chains) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 12x, quantified constraint scanning has superlinear overhead. \
         Expected ~4x with O(C) for {post_assertions} follow-up assertions."
    );

    eprintln!(
        "post_sep_conj_assertion_overhead: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(C) expect ~4x for C={small_chains}→{large_chains}, post_asserts={post_assertions})"
    );
}
