// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Formula Debug-string size: quadratic blowup detection
// =============================================================================

/// Measures the `Debug` representation length for left-recursive SepConj chains
/// at different sizes. Note: `FormulaCacheKey` now uses structural `u64`
/// hashing (not Debug strings), so this test documents the Formula `Debug`
/// output scaling independently of cache key cost.
///
/// For a left-recursive SepConj chain of N elements:
/// - The innermost `PointsTo` Debug string has length ~O(1)
/// - Level k's Debug string includes level (k-1)'s full text plus its own PointsTo
/// - The outermost Debug string is O(N), but cumulative across all levels is O(N^2)
///
/// This test verifies per-key Debug length grows linearly (the outermost key
/// is O(N) in chain length) and establishes a regression threshold.
///
/// Re: performance_proofs phase audit finding #1 (FormulaCacheKey O(N^2))
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_formula_debug_string_size_scaling() {
    let small_n = 16;
    let large_n = 64;

    let chain_small = build_sep_conj_chain(small_n);
    let chain_large = build_sep_conj_chain(large_n);

    let debug_small = format!("{chain_small:?}");
    let debug_large = format!("{chain_large:?}");

    let len_small = debug_small.len();
    let len_large = debug_large.len();

    // For a left-recursive SepConj chain, the outermost Debug string includes
    // all inner nodes, so length grows as O(N²) total characters.
    // The *outermost* key alone grows as O(N) because it contains N PointsTo
    // descriptions. But each intermediate level's key also grows, so the
    // cumulative cost across all keys is O(N²).
    //
    // For the outermost key: ratio(64/16) should be ~4x if per-key is O(N).
    // We document this and set a threshold that would catch O(N²) per-key growth.
    let ratio = len_large as f64 / len_small.max(1) as f64;

    // Per-key growth should be roughly linear (~4x for 4x size increase).
    // If it's quadratic per-key (~16x), the cache key construction has
    // super-linear per-node cost.
    assert!(
        ratio < 8.0,
        "Formula Debug string length ratio ({large_n}/{small_n}) = {ratio:.1}x \
         (len_small={len_small}, len_large={len_large}). \
         Per-key Debug length should grow O(N), not O(N²). \
         If > 8x, the Debug format has super-linear per-node growth."
    );

    // Also verify the absolute sizes are reasonable (not degenerate)
    assert!(
        len_small > 100,
        "16-element chain Debug should be substantial: got {len_small}"
    );
    assert!(
        len_large > len_small,
        "64-element chain should have longer Debug than 16-element"
    );

    eprintln!(
        "formula_debug_size: small({small_n})={len_small} bytes, \
         large({large_n})={len_large} bytes, ratio={ratio:.1}x \
         (O(N) expect ~4x per outermost key)"
    );
}
/// Measures the *cumulative* Debug string allocation cost when building cache
/// keys for every node in a SepConj chain, mimicking what `footprint_cached`
/// does during encoding. This verifies the O(N) cumulative cost after the
/// switch from Debug-string keys to structural hashing (#1294).
///
/// For a chain of N elements, the encoder calls `FormulaCacheKey::for_formula`
/// at each SepConj node. With structural hashing, each key is a fixed-size
/// `u64` — no string allocation. Cumulative Debug output is O(N).
///
/// Previously (Debug-string keys): ratio was ~16x (quadratic).
/// After fix: ratio should be ~4x (linear).
///
/// Re: performance_proofs phase audit finding #1 (cumulative O(N²) allocation)
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_formula_cache_key_cumulative_allocation() {
    use std::time::Instant;

    let small_n = 20;
    let large_n = 80;

    /// Build a SepConj chain and collect cache-key Debug strings at every
    /// level, exercising the real `FormulaCacheKey::for_formula` path used by
    /// the encoder.
    fn cumulative_cache_key_bytes(n: usize) -> usize {
        let make_pt = |i: usize| {
            points_to(
                &format!("loc_{i}"),
                int(i64::try_from(i).expect("fits i64")),
            )
        };
        let mut chain = make_pt(0);
        let mut total_bytes = format!("{:?}", FormulaCacheKey::for_formula(&chain)).len();
        for i in 1..n {
            chain = sep_conj(chain, make_pt(i));
            total_bytes += format!("{:?}", FormulaCacheKey::for_formula(&chain)).len();
        }
        total_bytes
    }

    let bytes_small = cumulative_cache_key_bytes(small_n);
    let bytes_large = cumulative_cache_key_bytes(large_n);

    let byte_ratio = bytes_large as f64 / bytes_small.max(1) as f64;

    // With structural u64 hashing, each key's Debug string is constant size.
    // Cumulative bytes scale linearly: ratio(80/20) ≈ 4.0x.
    // Threshold 6x catches any regression back toward quadratic.
    assert!(
        byte_ratio < 6.0,
        "Cumulative cache key ratio ({large_n}/{small_n}) = {byte_ratio:.1}x \
         (bytes: small={bytes_small}, large={bytes_large}). \
         Expected ~4x for O(N) with u64 hashing. If > 6x, possible regression."
    );

    // Measure wall-clock time for the cumulative key construction
    let start = Instant::now();
    for _ in 0..5 {
        let _ = cumulative_cache_key_bytes(large_n);
    }
    let elapsed = start.elapsed();

    eprintln!(
        "formula_cache_key_cumulative: small({small_n})={bytes_small} bytes, \
         large({large_n})={bytes_large} bytes, ratio={byte_ratio:.1}x \
         (O(N) with u64 hash), 5x large-n time={elapsed:?}",
    );
}

// =============================================================================
// Constructor datatype lookup: linear scan detection
// =============================================================================

/// Measures that encoding logic function calls that are NOT constructor names
/// scales linearly with the number of declared datatypes.
///
/// The `constructor_datatype` function in `match_enc.rs:210-217` performs a
/// linear scan over all declared datatypes for every logic function call.
/// With D datatypes having C constructors each, each lookup is O(D×C).
///
/// This test declares varying numbers of datatypes via Option/Result encoding
/// and measures the encoding time for non-constructor logic function calls.
/// If the lookup is optimized with a reverse index, the ratio should be ~1x.
/// With the current linear scan, it should scale with D.
///
/// Re: performance_proofs phase audit finding #2 (constructor_datatype O(D×C))
#[test]
#[timeout(30000)]
fn test_constructor_lookup_scales_with_datatypes() {
    use std::time::Instant;

    let iters = 500;

    // Baseline: encoder with no declared datatypes
    let start = Instant::now();
    for _ in 0..iters {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("user_fn", vec![var("x"), var("y")]);
        let _ = encoder.encode_pure(&expr);
    }
    let baseline_time = start.elapsed();

    // With Option and Result datatypes declared (common in real programs):
    // encoder.encode on a SepConj that uses Option will declare the datatype.
    let start = Instant::now();
    for _ in 0..iters {
        let mut encoder = AYEncoder::new();
        // Encode Some(x) to force Option datatype declaration
        let some_call = logic_fn_call("Some", vec![var("x")]);
        let _ = encoder.encode_pure(&some_call);
        // Encode Ok(x) to force Result datatype declaration
        let ok_call = logic_fn_call("Ok", vec![var("x")]);
        let _ = encoder.encode_pure(&ok_call);
        // Now encode a non-constructor function call — this must scan all datatypes
        let expr = logic_fn_call("user_fn", vec![var("x"), var("y")]);
        let _ = encoder.encode_pure(&expr);
    }
    let with_dt_time = start.elapsed();

    let baseline_secs = baseline_time.as_secs_f64().max(1e-12);
    let ratio = with_dt_time.as_secs_f64() / baseline_secs;

    // With declared datatypes, encoding a non-constructor call should not be
    // more than 10x slower than without datatypes. The linear scan adds O(D×C)
    // per call, but D is small (2-3 in typical programs). If the ratio is > 10x,
    // either D has grown or the scan itself has regressed.
    assert!(
        ratio < 10.0,
        "Constructor lookup overhead ratio = {ratio:.1}x. \
         With O(D×C) scan and D=2 (Option+Result), should be < 10x. \
         If > 10x, constructor_datatype scan has regressed."
    );

    eprintln!(
        "constructor_lookup_overhead: baseline={baseline_time:?}, \
         with_dt={with_dt_time:?}, ratio={ratio:.1}x over {iters} iterations"
    );
}

// =============================================================================
// assert_term throughput: per-assertion allocation overhead
// =============================================================================

/// Measures that asserting N terms to the solver scales linearly with N.
///
/// The `assert_term` path drains pending assertions through
/// `AssertionPipeline::drain_pending_assertions()`, materializing an owned
/// `Vec<Term>` on each call. This test ensures that per-assertion allocation
/// overhead does not cause superlinear scaling.
///
/// Re: performance_proofs phase audit finding #3 (assert_term drain/collect)
#[test]
#[timeout(30000)]
fn test_assert_term_throughput_linear() {
    use std::time::Instant;

    let small_n = 50;
    let large_n = 200;
    let rounds = 5;

    let run_assertions = |n: usize| {
        let mut encoder = AYEncoder::new();
        // Register sort hints for variables used in assertions
        let hint_exprs: Vec<PureExpr> =
            (0..n).map(|i| gt(var(&format!("x_{i}")), int(0))).collect();
        encoder.register_sort_hints(&hint_exprs);

        for i in 0..n {
            let expr = gt(var(&format!("x_{i}")), int(i64::try_from(i).expect("fits")));
            if let Ok(term) = encoder.encode_pure(&expr) {
                encoder.assert_term(term);
            }
        }
    };

    // Warmup
    run_assertions(small_n);
    run_assertions(large_n);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        run_assertions(small_n);
        let small_time = start.elapsed();

        let start = Instant::now();
        run_assertions(large_n);
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(N): ratio(200/50) ≈ 4x. For O(N²): ratio ≈ 16x.
    // Threshold 10x catches quadratic while tolerating system variance.
    assert!(
        min_ratio < 10.0,
        "assert_term throughput min scaling ratio ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, per-assertion overhead has quadratic scaling. \
         Expected ~4x with O(N) assertion throughput."
    );

    eprintln!(
        "assert_term_throughput: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x, O(N²) expect ~16x)"
    );
}
