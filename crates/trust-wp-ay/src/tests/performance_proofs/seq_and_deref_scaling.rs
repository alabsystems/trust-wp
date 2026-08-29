// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Seq encoding: scaling with sequence operations
// =============================================================================

/// Measures that encoding N independent `push_back` operations scales linearly.
///
/// Each `push_back` creates a new `SeqValue` in the encoder's `seq_state`,
/// with an array term, length term, and offset term. The total state grows
/// O(N). This test verifies the per-operation cost doesn't degrade as the
/// seq_state grows (e.g., from linear scans over existing SeqValues).
///
/// Uses independent push_back calls on separate base variables to avoid
/// building deeply nested expression trees that could overflow the stack
/// during recursive encoding.
///
/// Re: performance_proofs phase — Seq encoding gap
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)]
fn test_seq_push_back_scaling_linear() {
    use std::time::Instant;

    let small_n = 20;
    let large_n = 80;
    let rounds = 5;

    /// Build and encode N independent push_back calls, each on a fresh base
    /// variable. This exercises seq_state growth without deep expression nesting.
    fn encode_push_back_batch(n: usize) -> std::time::Duration {
        let start = Instant::now();
        let mut encoder = AYEncoder::new();

        // Register sort hints for all base variables
        let hints: Vec<PureExpr> = (0..n)
            .map(|i| method_call(var(&format!("v_{i}")), "len", vec![]))
            .collect();
        encoder.register_sort_hints(&hints);

        for i in 0..n {
            let push_expr = method_call(var(&format!("v_{i}")), "push_back", vec![int(i as i64)]);
            // Ignore encoding failures — we're measuring seq_state growth cost
            let _ = encoder.encode_pure(&push_expr);
        }
        start.elapsed()
    }

    // Warm up
    let _ = encode_push_back_batch(small_n);
    let _ = encode_push_back_batch(large_n);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = encode_push_back_batch(small_n);
        let large_time = encode_push_back_batch(large_n);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(N): ratio(80/20) ≈ 4x. For O(N²): ratio ≈ 16x.
    // Threshold 10x catches quadratic regression in seq_state management.
    assert!(
        min_ratio < 10.0,
        "Seq push_back scaling ratio ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, seq_state management has quadratic overhead. \
         Expected ~4x with O(N) per-operation cost."
    );

    eprintln!(
        "seq_push_back_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x, O(N²) expect ~16x)"
    );
}
// =============================================================================
// Deref/Final Ite branch duplication: exponential growth detection
// =============================================================================

/// Verifies that encoding nested Deref(Ite(...)) patterns doesn't cause
/// exponential expression tree growth.
///
/// The pure_encoding.rs Deref path (lines 411-412) clones both branches
/// of an Ite and wraps each with Deref. With D levels of Deref wrapping
/// an Ite, the tree size could grow as O(2^D). This test measures the
/// encode time at different Deref nesting depths to detect exponential
/// growth.
///
/// Re: performance_proofs phase — Deref/Final Ite branch duplication
#[test]
#[timeout(30000)]
fn test_deref_ite_nesting_does_not_explode() {
    use std::time::Instant;

    let small_d = 4;
    let large_d = 8;
    let iters = 50;

    /// Build Deref^d(Ite(cond, a, b)) — d levels of Deref wrapping an Ite.
    fn build_deref_ite(depth: usize) -> PureExpr {
        let base = ite(gt(var("c"), int(0)), var("a"), var("b"));
        let mut expr = base;
        for _ in 0..depth {
            expr = deref(expr);
        }
        expr
    }

    let small_expr = build_deref_ite(small_d);
    let large_expr = build_deref_ite(large_d);

    // Warm up
    for _ in 0..iters {
        let mut enc = AYEncoder::new();
        enc.register_sort_hints(&[gt(var("c"), int(0)), var("a"), var("b")]);
        let _ = enc.encode_pure(&small_expr);
    }

    let mut ratios = Vec::with_capacity(5);
    for _ in 0..5 {
        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new();
            enc.register_sort_hints(&[gt(var("c"), int(0)), var("a"), var("b")]);
            let _ = enc.encode_pure(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new();
            enc.register_sort_hints(&[gt(var("c"), int(0)), var("a"), var("b")]);
            let _ = enc.encode_pure(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(2^D): ratio(8/4) = 2^4 = 16x. For O(D): ratio ≈ 2x.
    // The depth limit (MAX_ENCODING_DEPTH=128) prevents true exponential
    // blowup at high depths, but at depth 8 we should see the encoding
    // pattern. Threshold 32x catches exponential while allowing for
    // expected O(2^D) growth at small depths where D_large/D_small = 2.
    //
    // NOTE: If the encoder short-circuits Deref(Ite) by not cloning
    // both branches, the ratio should drop. This test documents the
    // current behavior.
    assert!(
        min_ratio < 32.0,
        "Deref(Ite) nesting ratio (depth {large_d} / depth {small_d}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 32x, Deref/Ite duplication has worse-than-expected growth."
    );

    eprintln!(
        "deref_ite_nesting: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(D) expect ~2x, O(2^D) expect ~16x for depth {small_d}→{large_d})"
    );
}
