// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// 1. collect_constructor_datatype_candidates scaling
// ---------------------------------------------------------------------------

fn measure_result_match_datatype_time(exprs: &[PureExpr], iters: usize) -> std::time::Duration {
    let start = Instant::now();
    for _ in 0..iters {
        let _ = result_match_datatype_from_postcondition(exprs);
    }
    start.elapsed()
}

/// Correctness gate for result_match_datatype scaling tests (#2130).
fn assert_result_match_datatype_correctness(exprs: &[PureExpr]) {
    use crate::encoder::match_enc::SwitchTarget;
    let result = result_match_datatype_from_postcondition(exprs);
    assert!(
        result.is_some(),
        "should detect OptionInt from nested Eq(result, Some(i)) chain"
    );
    assert_eq!(
        result.unwrap(),
        SwitchTarget::OptionInt,
        "should infer OptionInt"
    );
}

/// Proves that `result_match_datatype_from_postcondition` with deeply nested
/// Eq chains scales at most quadratically in tree depth.
///
/// The O(T²) worst case arises because `collect_constructor_datatype_candidates`
/// recursively walks the tree (O(T)) and at each Eq node calls
/// `expr_contains_result_var` which is another O(T) walk. Doubling T from 50
/// to 200 should give at most 16x (quadratic) scaling.
///
/// This test validates the quadratic bound holds and detects any cubic or
/// worse regression (e.g., from accidental re-traversal or clone overhead).
///
/// Re: #901 — verify/result_inference.rs quadratic risk
#[test]
#[timeout(30000)]
fn test_result_inference_nested_eq_scaling() {
    let small_n = 50;
    let large_n = 200;
    let rounds = 5;
    let iters = 500;

    let small_exprs = vec![build_nested_eq_chain(small_n)];
    let large_exprs = vec![build_nested_eq_chain(large_n)];

    // Correctness gate: verify return value before measuring timing (#2130)
    assert_result_match_datatype_correctness(&small_exprs);

    // Warm up.
    let _ = measure_result_match_datatype_time(&small_exprs, iters);
    let _ = measure_result_match_datatype_time(&large_exprs, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_result_match_datatype_time(&small_exprs, iters);
        let large_time = measure_result_match_datatype_time(&large_exprs, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum ratio: least affected by system load spikes from
    // concurrent workers (#2009 audit finding).
    let min_ratio = ratios[0];

    // O(T²): doubling T from 50 to 200 is a 4x increase.
    // Quadratic: 4² = 16x. Allow up to 50x for multi-worker overhead.
    // Cubic: 4³ = 64x — still above threshold.
    // Previous 25x threshold failed consistently in full-suite runs under
    // multi-worker CPU contention (min ratios 47x observed). Passes in
    // isolation at ~16x. Bumped to 50x per #2023 audit. (#2023)
    assert!(
        min_ratio < 50.0,
        "result_inference nested eq scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(T²) for 4x input). \
         If > 50x, possible cubic or worse regression."
    );

    eprintln!(
        "result_inference_nested_eq: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(T²) expect ≤16x for T={small_n}->{large_n}, 4x increase)"
    );
}

/// Validates that right-recursive eq chains have the same scaling profile
/// as left-recursive chains (ruling out asymmetric traversal bugs).
///
/// Re: #901 — verify/result_inference.rs quadratic risk (right-recursive)
#[test]
#[timeout(30000)]
fn test_result_inference_right_recursive_eq_scaling() {
    let small_n = 50;
    let large_n = 200;
    let rounds = 5;
    let iters = 500;

    let small_exprs = vec![build_nested_eq_chain_right(small_n)];
    let large_exprs = vec![build_nested_eq_chain_right(large_n)];

    // Correctness gate: verify return value before measuring timing (#2130)
    assert_result_match_datatype_correctness(&small_exprs);

    // Warm up.
    let _ = measure_result_match_datatype_time(&small_exprs, iters);
    let _ = measure_result_match_datatype_time(&large_exprs, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_result_match_datatype_time(&small_exprs, iters);
        let large_time = measure_result_match_datatype_time(&large_exprs, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    assert!(
        min_ratio < 25.0,
        "result_inference right-recursive eq scaling ({large_n}/{small_n}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). Expected ≤16x (O(T²)). \
         If > 25x, asymmetric traversal or cubic regression."
    );

    eprintln!(
        "result_inference_right_eq: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(T²) expect ≤16x for T={small_n}->{large_n})"
    );
}

/// Validates that flat conjunction postconditions (many independent equalities
/// connected by And) scale linearly, not quadratically — since each equality
/// references `result` directly at the top level, the `expr_contains_result_var`
/// call should return true immediately without a deep traversal.
///
/// Re: #901 — verify/result_inference.rs: flat conjunction case
#[test]
#[timeout(30000)]
fn test_result_inference_flat_conjunction_scales_linearly() {
    let small_n = 50;
    let large_n = 200;
    let rounds = 5;
    let iters = 500;

    let small_exprs = vec![build_flat_eq_conjunction(small_n)];
    let large_exprs = vec![build_flat_eq_conjunction(large_n)];

    // Correctness gate: verify return value before measuring timing (#2130)
    assert_result_match_datatype_correctness(&small_exprs);

    // Warm up.
    let _ = measure_result_match_datatype_time(&small_exprs, iters);
    let _ = measure_result_match_datatype_time(&large_exprs, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_result_match_datatype_time(&small_exprs, iters);
        let large_time = measure_result_match_datatype_time(&large_exprs, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(T) expected: 4x input → ~4x time.
    // Even if `expr_contains_result_var` traverses, And nodes make it O(T)
    // not O(T²) because each Eq has `result` at leaf level.
    // Allow up to 14x to catch any superlinear regression.
    assert!(
        min_ratio < 14.0,
        "result_inference flat conjunction scaling ({large_n}/{small_n}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). Expected ~4x (O(T)). \
         If > 14x, flat conjunction has unexpected superlinear behavior."
    );

    eprintln!(
        "result_inference_flat_conj: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(T) expect ~4x for N={small_n}->{large_n})"
    );
}
