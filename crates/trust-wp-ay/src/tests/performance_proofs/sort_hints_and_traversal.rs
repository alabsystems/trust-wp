// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Sort hint registration idempotency
// =============================================================================

/// Calling `register_sort_hints` twice on the same expressions should produce
/// the same result as calling it once (idempotent). Verify via encoding: if the
/// hint is correctly set, `encode_pure` on a Bool expression produces a Bool-sorted
/// ay term without error; missing hint would cause a sort mismatch.
#[test]
#[timeout(30000)]
fn test_sort_hint_registration_idempotent() {
    let bool_expr = not(var("b"));
    let seq_expr = method_call(view(var("v")), "len", vec![]);
    let int_expr = gt(var("x"), int(0));
    let exprs = vec![bool_expr.clone(), seq_expr.clone(), int_expr.clone()];

    let mut encoder1 = AYEncoder::new();
    encoder1.register_sort_hints(&exprs);

    let mut encoder2 = AYEncoder::new();
    encoder2.register_sort_hints(&exprs);
    encoder2.register_sort_hints(&exprs); // double registration

    // Both should produce the same sort hints
    assert_eq!(
        encoder1.is_bool_var("b"),
        encoder2.is_bool_var("b"),
        "Bool hint should be the same after double registration"
    );
    assert!(encoder1.is_bool_var("b"), "b should be Bool");

    // Verify Bool hint is functional: encoding ¬b should succeed (requires Bool sort for b)
    let bool_term1 = encoder1
        .encode_pure(&bool_expr)
        .unwrap_or_else(|err| panic!("Encoding ¬b after single registration failed: {err:?}"));
    let bool_term2 = encoder2
        .encode_pure(&bool_expr)
        .unwrap_or_else(|err| panic!("Encoding ¬b after double registration failed: {err:?}"));
    assert_eq!(
        format!("{bool_term1:?}"),
        format!("{bool_term2:?}"),
        "Bool encoding should be stable after double sort-hint registration"
    );

    // Verify Seq hint is functional: encoding v@.len() should succeed
    let seq_term1 = encoder1.encode_pure(&seq_expr).unwrap_or_else(|err| {
        panic!("Encoding v@.len() after single registration failed: {err:?}")
    });
    let seq_term2 = encoder2.encode_pure(&seq_expr).unwrap_or_else(|err| {
        panic!("Encoding v@.len() after double registration failed: {err:?}")
    });
    assert_eq!(
        format!("{seq_term1:?}"),
        format!("{seq_term2:?}"),
        "Seq encoding should be stable after double sort-hint registration"
    );
}

/// After `register_sort_hints`, `encode_pure` should not re-scan (guarded by
/// `sort_hints_registered` flag). Verify encoding succeeds with pre-registered hints.
#[test]
#[timeout(30000)]
fn test_encode_pure_skips_rescan_after_registration() {
    let expr = not(var("flag"));
    let mut encoder = AYEncoder::new();
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    // encode_pure should succeed without re-scanning
    let term = encoder
        .encode_pure(&expr)
        .unwrap_or_else(|err| panic!("encode_pure after register_sort_hints failed: {err:?}"));
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Sat),
        "encode_pure after register_sort_hints should produce a satisfiable term"
    );
}
// Expression traversal: multi-pass constant factor bound
// =============================================================================

/// Verifies that the combined cost of calling all four `expr_has_*` analysis
/// functions scales linearly with expression tree size.
///
/// The encoder calls `expr_needs_quantifiers`, `expr_has_closure_spec_method`,
/// `expr_has_tuple_fn`, and `expr_has_datatype_spec_method` in 4 separate
/// full-tree passes on each contract expression. This test confirms the total
/// overhead remains O(N) by measuring the 4-pass scan time at N=200 vs N=50
/// and checking the ratio is bounded.
///
/// Uses min-of-rounds measurement to reduce sensitivity to system load
/// spikes (concurrent cargo builds, GC pauses) that caused flaky failures
/// with single-shot wall-clock measurement (#1129).
///
/// If any of these functions accidentally introduced quadratic behavior (e.g.,
/// via cloning or allocation per node), the ratio would exceed the threshold.
#[test]
#[timeout(30000)]
fn test_expr_analysis_multi_pass_scaling_linear() {
    use std::time::Instant;

    use crate::expr::{
        expr_has_closure_spec_method, expr_has_datatype_spec_method, expr_has_tuple_fn,
        expr_needs_quantifiers,
    };

    /// Build a deeply nested expression chain of `x + (x + (x + ... ))` with
    /// method calls, logic fn calls, and nested operators to exercise all
    /// branches of the traversal functions.
    fn build_complex_expr(depth: usize) -> PureExpr {
        let mut expr = var("x");
        for i in 0..depth {
            // Alternate between different node types to exercise all arms
            expr = match i % 5 {
                0 => add(expr, var("y")),
                1 => method_call(expr, "len", vec![var("z")]),
                2 => logic_fn_call("helper", vec![expr]),
                3 => ite(gt(var("a"), int(0)), expr, var("b")),
                _ => view(expr),
            };
        }
        expr
    }

    let small_n = 50;
    let large_n = 200;
    let iters_per_round = 100;
    let num_rounds = 5;

    // Run all 4 analysis passes on the expression
    let scan_all = |expr: &PureExpr| {
        let _ = expr_needs_quantifiers(expr);
        let _ = expr_has_closure_spec_method(expr);
        let _ = expr_has_tuple_fn(expr);
        let _ = expr_has_datatype_spec_method(expr);
    };

    let small_expr = build_complex_expr(small_n);
    let large_expr = build_complex_expr(large_n);

    // Warm up both sizes to stabilize allocator and cache.
    for _ in 0..iters_per_round {
        scan_all(&small_expr);
        scan_all(&large_expr);
    }

    // Collect per-round ratios and take the min to filter out load spikes.
    let mut ratios = Vec::with_capacity(num_rounds);
    for _ in 0..num_rounds {
        let start = Instant::now();
        for _ in 0..iters_per_round {
            scan_all(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters_per_round {
            scan_all(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // Keep only the upper-bound regression check: lower bounds are flaky under
    // scheduler noise and cache effects on busy machines.
    // For O(N): ratio(200/50) ≈ 4x. For O(N²): ratio ≈ 16x.
    // Threshold 10x catches quadratic while tolerating system variance (#1129).
    // Previous threshold of 8x was too tight under concurrent worker load.
    assert!(
        min_ratio < 10.0,
        "expr_analysis 4-pass min scaling ratio ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, one of the expr_has_* traversals may have quadratic behavior. \
         Expected ~4x with O(N) per-pass scanning."
    );

    eprintln!(
        "expr_analysis_multi_pass: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x, O(N²) expect ~16x)"
    );
}
// =============================================================================
// Full 7-pass expression analysis: all feature detection passes scale linearly
// =============================================================================

/// Verifies that all 7 `expr_*` analysis functions used in
/// `setup_verification_encoder` and `bootstrap_encoder` scale linearly.
///
/// The existing `test_expr_analysis_multi_pass_scaling_linear` tests only 4 of
/// the 7 passes. This test covers all 7:
/// 1. `expr_needs_quantifiers`
/// 2. `expr_has_closure_spec_method`
/// 3. `expr_has_tuple_fn`
/// 4. `expr_has_datatype_spec_method`
/// 5. `expr_has_match_constructor_pattern`
/// 6. `expr_has_seq_index_on_final`
/// 7. `collect_logic_fn_names`
///
/// A single-pass visitor combining all 7 checks would reduce total work by 7x.
/// This test documents the current 7-pass cost and regression-tests linearity.
///
/// Re: performance_proofs phase — 7-pass redundant traversal finding
#[test]
#[timeout(30000)]
fn test_expr_analysis_all_7_passes_scaling_linear() {
    use std::time::Instant;

    use crate::{
        expr::{
            collect_logic_fn_names, expr_has_closure_spec_method, expr_has_datatype_spec_method,
            expr_has_match_constructor_pattern, expr_has_tuple_fn, expr_needs_quantifiers,
        },
        expr_seq::expr_has_seq_index_on_final,
    };

    /// Build an expression tree with diverse node types to exercise all 7
    /// analysis functions. Includes MethodCall, LogicFnCall, Match,
    /// Forall/Exists, View, Deref, Final, and Ite nodes.
    fn build_diverse_expr(depth: usize) -> PureExpr {
        let mut expr = var("x");
        for i in 0..depth {
            expr = match i % 7 {
                0 => add(expr, var("y")),
                1 => method_call(expr, "len", vec![var("z")]),
                2 => logic_fn_call("helper", vec![expr]),
                3 => ite(gt(var("a"), int(0)), expr, var("b")),
                4 => view(expr),
                5 => deref(expr),
                6 => final_expr(expr),
                _ => unreachable!(),
            };
        }
        expr
    }

    let small_n = 50;
    let large_n = 200;
    let iters_per_round = 80;
    let num_rounds = 5;

    // Run all 7 analysis passes on the expression
    let scan_all_7 = |expr: &PureExpr| {
        let _ = expr_needs_quantifiers(expr);
        let _ = expr_has_closure_spec_method(expr);
        let _ = expr_has_tuple_fn(expr);
        let _ = expr_has_datatype_spec_method(expr);
        let _ = expr_has_match_constructor_pattern(expr);
        let _ = expr_has_seq_index_on_final(expr);
        let mut names = HashSet::new();
        collect_logic_fn_names(expr, &mut names);
    };

    let small_expr = build_diverse_expr(small_n);
    let large_expr = build_diverse_expr(large_n);

    // Warm up
    for _ in 0..iters_per_round {
        scan_all_7(&small_expr);
        scan_all_7(&large_expr);
    }

    let mut ratios = Vec::with_capacity(num_rounds);
    for _ in 0..num_rounds {
        let start = Instant::now();
        for _ in 0..iters_per_round {
            scan_all_7(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters_per_round {
            scan_all_7(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(N): ratio(200/50) ≈ 4x. For O(N²): ratio ≈ 16x.
    // 7 passes at O(N) each = O(7N), still linear → ratio ≈ 4x.
    // Threshold 10x catches quadratic in any single pass.
    assert!(
        min_ratio < 10.0,
        "expr_analysis 7-pass min scaling ratio ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, one of the 7 expr analysis passes has quadratic behavior. \
         Expected ~4x with O(N) per-pass scanning."
    );

    eprintln!(
        "expr_analysis_all_7_passes: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x, 7 passes at O(N) each = O(7N) still linear)"
    );
}
// =============================================================================
// Sort hint collection: register_sort_hints scaling
// =============================================================================

/// Build a flat And-chain of N boolean comparisons: `(x0 > 0) && (x1 > 0) && ...`
fn build_flat_and_chain(n: usize) -> Vec<PureExpr> {
    (0..n).map(|i| gt(var(&format!("x{i}")), int(0))).collect()
}

/// Build a right-recursive Ite chain of depth D.
fn build_nested_ite_chain(depth: usize) -> PureExpr {
    let mut expr = var("leaf");
    for i in (0..depth).rev() {
        expr = ite(gt(var(&format!("c{i}")), int(0)), expr, int(0));
    }
    expr
}

/// `register_sort_hints` on flat And-chains scales linearly in expression count.
#[test]
#[timeout(30000)]
#[serial(perf)]
#[allow(clippy::cast_precision_loss)]
fn test_register_sort_hints_flat_chain_scales_linearly() {
    use std::time::Instant;

    let small_n = 100;
    let large_n = 400;
    let rounds = 5;
    let mut ratios: Vec<f64> = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        let small_exprs = build_flat_and_chain(small_n);
        let large_exprs = build_flat_and_chain(large_n);

        let start = Instant::now();
        let mut enc_small = AYEncoder::new();
        enc_small.register_sort_hints(&small_exprs);
        let small_time = start.elapsed();

        let start = Instant::now();
        let mut enc_large = AYEncoder::new();
        enc_large.register_sort_hints(&large_exprs);
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    assert!(
        median < 10.0,
        "register_sort_hints flat chain scaling ({large_n}/{small_n}) median = \
         {median:.1}x (rounds: {ratios:.1?}). \
         If > 10x, hint collection has regressed from O(N)."
    );

    eprintln!(
        "register_sort_hints flat chain: median={median:.1}x, rounds={ratios:.1?} \
         (O(N) expect ~4x)"
    );
}

/// `register_sort_hints` on nested Ite chains should stay subquadratic.
///
/// `collect_all_sort_hints` now threads a shared subtree cache through
/// `infer_expr_sort`, so repeated Bool checks on nested Ite branches should no
/// longer re-walk the full remaining tree. The linear target for a 4x larger
/// input is ~4x; allow up to 10x for noise while rejecting the old quadratic
/// ~16x behavior. (#2243)
///
/// Threshold 10x keeps the test stable across noisy CI while still failing if
/// hint collection regresses toward the previous quadratic bound.
#[test]
#[timeout(30000)]
#[serial(perf)]
#[allow(clippy::cast_precision_loss)]
fn test_register_sort_hints_nested_ite_subquadratic() {
    use std::time::Instant;

    let small_n = 100;
    let large_n = 400;
    let rounds = 5;
    let mut ratios: Vec<f64> = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        let small_expr = build_nested_ite_chain(small_n);
        let large_expr = build_nested_ite_chain(large_n);

        let start = Instant::now();
        let mut enc_small = AYEncoder::new();
        enc_small.register_sort_hints(std::slice::from_ref(&small_expr));
        let small_time = start.elapsed();

        let start = Instant::now();
        let mut enc_large = AYEncoder::new();
        enc_large.register_sort_hints(std::slice::from_ref(&large_expr));
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    assert!(
        median < 10.0,
        "register_sort_hints nested Ite scaling ({large_n}/{small_n}) median = \
         {median:.1}x (rounds: {ratios:.1?}). \
         Expected subquadratic after cached sort inference. If > 10x, \
         hint collection likely regressed toward quadratic behavior."
    );

    eprintln!(
        "register_sort_hints nested Ite: median={median:.1}x, rounds={ratios:.1?} \
         (cached sort inference target: <10x, linear ideal: ~4x)"
    );
}
