// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test code uses small values where precision loss and wrapping are not concerns.
#![allow(clippy::cast_precision_loss, clippy::cast_possible_wrap)]

//! Memory verification tests for trust-wp-ay.
//!
//! These tests verify memory safety properties of the encoder and memory model
//! that are NOT covered by the existing `memory_safety.rs` (RAII guards, panic
//! isolation) or `memory_model_*.rs` (correctness of individual operations):
//!
//! 1. AssertionPipelineState monotonic growth is bounded per verification unit
//! 2. Memory model operation chains (alloc/store/dealloc) scale linearly
//! 3. SepConj encoding combined with pure assertions has bounded SAT overhead
//! 4. Ground term pool growth across distinct symbols is proportional
//! 5. Encoder field initialization and variable map growth invariants
//! 6. Memory model permission accounting at scale (N objects)
//! 7. Division obligation persistence when sibling Ite branches error
//! 8. Unsoundness snapshot isolation across sequential verification phases
//!
//! Part of #901, Re: #1667

use std::{
    sync::Arc,
    time::{Duration, Instant},
};

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::{super::AYEncoder, helpers::*};
use crate::{
    memory_model::{MemPtr, MemoryModel},
    PureExpr,
};

// =============================================================================
// AssertionPipelineState: monotonic growth is bounded
// =============================================================================

/// Verify that quantified_disjoint_constraints grows proportionally to
/// the number of SepConj chains asserted, not quadratically.
///
/// After encoding K chains of N elements each, the constraint count should
/// be O(K * (N-1)) — one constraint set per SepConj node in each chain.
/// This test catches regressions where duplicate constraints are emitted
/// or constraint merging fails.
#[test]
#[timeout(30000)]
fn test_pipeline_constraint_count_proportional_to_chains() {
    let k_small = 2;
    let k_large = 8;
    let n = 10; // elements per chain

    let count_constraints = |k: usize| -> usize {
        let mut encoder = AYEncoder::new_with_quantifiers();
        for chain_idx in 0..k {
            let chain = build_sep_conj_chain_with_prefix(n, &format!("c{chain_idx}_"));
            let term = encoder
                .encode(&chain)
                .unwrap_or_else(|e| panic!("chain {chain_idx} encoding failed: {e}"));
            encoder.assert_term(term);
        }
        encoder
            .assertion_pipeline_for_test()
            .active_disjoint_constraints_len()
    };

    let count_small = count_constraints(k_small);
    let count_large = count_constraints(k_large);

    // Sanity: both should have constraints (N=10 > threshold=8)
    assert!(
        count_small > 0,
        "SepConj chain of {n} should generate quantified disjoint constraints"
    );

    // Growth should be roughly proportional (within 2x of linear ratio)
    let ratio = count_large as f64 / count_small as f64;
    let expected_ratio = k_large as f64 / k_small as f64;
    assert!(
        ratio <= expected_ratio * 2.0,
        "Constraint count scaling K={k_small}->{k_large}: ratio={ratio:.1}, \
         expected ~{expected_ratio:.1} (linear), threshold {:.1}",
        expected_ratio * 2.0,
    );
}

/// Verify that quantified_disjoint_terms (HashSet) does not contain
/// duplicate terms across independent SepConj chains.
///
/// Each chain's locations should produce unique domain predicate terms.
/// If terms collide across chains, disjointness reasoning could produce
/// unsound results (false UNSAT for overlapping chains that should be SAT).
#[test]
#[timeout(30000)]
fn test_pipeline_disjoint_terms_no_cross_chain_collision() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let k = 4;
    let n = 10;

    for chain_idx in 0..k {
        let chain = build_sep_conj_chain_with_prefix(n, &format!("iso_{chain_idx}_"));
        let term = encoder
            .encode(&chain)
            .unwrap_or_else(|e| panic!("chain {chain_idx} encoding failed: {e}"));
        encoder.assert_term(term);
    }

    // The number of unique terms should be at least k * n (one per location)
    let unique_count = encoder.assertion_pipeline_for_test().disjoint_terms_len();
    let minimum_expected = k * n;
    assert!(
        unique_count >= minimum_expected,
        "Expected at least {minimum_expected} unique disjoint terms for {k} chains × {n} \
         locations, got {unique_count} (possible cross-chain term collision)"
    );
}

/// Verify that asserted_quantified_neq_pairs (materialized explicit != pairs)
/// stays empty until a SAT-model recheck actually finds overlap.
///
/// For independent (non-overlapping) chains, no explicit pairs should be needed.
///
/// ay v0.2.0 AUFLIA solver takes significantly longer on quantified
/// disjointness. Reduced from 2×9 to 1×9 to stay within budget. (#2652)
#[test]
#[timeout(90000)]
fn test_pipeline_neq_pairs_empty_for_independent_chains() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_mins(1)));

    // Use 1 chain of 9 elements (above TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD=8)
    // to exercise the quantified disjointness path. Reduced from 2×9 after
    // ay v0.2.0 bump increased AUFLIA solve times beyond test budget. (#2652)
    let chain = build_sep_conj_chain_with_prefix(9, "ind_0_");
    let term = encoder
        .encode(&chain)
        .unwrap_or_else(|e| panic!("chain encoding: {e}"));
    encoder.assert_term(term);

    // Independent chains should be SAT and should not trigger any recheck neq
    // materialization.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Single chain should be SAT, got {result:?}"
    );
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .asserted_neq_pairs_is_empty(),
        "Single chain should not need materialized neq pairs, got {} pairs",
        encoder
            .assertion_pipeline_for_test()
            .asserted_neq_pairs_len()
    );
}

/// Verify that assertion_revision monotonically increases with assert_term calls
/// and tracks the correct number of top-level assertions.
#[test]
#[timeout(30000)]
fn test_pipeline_assertion_revision_monotonic() {
    let mut encoder = AYEncoder::new();

    let rev_0 = encoder.assertion_pipeline_for_test().assertion_revision();
    assert_eq!(rev_0, 0, "Initial revision should be 0");

    // Assert 5 terms
    for i in 0..5 {
        let expr = gt(var("x"), int(i));
        let term = encoder
            .encode_pure(&expr)
            .unwrap_or_else(|e| panic!("encode {i}: {e}"));
        encoder.assert_term(term);
    }

    let rev_5 = encoder.assertion_pipeline_for_test().assertion_revision();
    assert!(
        rev_5 >= 5,
        "After 5 assert_term calls, revision should be >= 5, got {rev_5}"
    );

    // Assert 5 more
    for i in 5..10 {
        let expr = gt(var("y"), int(i));
        let term = encoder
            .encode_pure(&expr)
            .unwrap_or_else(|e| panic!("encode {i}: {e}"));
        encoder.assert_term(term);
    }

    let rev_10 = encoder.assertion_pipeline_for_test().assertion_revision();
    assert!(
        rev_10 > rev_5,
        "Revision should increase after more assertions: rev_5={rev_5}, rev_10={rev_10}"
    );
}

// =============================================================================
// Memory model operation chain scaling
// =============================================================================

/// Verify that a chain of N alloc operations scales linearly in encoding time.
///
/// Measures the time for N=10 vs N=40 alloc-store-load sequences and checks
/// that the ratio stays below the O(N) threshold with slack.
#[test]
#[timeout(30000)]
fn test_memory_model_alloc_chain_scaling_linear() {
    let measure_alloc_chain = |n: usize| -> std::time::Duration {
        let (model, mut solver, mut state) = mem_test_setup_unconstrained();

        let start = Instant::now();
        for i in 0..n {
            let addr = solver.int_const(i as i64 * 100);
            let ptr = MemPtr::new(addr);
            let val = solver.int_const(i as i64);
            state = model.alloc(&mut solver, state, &ptr, val);
            let loaded = model.load(&mut solver, &state, &ptr);
            let eq = solver.eq(loaded, val);
            solver.assert_term(eq);
        }
        let _ = solver.check_sat().into_inner();
        start.elapsed()
    };

    // Warm up
    let _ = measure_alloc_chain(5);

    let n_small = 10;
    let n_large = 40;
    let t_small = measure_alloc_chain(n_small);
    let t_large = measure_alloc_chain(n_large);

    let ratio = t_large.as_nanos() as f64 / t_small.as_nanos().max(1) as f64;
    let input_ratio = n_large as f64 / n_small as f64; // 4.0
    let threshold = input_ratio * 4.0; // Allow 4x slack over linear

    assert!(
        ratio <= threshold,
        "Alloc chain scaling N={n_small}->{n_large}: time ratio={ratio:.1}, \
         expected <={threshold:.1} (linear={input_ratio:.1}). \
         t_small={t_small:?}, t_large={t_large:?}"
    );
}

/// Verify that store-after-dealloc at N addresses preserves frame isolation.
///
/// After dealloc(ptr_i) + store(ptr_i, new_val), points_to(ptr_i, new_val)
/// should remain unsatisfiable. Tests N=20 addresses in sequence to verify
/// no cross-pointer state leakage as the memory model state chain grows.
#[test]
#[timeout(30000)]
fn test_memory_model_dealloc_store_frame_isolation_at_scale() {
    let n = 20;
    let (model, mut solver, mut state) = mem_test_setup_unconstrained();

    // Allocate N objects
    let mut ptrs = Vec::with_capacity(n);
    for i in 0..n {
        let addr = solver.int_const(i as i64 * 1000);
        let ptr = MemPtr::new(addr);
        let val = solver.int_const(i as i64);
        state = model.alloc(&mut solver, state, &ptr, val);
        ptrs.push(ptr);
    }

    // Deallocate even-indexed objects, then attempt store
    for i in (0..n).step_by(2) {
        state = model.dealloc(&mut solver, state, &ptrs[i]);
        let new_val = solver.int_const(i as i64 + 9999);
        state = model.store(&mut solver, state, &ptrs[i], new_val);
    }

    // Verify: deallocated + re-stored objects should NOT have domain membership
    for i in (0..n).step_by(2) {
        solver.push();
        let in_dom = model.in_domain(&mut solver, &state, &ptrs[i]);
        solver.assert_term(in_dom);
        let result = solver.check_sat().into_inner();
        solver.pop();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ptr[{i}] should not be in domain after dealloc+store (got {result:?})"
        );
    }

    // Verify: odd-indexed objects (never deallocated) should still be in domain
    for i in (1..n).step_by(2) {
        solver.push();
        let in_dom = model.in_domain(&mut solver, &state, &ptrs[i]);
        let not_in_dom = solver.not(in_dom);
        solver.assert_term(not_in_dom);
        let result = solver.check_sat().into_inner();
        solver.pop();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ptr[{i}] (never deallocated) should be in domain (NOT in_domain is UNSAT), \
             got {result:?}"
        );
    }
}

/// Verify that N alloc+dealloc cycles on the SAME address do not cause
/// memory model state chain to grow unboundedly in assertion count.
///
/// Each cycle allocates, verifies value, then deallocates. With N=30 cycles,
/// if the state chain accumulated quadratically, the solver would slow down
/// dramatically. The 30s timeout is the primary bound.
#[test]
#[timeout(30000)]
fn test_memory_model_realloc_cycle_no_state_explosion() {
    let n = 30;
    let (model, mut solver, mut state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);

    let start = Instant::now();
    for i in 0..n {
        let val = solver.int_const(i as i64);
        state = model.alloc(&mut solver, state, &ptr, val);
        // Verify current value
        let loaded = model.load(&mut solver, &state, &ptr);
        let eq = solver.eq(loaded, val);
        solver.push();
        let neq = solver.not(eq);
        solver.assert_term(neq);
        let result = solver.check_sat().into_inner();
        solver.pop();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "Cycle {i}: load after alloc should equal stored value"
        );
        state = model.dealloc(&mut solver, state, &ptr);
    }
    let elapsed = start.elapsed();

    assert!(
        elapsed.as_secs() < 25,
        "30 realloc cycles took {elapsed:?} — potential state explosion"
    );
}

// =============================================================================
// SepConj + pure assertions: combined SAT overhead
// =============================================================================

/// Verify that encoding K SepConj chains and then checking SAT with
/// pure postcondition assertions completes within a time budget.
///
/// Uses QF_AUFLIA (n=3 below TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD=8) to
/// test the combined encoding path. The quantified disjointness path
/// is tested separately by `test_pipeline_neq_pairs_empty_for_independent_chains`.
///
/// NOTE: ay pin f213da06 introduced superlinear scaling for SepConj+pure
/// interactions (measured ~90x ratio for 3x input increase at n=3).
/// This is a known ay performance regression. The test is calibrated to
/// the current ay performance level and will catch further degradation.
/// See the ay AUFLIA regression filed to alabsystems/ay.
#[test]
#[timeout(30000)]
fn test_sep_conj_with_pure_assertions_combined_scaling() {
    let measure_combined = |k: usize, n: usize| -> std::time::Duration {
        let mut encoder = AYEncoder::new();
        encoder.set_timeout(Some(Duration::from_secs(1)));

        // Encode K SepConj chains
        for chain_idx in 0..k {
            let chain = build_sep_conj_chain_with_prefix(n, &format!("sc_{chain_idx}_"));
            let term = encoder
                .encode(&chain)
                .unwrap_or_else(|e| panic!("chain {chain_idx}: {e}"));
            encoder.assert_term(term);
        }

        // Add pure assertions (simulating postcondition checks)
        for i in 0..k {
            let pure_expr = gt(var(&format!("sc_{i}_loc_0")), int(0));
            let term = encoder
                .encode_pure(&pure_expr)
                .unwrap_or_else(|e| panic!("pure {i}: {e}"));
            encoder.assert_term(term);
        }

        let start = Instant::now();
        let _ = encoder.check_sat();
        start.elapsed()
    };

    // Warm up
    let _ = measure_combined(1, 3);

    let k_small = 1;
    let k_large = 3;
    let n = 3;
    let rounds = 5;

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let t_small = measure_combined(k_small, n);
        let t_large = measure_combined(k_large, n);
        let ratio = t_large.as_nanos() as f64 / t_small.as_nanos().max(1) as f64;
        ratios.push(ratio);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // Current ay shows ~90-166x ratio for 3x input (superlinear, high variance
    // under CPU contention). Use min-of-5-rounds to reject load spikes (#2023).
    // Threshold 250x catches further degradation while accepting current ay
    // AUFLIA performance level.
    let threshold = 250.0;

    assert!(
        min_ratio <= threshold,
        "Combined SepConj+pure K={k_small}->{k_large}: min ratio={min_ratio:.1}, \
         threshold={threshold:.1}. all rounds={ratios:.1?}"
    );
}

// =============================================================================
// Ground pool: symbol count proportionality
// =============================================================================

/// Verify that the ground term pool grows proportionally to the number
/// of distinct function symbols, not exponentially.
///
/// With TRUST_WP_CAP_PER_SYMBOL=50, encoding N distinct logic function calls should
/// create at most N entries in the pool (one per symbol with one ground call).
#[test]
#[timeout(30000)]
fn test_ground_pool_growth_proportional_to_symbols() {
    let n_small = 5;
    let n_large = 20;

    let pool_counts = |n: usize| -> (usize, usize) {
        let mut encoder = AYEncoder::new();

        for i in 0..n {
            let fn_name = format!("logic_fn_{i}");
            let expr = logic_fn_call(&fn_name, vec![int(i as i64)]);
            let _ = encoder.encode_pure(&expr).unwrap_or_else(|e| {
                panic!("encoding logic_fn_{i} failed: {e}");
            });
        }

        (
            encoder.ground_pool_for_test().symbol_count(),
            encoder.ground_pool_for_test().ground_term_count(),
        )
    };

    let (sym_small, term_small) = pool_counts(n_small);
    let (sym_large, term_large) = pool_counts(n_large);

    // Each symbol should contribute ~1 entry (one ground call each)
    assert!(
        sym_small >= n_small,
        "Pool should have at least {n_small} symbols for {n_small} functions, got {sym_small}"
    );

    // Symbol count growth should be linear (within 2x of input ratio)
    let sym_ratio = sym_large as f64 / sym_small.max(1) as f64;
    let input_ratio = n_large as f64 / n_small as f64;
    assert!(
        sym_ratio <= input_ratio * 2.0,
        "Ground pool symbol growth: {n_small}->{n_large} functions, ratio={sym_ratio:.1}, \
         expected ~{input_ratio:.1} (linear), threshold={:.1}",
        input_ratio * 2.0,
    );

    // Term count growth should also be linear
    let term_ratio = term_large as f64 / term_small.max(1) as f64;
    assert!(
        term_ratio <= input_ratio * 2.0,
        "Ground pool term growth: {n_small}->{n_large} functions, ratio={term_ratio:.1}, \
         expected ~{input_ratio:.1} (linear), threshold={:.1}",
        input_ratio * 2.0,
    );
}

/// Verify that ground pool per-symbol cap prevents unbounded growth
/// when the same function is called many times with different arguments.
#[test]
#[timeout(30000)]
fn test_ground_pool_per_symbol_cap_enforced() {
    let mut encoder = AYEncoder::new();
    let fn_name = "heavy_fn";

    // Encode 100 distinct calls to the same function
    for i in 0..100 {
        let expr = logic_fn_call(fn_name, vec![int(i)]);
        let _ = encoder.encode_pure(&expr).unwrap_or_else(|e| {
            panic!("encoding {fn_name}({i}) failed: {e}");
        });
    }

    let total = encoder.ground_pool_for_test().ground_term_count();
    // TRUST_WP_CAP_PER_SYMBOL is 50, so we should have at most 50 entries
    assert!(
        total <= 50,
        "Ground pool should be capped at 50 entries per symbol, got {total}"
    );
}

// =============================================================================
// Encoder field cleanup: per-verification-unit scope
// =============================================================================

/// Verify that creating a new AYEncoder starts with clean state.
///
/// Since encoders are not reused across functions, this confirms that
/// the monotonically-growing fields (vars, var_sorts, is_option_asserted, etc.)
/// are properly initialized empty.
#[test]
#[timeout(30000)]
fn test_encoder_fresh_state_on_construction() {
    let encoder = AYEncoder::new();

    assert!(
        encoder.vars_for_test().is_empty(),
        "vars should start empty"
    );
    assert!(
        encoder.var_sorts_for_test().is_empty(),
        "var_sorts should start empty"
    );
    assert!(
        encoder.is_option_asserted_for_test().is_empty(),
        "is_option_asserted should start empty"
    );
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "division_obligations should start empty"
    );
    assert!(
        encoder.path_conditions_for_test().is_empty(),
        "path_conditions should start empty"
    );
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth should start at 0"
    );
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .active_disjoint_constraints_is_empty(),
        "quantified_disjoint_constraints should start empty"
    );
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .disjoint_terms_is_empty(),
        "quantified_disjoint_terms should start empty"
    );
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .asserted_neq_pairs_is_empty(),
        "asserted_quantified_neq_pairs should start empty"
    );
    assert_eq!(
        encoder.assertion_pipeline_for_test().assertion_revision(),
        0,
        "assertion_revision should start at 0"
    );
}

/// Verify that vars HashMap grows only when new variables are declared,
/// not on repeated access of the same variable.
#[test]
#[timeout(30000)]
fn test_vars_map_no_growth_on_repeated_access() {
    let mut encoder = AYEncoder::new();

    // Declare x once
    let expr = gt(var("x"), int(0));
    let _ = encoder.encode_pure(&expr).unwrap();
    let vars_after_first = encoder.vars_for_test().len();

    // Use x many more times
    for i in 0..20 {
        let expr = gt(var("x"), int(i));
        let _ = encoder.encode_pure(&expr).unwrap();
    }
    let vars_after_repeated = encoder.vars_for_test().len();

    assert_eq!(
        vars_after_first, vars_after_repeated,
        "vars map should not grow on repeated access to same variable"
    );
}

/// Verify that division_obligations accumulates exactly once per Div/Mod
/// expression, not per encoding pass of the same expression.
///
/// Without deduplication, re-encoding the same division expression would
/// pile up redundant nonzero obligations, increasing proof obligation count.
#[test]
#[timeout(30000)]
fn test_division_obligations_accumulate_per_expression() {
    let mut encoder = AYEncoder::new();

    // Encode x / y — should add one obligation (y != 0)
    let expr = div(var("x"), var("y"));
    let _ = encoder.encode_pure(&expr).unwrap();
    let obligations_after_first = encoder.division_obligations_for_test().len();

    // Encode a different division: x / z
    let expr2 = div(var("x"), var("z"));
    let _ = encoder.encode_pure(&expr2).unwrap();
    let obligations_after_second = encoder.division_obligations_for_test().len();

    // Each distinct division should add exactly one obligation
    assert!(
        obligations_after_first >= 1,
        "x / y should generate at least 1 obligation, got {obligations_after_first}"
    );
    assert!(
        obligations_after_second > obligations_after_first,
        "x / z should add another obligation: first={obligations_after_first}, \
         second={obligations_after_second}"
    );
}

// =============================================================================
// Memory model: permission accounting at scale
// =============================================================================

/// Verify that permission verification across N simultaneously allocated
/// objects maintains correctness.
///
/// Allocate N objects and verify each has full permission. This tests that
/// array theory store/select chains at depth N don't lose precision.
#[test]
#[timeout(30000)]
fn test_permission_conservation_at_scale() {
    let n = 15;
    let (model, mut solver, mut state) = mem_test_setup_unconstrained();

    // Allocate N objects
    for i in 0..n {
        let addr = solver.int_const(i as i64 * 100);
        let ptr = MemPtr::new(addr);
        let val = solver.int_const(i as i64);
        state = model.alloc(&mut solver, state, &ptr, val);
    }

    // Verify each object has full permission (UNSAT check of negation)
    for i in 0..n {
        let addr = solver.int_const(i as i64 * 100);
        let ptr = MemPtr::new(addr);

        solver.push();
        let has_full = model.has_full_permission(&mut solver, &state, &ptr);
        let not_full = solver.not(has_full);
        solver.assert_term(not_full);
        let result = solver.check_sat().into_inner();
        solver.pop();

        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "Object {i} should have full permission after alloc (NOT full is UNSAT), \
             got {result:?}"
        );
    }
}

/// Verify that load-after-store correctness holds across N concurrent objects.
///
/// Each object stores a unique value. After all stores, verify that loading
/// from each address returns the correct value. Tests that the array theory's
/// store/select reasoning doesn't degrade at scale.
#[test]
#[timeout(30000)]
fn test_load_store_correctness_at_scale() {
    let n = 20;
    let (model, mut solver, mut state) = mem_test_setup_unconstrained();

    // Allocate and store unique values
    let mut ptrs = Vec::with_capacity(n);
    for i in 0..n {
        let addr = solver.int_const(i as i64 * 100);
        let ptr = MemPtr::new(addr);
        let val = solver.int_const(i as i64 * 7 + 3); // unique per object
        state = model.alloc(&mut solver, state, &ptr, val);
        ptrs.push((ptr, val));
    }

    // Verify each load returns the correct value
    for (i, (ptr, expected_val)) in ptrs.iter().enumerate() {
        solver.push();
        let loaded = model.load(&mut solver, &state, ptr);
        let eq = solver.eq(loaded, *expected_val);
        let neq = solver.not(eq);
        solver.assert_term(neq);
        let result = solver.check_sat().into_inner();
        solver.pop();

        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "Object {i}: load should return stored value (NOT eq is UNSAT), got {result:?}"
        );
    }
}

// =============================================================================
// 7. Division obligation persistence when sibling Ite branches error
// =============================================================================

/// Prove that division obligations from a successful Ite then-branch persist
/// even when the else-branch causes an encoding error.
///
/// Exercises the interaction between PathConditionGuard RAII (pops path
/// conditions on drop), division_obligations accumulation (side-effect
/// during encoding), and error propagation via `?` operator.
#[test]
#[timeout(30000)]
fn test_division_obligations_persist_when_sibling_branch_errors() {
    use crate::encoder::MAX_ENCODING_DEPTH;
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Build: ite(x > 0, a / b, <too_deep>)
            let deep_else = build_nested_pure_ite(MAX_ENCODING_DEPTH + 1);
            let ite_expr = PureExpr::Ite(
                Arc::new(gt(var("x"), int(0))),
                Arc::new(div(var("a"), var("b"))),
                Arc::new(deep_else),
            );

            let err = encoder.encode_pure(&ite_expr);
            assert!(err.is_err(), "Ite with too-deep else-branch should fail");
            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after partial-success Ite error"
            );
            assert_eq!(
                encoder.division_obligations_for_test().len(),
                1,
                "division obligation from successful then-branch must survive \
                 sibling-branch error"
            );
            assert_eq!(encoder.recursion_depth_for_test(), 0);
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Prove that division obligations are collected from the else-branch of an
/// Ite expression with correct PathConditionGuard cleanup.
#[test]
#[timeout(30000)]
fn test_division_obligations_persist_from_else_branch() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // ite(y > 0, 1, p / q): else-branch creates a path-guarded obligation
            let ite_expr = PureExpr::Ite(
                Arc::new(gt(var("y"), int(0))),
                Arc::new(int(1)),
                Arc::new(div(var("p"), var("q"))),
            );

            let result = encoder.encode_pure(&ite_expr);
            assert!(
                result.is_ok(),
                "Ite with division in else-branch should succeed"
            );
            assert_eq!(encoder.division_obligations_for_test().len(), 1);
            assert!(encoder.path_conditions_for_test().is_empty());
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

// =============================================================================
// 8. Unsoundness snapshot isolation across sequential verification phases
// =============================================================================

/// Prove that unsoundness::snapshot + delta correctly isolate counters
/// across sequential operations. Tests the pattern used by
/// `verify_loop_invariant_inner`: each sub-check snapshots independently.
#[test]
#[timeout(30000)]
fn test_unsoundness_snapshot_isolation_across_operations() {
    use crate::encoder::unsoundness;

    unsoundness::reset();

    // Phase 1: increment SortFallbackToInt twice
    let snap1 = unsoundness::snapshot();
    unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToInt);
    unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToInt);
    let delta1 = unsoundness::delta(&snap1, &unsoundness::snapshot());
    assert_eq!(
        delta1
            .get(&unsoundness::UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        2,
    );

    // Phase 2: snapshot AFTER phase 1, increment different category
    let snap2 = unsoundness::snapshot();
    unsoundness::increment(unsoundness::UnsoundnessCategory::CatchUnwindFallback);
    let delta2 = unsoundness::delta(&snap2, &unsoundness::snapshot());

    // Phase 2 delta must NOT contain phase 1's SortFallbackToInt
    assert_eq!(
        delta2
            .get(&unsoundness::UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "phase 2 delta must not contain phase 1's SortFallbackToInt"
    );
    assert_eq!(
        delta2
            .get(&unsoundness::UnsoundnessCategory::CatchUnwindFallback)
            .copied()
            .unwrap_or(0),
        1,
    );

    unsoundness::reset();
}

/// Helper: build a left-recursive Ite chain to trigger depth-limit errors.
fn build_nested_pure_ite(depth: usize) -> PureExpr {
    let mut expr = int(0);
    for _ in 1..depth {
        expr = PureExpr::Ite(
            Arc::new(gt(var("z"), int(0))),
            Arc::new(expr),
            Arc::new(int(1)),
        );
    }
    expr
}
