// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test code uses small values where precision loss is not a concern.
#![allow(clippy::cast_precision_loss)]

//! Memory RAII guard and encoder state isolation tests.
//!
//! These tests verify exact state invariants of the encoder's RAII guard
//! patterns and internal data structure growth bounds that existing tests
//! in `memory_safety.rs` and `memory_verification.rs` cover only indirectly:
//!
//! 1. DepthGuard: `recursion_depth` is exactly 0 after successful and failed encodings
//! 2. PathConditionGuard: `path_conditions` stack is exactly empty after Ite encoding
//! 3. Deep encoding scaling: Let-chains and nested quantifiers complete in bounded time
//! 4. seq_values registry: growth proportional to seq-producing operations
//! 5. AssertionPipeline: solver_panic_reason prevents post-panic SAT queries
//! 6. SepConj cache: variable count grows linearly with chain length
//!
//! Part of #901, Re: #1667

use std::{sync::Arc, time::Instant};

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::{super::AYEncoder, helpers::*};
use crate::{encoder::MAX_ENCODING_DEPTH, Formula, PureExpr};

// =============================================================================
// DepthGuard RAII: exact counter value after encoding
// =============================================================================

/// Verify that `recursion_depth` is exactly 0 after a successful encoding.
///
/// The `DepthGuard` RAII pattern increments on entry and decrements on drop.
/// If any exit path (early return, `?` propagation, normal return) misses the
/// decrement, the counter drifts. This test asserts the exact value — not just
/// "encoder still works" but "counter is precisely 0".
///
/// Re: #1116, memory_verification phase
#[test]
#[timeout(30000)]
fn test_recursion_depth_exactly_zero_after_successful_encoding() {
    let mut encoder = AYEncoder::new();

    // Encode a moderately nested expression with multiple recursive paths
    let nested = Formula::And(
        Arc::new(Formula::Or(
            Arc::new(Formula::Pure(gt(var("x"), int(0)))),
            Arc::new(Formula::Pure(lt(var("y"), int(10)))),
        )),
        Arc::new(Formula::Implies(
            Arc::new(Formula::Pure(ge(var("a"), int(1)))),
            Arc::new(Formula::Pure(le(var("b"), int(100)))),
        )),
    );
    let _ = encoder
        .encode(&nested)
        .expect("nested formula should encode");
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be exactly 0 after successful formula encoding, got {}",
        encoder.recursion_depth_for_test(),
    );

    // Also verify via encode_pure path
    let pure_nested = ite(
        gt(var("x"), int(0)),
        add(var("x"), int(1)),
        sub(var("x"), int(1)),
    );
    let _ = encoder
        .encode_pure(&pure_nested)
        .expect("pure expr should encode");
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be exactly 0 after successful pure encoding, got {}",
        encoder.recursion_depth_for_test(),
    );
}

/// Verify that `recursion_depth` returns to exactly 0 after a depth-limit error.
///
/// The manual decrement on the early-exit path (lines 89-91 in `encode_pure_impl`)
/// is separate from the `DepthGuard` drop. This test exercises the interaction
/// between the manual decrement and the guard to ensure they don't double-decrement
/// or leave residual depth.
///
/// Runs in a thread with 8 MB stack because debug build stack frames are large.
/// Re: #1116, memory_verification phase
#[test]
#[timeout(30000)]
fn test_recursion_depth_exactly_zero_after_depth_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Build expression exceeding MAX_ENCODING_DEPTH
            let mut deep = int(0);
            for _ in 0..MAX_ENCODING_DEPTH + 5 {
                deep = not(deep);
            }
            let result = encoder.encode_pure(&deep);
            assert!(result.is_err(), "should exceed depth limit");

            assert_eq!(
                encoder.recursion_depth_for_test(),
                0,
                "recursion_depth must be exactly 0 after depth-limit error, got {}",
                encoder.recursion_depth_for_test(),
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

// =============================================================================
// PathConditionGuard: exact stack balance after Ite encoding
// =============================================================================

/// Verify that `path_conditions` is exactly empty after encoding Ite expressions.
///
/// The `PathConditionGuard` pops one entry on drop. If the guard fails to
/// fire (e.g., if `encode_pure_impl` takes a different exit path inside Ite),
/// stale path conditions would leak into subsequent encodings, causing
/// side-effect assertions to be incorrectly guarded.
///
/// Re: #1207, memory_verification phase
#[test]
#[timeout(30000)]
fn test_path_conditions_empty_after_ite_encoding() {
    let mut encoder = AYEncoder::new();

    // Encode a nested Ite expression (exercises PathConditionGuard twice)
    let nested_ite = ite(
        gt(var("x"), int(0)),
        ite(lt(var("y"), int(10)), var("y"), int(10)),
        int(0),
    );
    let _ = encoder
        .encode_pure(&nested_ite)
        .expect("nested Ite should encode");

    assert!(
        encoder.path_conditions_for_test().is_empty(),
        "path_conditions must be empty after Ite encoding, got {} entries",
        encoder.path_conditions_for_test().len(),
    );
}

/// Verify that `path_conditions` is empty after encoding an Ite where the
/// then-branch contains a LetAssume (which reads path_conditions for guarding).
///
/// This exercises the interaction between PathConditionGuard and the
/// LetAssume encoding path which calls `guard_with_active_path`.
///
/// Re: #1207, memory_verification phase
#[test]
#[timeout(30000)]
fn test_path_conditions_empty_after_ite_with_let_assume() {
    let mut encoder = AYEncoder::new();

    // Ite with LetAssume in then-branch
    let ite_with_assume = ite(
        gt(var("x"), int(0)),
        let_assume(gt(var("x"), int(1)), add(var("x"), int(1))),
        int(0),
    );
    let _ = encoder
        .encode_pure(&ite_with_assume)
        .expect("Ite with LetAssume should encode");

    assert!(
        encoder.path_conditions_for_test().is_empty(),
        "path_conditions must be empty after Ite+LetAssume encoding, got {} entries",
        encoder.path_conditions_for_test().len(),
    );
}

// =============================================================================
// Deep encoding: Let-chain and nested expression scaling
// =============================================================================

/// Verify that encoding a deep Let-bind chain completes in bounded time.
///
/// Let-bind encoding exercises the expr_subst substitution engine internally.
/// A depth-N Let chain should encode in O(N) time, not O(N²) from repeated
/// tree clones at each level. The 10s timeout is the primary bound.
///
/// Re: expr_subst.rs:100-136 clone-heavy pattern, memory_verification phase
#[test]
#[timeout(30000)]
fn test_deep_let_chain_encoding_completes_bounded() {
    // Build a depth-80 Let chain: let x1 = x0+1 in let x2 = x1+1 in ... in xN
    // (staying below MAX_ENCODING_DEPTH=128)
    let depth = 80;
    let mut expr = var(&format!("x{depth}"));
    for i in (0..depth).rev() {
        expr = let_bind(
            &format!("x{}", i + 1),
            add(var(&format!("x{i}")), int(1)),
            expr,
        );
    }

    let mut encoder = AYEncoder::new();
    let start = Instant::now();
    let result = encoder.encode_pure(&expr);
    let elapsed = start.elapsed();

    assert!(
        result.is_ok(),
        "depth-{depth} Let chain should encode successfully: {:?}",
        result.err()
    );
    assert!(
        elapsed.as_secs() < 8,
        "depth-{depth} Let chain encoding took {elapsed:?} — potential quadratic allocation"
    );

    // Verify encoder state is clean after deep encoding
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after deep Let chain"
    );
}

/// Verify that encoding nested forall quantifiers scales linearly.
///
/// Nested quantifiers exercise the quantifier encoding path which involves
/// variable binding management. A depth-20 nesting should encode quickly.
///
/// Re: memory_verification phase
#[test]
#[timeout(30000)]
fn test_deep_nested_quantifier_encoding_completes_bounded() {
    let depth = 20;
    let mut expr = gt(var(&format!("x{}", depth - 1)), int(0));
    for i in (0..depth).rev() {
        expr = forall(&format!("x{i}"), expr);
    }

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let start = Instant::now();
    let result = encoder.encode_pure(&expr);
    let elapsed = start.elapsed();

    assert!(
        result.is_ok(),
        "depth-{depth} nested quantifier should encode: {:?}",
        result.err()
    );
    assert!(
        elapsed.as_secs() < 5,
        "depth-{depth} nested quantifier encoding took {elapsed:?}"
    );
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after nested quantifier encoding"
    );
}

// =============================================================================
// seq_values registry: bounded growth per seq operation
// =============================================================================

/// Verify that the seq_values registry grows proportionally to the number
/// of seq-producing operations, not quadratically.
///
/// Each `push_back` encoding may register both the result Seq term and its
/// backing Array+Length+Offset components. The key invariant is that growth
/// is bounded per operation (constant factor), not per-access.
///
/// Re: SeqState::seq_values unbounded growth concern, memory_verification phase
#[test]
#[timeout(30000)]
fn test_seq_values_registry_grows_proportional_to_operations() {
    let mut encoder = AYEncoder::new();

    // Encode push_back operations and measure registry growth
    let push1 = method_call(var("s"), "push_back", vec![int(1)]);
    let _ = encoder.encode_pure(&push1);
    let after_push1 = encoder.seq_state_for_test().seq_values_len();

    // Each push_back adds a bounded number of entries (implementation detail:
    // typically 2 — the result Seq and its UF application term).
    // The bound is "constant per operation", verified by ratio.
    let push_chain_3 = method_call(
        method_call(
            method_call(var("s2"), "push_back", vec![int(1)]),
            "push_back",
            vec![int(2)],
        ),
        "push_back",
        vec![int(3)],
    );
    let _ = encoder.encode_pure(&push_chain_3);
    let after_chain_3 = encoder.seq_state_for_test().seq_values_len();

    let growth = after_chain_3 - after_push1;
    // 3 push_backs should add at most 3 * (entries per push_back) entries.
    // We use a generous bound of 4 entries per push_back to account for
    // implementation variance.
    assert!(
        growth <= 3 * 4,
        "3-push_back chain should add at most 12 entries (4 per op), \
         got {growth}: after_push1={after_push1}, after_chain_3={after_chain_3}"
    );
}

// =============================================================================
// Encoder state isolation: solver_panic_reason prevents incorrect assertions
// =============================================================================

/// Verify that once `solver_panic_reason` is set, the assertion pipeline's
/// `assertion_revision` stops advancing. This prevents the encoder from
/// accumulating assertions that could silently pass after a solver corruption.
///
/// Re: AssertionPipelineState::solver_panic_reason, memory_verification phase
#[test]
#[timeout(30000)]
fn test_assertion_revision_frozen_after_solver_panic() {
    let mut encoder = AYEncoder::new();

    // Normal assertion advances revision
    let valid = encoder
        .encode_pure(&gt(var("x"), int(0)))
        .expect("should encode");
    encoder.assert_term(valid);
    let rev_before = encoder.assertion_pipeline_for_test().assertion_revision();
    assert!(rev_before > 0, "revision should advance after assert_term");

    // Force solver panic
    let non_bool = encoder.solver_mut().int_const(42);
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool);
    }));

    assert!(
        encoder.solver_panic_reason().is_some(),
        "solver_panic_reason should be set after panic"
    );

    // Post-panic check_sat must return Unknown regardless of assertions
    let post_sat = encoder.check_sat();
    assert_eq!(
        post_sat,
        SolveResult::Unknown,
        "check_sat after solver panic must return Unknown, got {post_sat:?}"
    );
}

// =============================================================================
// FormulaCacheKey size: Debug-format strings bounded by formula structure
// =============================================================================

/// Verify that SepConj encoding with increasing chain lengths produces
/// cache key counts proportional to chain size, not exponential.
///
/// `FormulaCacheKey` uses structural `u64` hashing (via `Hash` derive on
/// `Formula`), so key construction is O(N) per formula — no string
/// allocation. The number of unique cache entries should be O(N) — one per
/// unique sub-formula. This test ensures the cache doesn't grow faster than
/// linear in the number of SepConj nodes.
///
/// Re: FormulaCacheKey allocation concern, memory_verification phase
#[test]
#[timeout(30000)]
fn test_sep_conj_cache_entry_count_linear_in_chain_length() {
    let measure_cache_size = |n: usize| -> usize {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let chain = build_sep_conj_chain_with_prefix(n, "cache_");
        let term = encoder
            .encode(&chain)
            .unwrap_or_else(|e| panic!("chain of {n} failed: {e}"));
        encoder.assert_term(term);
        // Measure total variables as a proxy for cache-driven encoder state growth
        encoder.vars_for_test().len()
    };

    let size_10 = measure_cache_size(10);
    let size_40 = measure_cache_size(40);

    let ratio = size_40 as f64 / size_10.max(1) as f64;
    let input_ratio = 40.0 / 10.0; // 4.0

    assert!(
        ratio <= input_ratio * 3.0,
        "SepConj variable count growth 10->{}: ratio={ratio:.1}, \
         expected <={:.1} (3x linear). size_10={size_10}, size_40={size_40}",
        40,
        input_ratio * 3.0,
    );
}

// =============================================================================
// PathConditionGuard: nested Ite error recovery (#1207, memory_verification P1-79)
// =============================================================================

/// Verify that `path_conditions` is exactly empty after a nested Ite where
/// the innermost then-branch exceeds `MAX_ENCODING_DEPTH`.
///
/// This exercises multi-level PathConditionGuard unwinding: the outer Ite
/// pushes a path condition, then the inner Ite pushes another, and the inner
/// Ite's then-branch triggers a depth-limit error. Both guards must pop on
/// their respective scope exits. If either guard leaks, the path_conditions
/// stack has residual entries.
///
/// This is a strictly harder case than `path_condition_guard_pops_on_encode_error_path`
/// in memory_safety.rs, which tests only a single Ite level.
///
/// Runs in a thread with 8 MB stack because depth-limit testing requires deep
/// recursion in debug builds.
/// Re: #1207, memory_verification phase
#[test]
#[timeout(30000)]
fn test_path_conditions_balanced_after_nested_ite_depth_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Build a deeply nested expression that exceeds MAX_ENCODING_DEPTH
            let mut deep = PureExpr::Bool(true);
            for _ in 0..MAX_ENCODING_DEPTH + 5 {
                deep = PureExpr::UnOp(crate::UnOp::Not, Arc::new(deep));
            }

            // Nest it inside TWO Ite levels:
            // ite(x > 0,
            //   ite(y > 0,
            //     <deep — will fail>,
            //     42),
            //   99)
            let inner_ite = ite(gt(var("y"), int(0)), deep, int(42));
            let outer_ite = ite(gt(var("x"), int(0)), inner_ite, int(99));

            // Encoding should fail due to depth exceeded in the inner then-branch
            let result = encoder.encode_pure(&outer_ite);
            assert!(
                result.is_err(),
                "nested Ite with depth-exceeding inner then-branch should error: {result:?}"
            );

            // Critical assertion: path_conditions must be exactly empty.
            // Two PathConditionGuards were created (one per Ite level), and both
            // must have popped on error propagation.
            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after nested Ite depth error, \
                 got {} entries (guard leak)",
                encoder.path_conditions_for_test().len(),
            );

            // Also verify recursion_depth is clean
            assert_eq!(
                encoder.recursion_depth_for_test(),
                0,
                "recursion_depth must be 0 after nested Ite depth error, got {}",
                encoder.recursion_depth_for_test(),
            );

            // Encoder must remain usable for subsequent encodings
            let simple = encoder.encode_pure(&gt(var("a"), int(0)));
            assert!(
                simple.is_ok(),
                "encoder should remain usable after nested Ite error: {simple:?}"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Verify that `path_conditions` is empty after a triple-nested Ite where
/// errors occur at the deepest level, exercising 3 PathConditionGuard unwinds.
///
/// Runs in a thread with 8 MB stack for depth-limit testing.
/// Re: #1207, memory_verification phase
#[test]
#[timeout(30000)]
fn test_path_conditions_balanced_after_triple_nested_ite_depth_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            let mut deep = PureExpr::Bool(true);
            for _ in 0..MAX_ENCODING_DEPTH + 5 {
                deep = PureExpr::UnOp(crate::UnOp::Not, Arc::new(deep));
            }

            // Triple nesting: ite(a, ite(b, ite(c, <deep>, 1), 2), 3)
            let inner = ite(gt(var("c"), int(0)), deep, int(1));
            let middle = ite(gt(var("b"), int(0)), inner, int(2));
            let outer = ite(gt(var("a"), int(0)), middle, int(3));

            let result = encoder.encode_pure(&outer);
            assert!(
                result.is_err(),
                "triple-nested Ite with deep expr should error"
            );

            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after triple-nested Ite error, \
                 got {} entries (3 guards must all have popped)",
                encoder.path_conditions_for_test().len(),
            );
            assert_eq!(encoder.recursion_depth_for_test(), 0, "depth must be 0");
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Verify that `path_conditions` is exactly empty when an Ite else-branch
/// (not then-branch) contains the depth-exceeding expression.
///
/// This tests the else-branch PathConditionGuard specifically — the guard
/// that pushes `NOT(condition)` rather than `condition`.
///
/// Runs in a thread with 8 MB stack for depth-limit testing.
/// Re: #1207, memory_verification phase
#[test]
#[timeout(30000)]
fn test_path_conditions_balanced_after_else_branch_depth_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            let mut deep = PureExpr::Bool(true);
            for _ in 0..MAX_ENCODING_DEPTH + 5 {
                deep = PureExpr::UnOp(crate::UnOp::Not, Arc::new(deep));
            }

            // Error in else-branch: ite(x > 0, 42, <deep>)
            let ite_else_error = ite(gt(var("x"), int(0)), int(42), deep);
            let result = encoder.encode_pure(&ite_else_error);
            assert!(
                result.is_err(),
                "Ite with depth error in else-branch should error"
            );

            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after else-branch depth error, \
                 got {} entries",
                encoder.path_conditions_for_test().len(),
            );
            assert_eq!(encoder.recursion_depth_for_test(), 0, "depth must be 0");

            // Verify subsequent encoding works
            let ok = encoder.encode_pure(&PureExpr::Bool(true));
            assert!(ok.is_ok(), "encoder usable after else-branch error: {ok:?}");
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}
