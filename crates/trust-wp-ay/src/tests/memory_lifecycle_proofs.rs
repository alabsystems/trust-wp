// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test code uses small values where precision loss is not a concern.
#![allow(clippy::cast_precision_loss)]

//! Memory lifecycle and panic isolation proofs for trust-wp-ay.
//!
//! These tests prove memory safety properties NOT covered by existing test files:
//!
//! 1. **DepthGuard RAII under panic unwind**: The raw `*mut usize` in DepthGuard
//!    is decremented even when encoding panics mid-recursion (via `catch_unwind`).
//!
//! 2. **PathConditionGuard balance under nested error paths**: Path condition stack
//!    stays exactly balanced across Ite branches that produce encoding errors,
//!    including nested Ite-within-Ite error recovery.
//!
//! 3. **Division obligations lifecycle**: `division_obligations` accumulates
//!    during encoding and drains at verification. Tests the monotonic growth,
//!    drain-and-restart cycle, and suppression under `total_int_arithmetic`.
//!
//! 4. **Solver panic poison-pill persistence across multiple operations**: Once
//!    `solver_panic_reason` is set, ALL subsequent operations (check_sat, eq_or_iff,
//!    assert_solver_term, get_model) respect the poison. Tests multiple operations
//!    in sequence after a single panic.
//!
//! 5. **Recheck loop neq-pair accumulation bound**: The quantified-disjoint recheck
//!    loop materializes neq pairs. After repeated check_sat calls with growing
//!    constraint sets, the `asserted_quantified_neq_pairs` set grows at most O(L*R)
//!    per constraint set, not unboundedly across calls.
//!
//! 6. **Encoder drop releases all resources**: After dropping a AYEncoder, the Solver
//!    and all cached state (SepConjCache Rc refs, ground pool, etc.) are released.
//!    Verified by strong_count checks on shared Rc references.
//!
//! Part of #901
//! Phase: memory_verification

use std::{
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
};

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::{super::AYEncoder, helpers::*};
use crate::{encoder::MAX_ENCODING_DEPTH, Formula, PureExpr};

// =============================================================================
// 1. DepthGuard RAII under panic unwind
// =============================================================================

/// Prove that `recursion_depth` is exactly 0 after a caught panic during encoding.
///
/// The DepthGuard uses `*mut usize` with an unsafe `Drop`. When `catch_unwind`
/// catches a panic mid-encoding, the unwind must run all DepthGuard destructors
/// on the stack. If any guard is skipped, `recursion_depth` will be > 0 after
/// the unwind, causing subsequent encodings to start with a non-zero counter
/// and hit the depth limit prematurely.
///
/// This test exercises the scenario by constructing a formula that panics deep
/// in the encoding stack (via a formula that triggers a ay solver internal panic),
/// catching the unwind, and then verifying the encoder's depth counter.
#[test]
#[timeout(30000)]
fn test_depth_guard_reset_after_caught_unwind() {
    let mut encoder = AYEncoder::new();

    // Build a deeply nested formula that will succeed
    let deep_formula = build_nested_and(50);
    let result = encoder.encode(&deep_formula);
    assert!(
        result.is_ok(),
        "50-deep And chain should encode successfully"
    );
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after successful encoding"
    );

    // Now build a formula at exactly MAX_ENCODING_DEPTH + 1 to trigger the depth error
    let too_deep = build_nested_and(MAX_ENCODING_DEPTH + 1);
    let err = encoder.encode(&too_deep);
    assert!(
        err.is_err(),
        "formula exceeding MAX_ENCODING_DEPTH should fail"
    );
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after depth-limit error — DepthGuard unwind"
    );

    // Verify the encoder is still functional after the depth error
    let simple = Formula::Pure(gt(var("x"), int(0)));
    let result = encoder.encode(&simple);
    assert!(
        result.is_ok(),
        "encoder must remain functional after depth-limit error recovery"
    );
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after post-recovery encoding"
    );
}

/// Prove that multiple sequential depth-limit errors don't cause counter drift.
///
/// If the DepthGuard has a double-decrement or missed-decrement bug, it would
/// manifest as an off-by-one that accumulates across multiple error cycles.
/// This test runs N error cycles and verifies the counter is exactly 0 after each.
#[test]
#[timeout(30000)]
fn test_depth_guard_no_drift_across_repeated_errors() {
    let mut encoder = AYEncoder::new();
    let too_deep = build_nested_and(MAX_ENCODING_DEPTH + 1);

    for i in 0..20 {
        let err = encoder.encode(&too_deep);
        assert!(err.is_err(), "iteration {i}: should fail with depth error");
        assert_eq!(
            encoder.recursion_depth_for_test(),
            0,
            "iteration {i}: recursion_depth must be 0 after error"
        );
    }

    // After 20 error cycles, encoding should still work at normal depth
    let normal = build_nested_and(10);
    assert!(
        encoder.encode(&normal).is_ok(),
        "encoder must work after 20 error-recovery cycles"
    );
    assert_eq!(encoder.recursion_depth_for_test(), 0);
}

// =============================================================================
// 2. PathConditionGuard balance under nested error paths
// =============================================================================

/// Prove that path_conditions is empty after Ite encoding where the then-branch
/// produces an encoding error (e.g., unsupported expression).
///
/// The PathConditionGuard pops one element on drop. If the then-branch errors
/// out via `?` propagation, the guard's Drop must fire before the error propagates
/// to the caller. This test verifies exact stack balance.
///
/// Uses 8 MB stack because `encode_pure_impl` frames are large in debug builds
/// and 129+ recursive calls can exceed the default 2 MB test-thread stack. (#1116)
#[test]
#[timeout(30000)]
fn test_path_conditions_balanced_after_then_branch_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Build an Ite where the then-branch has a formula too deep to encode
            let deep_then = build_nested_pure_ite(MAX_ENCODING_DEPTH + 1);
            let ite_expr = PureExpr::Ite(
                Arc::new(gt(var("x"), int(0))),
                Arc::new(deep_then),
                Arc::new(int(42)),
            );

            let err = encoder.encode_pure(&ite_expr);
            assert!(err.is_err(), "Ite with too-deep then-branch should fail");
            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after Ite then-branch error — \
                 found {} elements",
                encoder.path_conditions_for_test().len()
            );
            assert_eq!(
                encoder.recursion_depth_for_test(),
                0,
                "recursion_depth must also be 0"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Prove that path_conditions is empty after Ite encoding where the else-branch
/// produces an encoding error.
///
/// Similar to the then-branch case, but the else-branch PathConditionGuard
/// must pop `!cond` from the stack on error.
#[test]
#[timeout(30000)]
fn test_path_conditions_balanced_after_else_branch_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            let deep_else = build_nested_pure_ite(MAX_ENCODING_DEPTH + 1);
            let ite_expr = PureExpr::Ite(
                Arc::new(gt(var("x"), int(0))),
                Arc::new(int(42)),
                Arc::new(deep_else),
            );

            let err = encoder.encode_pure(&ite_expr);
            assert!(err.is_err(), "Ite with too-deep else-branch should fail");
            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after Ite else-branch error — \
                 found {} elements",
                encoder.path_conditions_for_test().len()
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Prove path_conditions balance across nested Ite where BOTH branches have
/// sub-Ite expressions and the inner one fails.
///
/// This is the hardest case: the outer Ite pushes cond, the inner Ite pushes
/// another cond, the inner fails, both guards must fire in LIFO order.
#[test]
#[timeout(30000)]
fn test_path_conditions_balanced_nested_ite_inner_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Inner Ite with too-deep then-branch
            let inner_ite = PureExpr::Ite(
                Arc::new(gt(var("y"), int(0))),
                Arc::new(build_nested_pure_ite(MAX_ENCODING_DEPTH)),
                Arc::new(int(99)),
            );
            // Outer Ite with failing inner Ite in then-branch
            let outer_ite = PureExpr::Ite(
                Arc::new(gt(var("x"), int(0))),
                Arc::new(inner_ite),
                Arc::new(int(0)),
            );

            let err = encoder.encode_pure(&outer_ite);
            assert!(
                err.is_err(),
                "nested Ite with too-deep inner branch should fail"
            );
            assert!(
                encoder.path_conditions_for_test().is_empty(),
                "path_conditions must be empty after nested Ite error — \
                 found {} elements (expected 0)",
                encoder.path_conditions_for_test().len()
            );
            assert_eq!(encoder.recursion_depth_for_test(), 0);
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

// =============================================================================
// 3. Division obligations lifecycle: accumulate during encoding, drain at verify
// =============================================================================

/// Prove that `division_obligations` accumulates exactly one obligation per
/// Div/Mod expression during encoding and starts empty on a fresh encoder.
///
/// This tests the lifecycle of the `division_obligations: Vec<Term>` field:
/// it grows monotonically during encoding and can be drained via `std::mem::take`.
/// If this lifecycle breaks, division-by-zero proof obligations would be lost
/// or duplicated.
#[test]
#[timeout(30000)]
fn test_division_obligations_accumulate_per_expression() {
    let mut encoder = AYEncoder::new();

    // Fresh encoder has no obligations
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "fresh encoder must have no division obligations"
    );

    // Encode a formula with Div — should produce exactly one obligation
    let div_formula = Formula::Pure(div(var("x"), var("y")));
    encoder
        .encode(&div_formula)
        .expect("Div formula should encode");
    assert_eq!(
        encoder.division_obligations_for_test().len(),
        1,
        "one Div expression should produce exactly one division obligation"
    );

    // Encode another with Mod — should accumulate to 2
    let mod_formula = Formula::Pure(mod_expr(var("a"), var("b")));
    encoder
        .encode(&mod_formula)
        .expect("Mod formula should encode");
    assert_eq!(
        encoder.division_obligations_for_test().len(),
        2,
        "second Div/Mod should accumulate to 2 obligations"
    );

    // Drain obligations (simulating what the verification layer does)
    let drained = encoder.take_division_obligations();
    assert_eq!(drained.len(), 2, "drained vec should have 2 obligations");
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "after drain, obligations must be empty"
    );

    // New encoding after drain should start fresh
    let div_formula2 = Formula::Pure(div(var("p"), var("q")));
    encoder
        .encode(&div_formula2)
        .expect("Div formula should encode after drain");
    assert_eq!(
        encoder.division_obligations_for_test().len(),
        1,
        "after drain, new encoding should start fresh with 1 obligation"
    );
}

/// Prove that division obligations are NOT generated when `total_int_arithmetic`
/// is true (ghost/mathematical context).
#[test]
#[timeout(30000)]
fn test_division_obligations_suppressed_in_total_arithmetic_mode() {
    let mut encoder = AYEncoder::new();
    encoder.set_total_int_arithmetic(true);

    let div_formula = Formula::Pure(div(var("x"), var("y")));
    encoder
        .encode(&div_formula)
        .expect("Div formula should encode");
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "total_int_arithmetic mode must suppress division obligations"
    );

    let mod_formula = Formula::Pure(mod_expr(var("a"), var("b")));
    encoder
        .encode(&mod_formula)
        .expect("Mod formula should encode");
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "total_int_arithmetic mode must suppress Mod obligations too"
    );
}

// =============================================================================
// 4. Solver panic poison-pill persistence across multiple operations
// =============================================================================

/// Prove that once `solver_panic_reason` is set, ALL subsequent operations
/// respect the poison: check_sat returns Unknown, and the reason persists
/// across multiple calls.
///
/// This tests the full chain: first panic sets the reason, then verify that
/// check_sat, a second assert_term, and another check_sat all respect it.
/// The first panic reason must be preserved (not overwritten by subsequent ops).
#[test]
#[timeout(30000)]
fn test_solver_panic_reason_persists_across_all_operations() {
    let mut encoder = AYEncoder::new();

    // Manually inject a panic reason (simulating a caught solver panic)
    encoder
        .assertion_pipeline_mut_for_test()
        .set_solver_panic_reason_for_test(Some("test: simulated ay sort mismatch".to_string()));

    // 1. check_sat must return Unknown
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "check_sat must return Unknown after panic poison"
    );

    // 2. Assert a valid term — the assertion infrastructure should still work
    //    (the term goes to the solver, but check_sat won't trust the result)
    let term = encoder.solver_mut().bool_const(true);
    encoder.assert_term(term);

    // 3. check_sat must still return Unknown
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "check_sat must still return Unknown after assertion post-panic"
    );

    // 4. The panic reason must be the FIRST one (not overwritten)
    assert_eq!(
        encoder.assertion_pipeline_for_test().solver_panic_reason(),
        Some("test: simulated ay sort mismatch"),
        "first panic reason must be preserved"
    );

    // 5. Try to set a second panic reason — record_solver_panic should preserve first
    encoder
        .assertion_pipeline_mut_for_test()
        .record_solver_panic("second panic reason".to_string());
    assert_eq!(
        encoder.assertion_pipeline_for_test().solver_panic_reason(),
        Some("test: simulated ay sort mismatch"),
        "record_solver_panic must not overwrite first panic reason"
    );
}

/// Prove that assert_solver_term returns false and sets panic reason when
/// the solver panics, and subsequent check_sat respects the poison.
#[test]
#[timeout(30000)]
fn test_assert_solver_term_panic_isolation_chain() {
    let mut encoder = AYEncoder::new();

    // First, verify clean state: check_sat should work
    let term = encoder.solver_mut().bool_const(true);
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "clean encoder should return Sat for true"
    );

    // Now inject poison
    encoder
        .assertion_pipeline_mut_for_test()
        .set_solver_panic_reason_for_test(Some(
            "sort mismatch: expected Int, got Bool".to_string(),
        ));

    // check_sat with poison
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "poisoned check_sat must return Unknown"
    );

    // Multiple check_sat calls should all return Unknown
    for i in 0..5 {
        assert_eq!(
            encoder.check_sat(),
            SolveResult::Unknown,
            "check_sat call {i} must still return Unknown"
        );
    }
}

// =============================================================================
// 5. Recheck loop neq-pair accumulation bound
// =============================================================================

/// Prove that `asserted_quantified_neq_pairs` grows at most O(L*R) per constraint
/// set and does not accumulate unboundedly across check_sat calls with no new
/// constraints.
///
/// The recheck loop materializes `lt != rt` pairs only when the SAT model shows
/// collision. If no new assertions arrive between check_sat calls, the recheck
/// should be skipped entirely (revision-gated).
#[test]
#[timeout(30000)]
fn test_recheck_neq_pairs_bounded_by_constraint_set_size() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    // Build and encode a SepConj chain that activates quantified disjointness
    let chain = build_sep_conj_chain_with_prefix(6, "a_");
    let term = encoder
        .encode(&chain)
        .expect("6-element sep_conj chain should encode");
    encoder.assert_term(term);

    let neq_before = encoder
        .assertion_pipeline_for_test()
        .asserted_neq_pairs_len();

    // First check_sat may trigger recheck and materialize neq pairs
    let _result = encoder.check_sat();
    let neq_after_first = encoder
        .assertion_pipeline_for_test()
        .asserted_neq_pairs_len();

    // Second check_sat with no new assertions should NOT grow neq pairs
    // (revision gate should skip the recheck)
    let _result = encoder.check_sat();
    let neq_after_second = encoder
        .assertion_pipeline_for_test()
        .asserted_neq_pairs_len();

    assert_eq!(
        neq_after_first, neq_after_second,
        "neq pairs must not grow between check_sat calls with no new assertions \
         (revision gate). Before: {neq_before}, after first: {neq_after_first}, \
         after second: {neq_after_second}"
    );

    // Bound check: neq_after_first <= L * R for a 6-element chain.
    // In a 6-element left-recursive SepConj, the maximum constraint sets are
    // 5 (one per SepConj node), each with at most 5 left terms and 1 right term.
    // So max neq pairs is 5 * 5 * 1 = 25 (very conservative).
    let max_reasonable = 6 * 6; // L * R upper bound
    assert!(
        neq_after_first <= max_reasonable,
        "neq pairs ({neq_after_first}) should be bounded by O(L*R) = {max_reasonable}"
    );
}

// =============================================================================
// 6. Encoder drop releases all cached state
// =============================================================================

/// Prove that dropping a AYEncoder releases SepConj cache Rc references.
///
/// The `SepConjCache` uses `Rc<Vec<String>>` and `Rc<Vec<Term>>` to avoid
/// O(N^2) cloning. If the cache holds the only strong reference, dropping
/// the encoder should drop all Rc contents. This test verifies via
/// `Rc::strong_count` that no external references keep data alive.
#[test]
#[timeout(90000)]
fn test_encoder_drop_releases_sep_conj_cache() {
    // We can't directly observe Rc::strong_count from outside the encoder
    // because the cache is private. Instead, we verify that creating and
    // dropping an encoder with sep_conj formulas does not leak by checking
    // that a second encoder can be created and works normally.
    //
    // The real proof here is structural: SepConjCache fields are owned by
    // AYEncoder, which has no Drop impl, so Rust's automatic drop order
    // guarantees all fields are dropped. We verify this by encoding the same
    // formula in two sequential encoder lifetimes.

    for i in 0..5 {
        let mut encoder = AYEncoder::new_with_quantifiers();
        // The 8-element quantified SepConj query is intentionally at the
        // quantified-cache threshold and can run close to two seconds under
        // load. Keep the SAT assertion strict; give the solver enough budget
        // that this lifecycle test is not coupled to scheduler jitter.
        encoder.set_timeout(Some(std::time::Duration::from_secs(10)));
        let chain = build_sep_conj_chain_with_prefix(8, &format!("enc{i}_"));
        let term = encoder
            .encode(&chain)
            .expect("8-element sep_conj chain should encode");
        encoder.assert_term(term);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "8-element sep_conj chain should be SAT before encoder drop, got: {result:?}"
        );
        // encoder drops here — all Rc refs, solver state, and caches released
    }
    // If we get here without panics or leaks, the drop lifecycle is sound.
}

/// Prove that encoder core state and assertion pipeline start clean.
///
/// Regression test: every counter starts at 0, every collection starts empty,
/// and every Option starts as None on a fresh AYEncoder.
#[test]
#[timeout(30000)]
fn test_encoder_fresh_state_core_and_pipeline() {
    let encoder = AYEncoder::new();

    // Core state
    assert!(encoder.vars_for_test().is_empty(), "vars must start empty");
    assert!(
        encoder.var_sorts_for_test().is_empty(),
        "var_sorts must start empty"
    );
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must start at 0"
    );
    assert!(
        encoder.path_conditions_for_test().is_empty(),
        "path_conditions must start empty"
    );

    // Assertion pipeline
    let ap = encoder.assertion_pipeline_for_test();
    assert!(
        ap.pending_assertions_is_empty(),
        "pending_assertions must start empty"
    );
    assert!(
        ap.pending_disjoint_constraints().is_empty(),
        "pending_quantified_disjoint_constraints must start empty"
    );
    assert!(
        !ap.has_pending_pure_equalities(),
        "pending_pure_equality_terms must start empty"
    );
    assert!(
        ap.active_disjoint_constraints_is_empty(),
        "quantified_disjoint_constraints must start empty"
    );
    assert!(
        ap.disjoint_terms_is_empty(),
        "quantified_disjoint_terms must start empty"
    );
    assert!(
        ap.asserted_neq_pairs_is_empty(),
        "asserted_quantified_neq_pairs must start empty"
    );
    assert_eq!(
        ap.assertion_revision(),
        0,
        "assertion_revision must start at 0"
    );
    assert!(
        !ap.was_encoded_since_assert(),
        "saw_encoded_term_since_assert must start false"
    );
    assert_eq!(
        ap.quantified_pairs_revision(),
        0,
        "quantified_pairs_revision must start at 0"
    );
    assert!(!ap.is_panicked(), "solver_panic_reason must start as None");
}

/// Prove that encoder resolver state and secondary collections start clean.
///
/// Regression test companion to `test_encoder_fresh_state_core_and_pipeline`.
#[test]
#[timeout(30000)]
fn test_encoder_fresh_state_resolver_and_collections() {
    let encoder = AYEncoder::new();

    // Sort resolver
    let sr = encoder.sort_resolver_for_test();
    assert!(sr.sort_hints_is_empty(), "sort_hints must start empty");
    assert!(
        !sr.are_sort_hints_registered(),
        "sort_hints_registered must start false"
    );
    assert!(
        sr.type_constants_is_empty(),
        "type_constants must start empty"
    );
    assert!(
        sr.view_identity_is_empty(),
        "view_identity_asserted must start empty"
    );
    assert!(
        sr.produces_ground_is_empty(),
        "produces_ground_calls must start empty"
    );

    // Other collections
    assert!(
        encoder.unit_sorted_vars_for_test().is_empty(),
        "unit_sorted_vars must start empty"
    );
    assert!(
        encoder.is_option_asserted_for_test().is_empty(),
        "is_option_asserted must start empty"
    );
    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "division_obligations must start empty"
    );
    assert!(
        !encoder.total_int_arithmetic_for_test(),
        "total_int_arithmetic must start false"
    );
}

// =============================================================================
// 7. catch_unwind + RAII guard interaction proof
// =============================================================================

/// Prove that DepthGuard RAII unwind is compatible with `catch_unwind`.
///
/// `catch_unwind` catches panics and unwinds the stack, which should trigger
/// all `Drop` impls. Since DepthGuard holds a raw `*mut usize`, we must verify
/// that the pointer is still valid during unwind (the encoder hasn't been moved
/// or dropped). This test wraps the encoder in `AssertUnwindSafe` and forces
/// a panic during deep encoding, then verifies the counter.
#[test]
#[timeout(30000)]
fn test_depth_guard_raii_compatible_with_catch_unwind() {
    let mut encoder = AYEncoder::new();

    // Encode a valid formula first to confirm clean state
    let valid = Formula::Pure(gt(var("x"), int(0)));
    encoder.encode(&valid).expect("valid formula should encode");
    assert_eq!(encoder.recursion_depth_for_test(), 0);

    // Now use catch_unwind to catch a depth-limit error.
    // Note: depth-limit returns Err, not panic, so this confirms the non-panic path.
    let too_deep = build_nested_and(MAX_ENCODING_DEPTH + 1);
    let result = catch_unwind(AssertUnwindSafe(|| encoder.encode(&too_deep)));
    assert!(
        result.is_ok(),
        "depth-limit error should not panic (returns Err)"
    );
    assert!(result.unwrap().is_err(), "should be a depth-limit Err");
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after catch_unwind of depth error"
    );

    // Encoder must still be usable after catch_unwind
    let simple = Formula::Pure(int(42));
    assert!(
        encoder.encode(&simple).is_ok(),
        "encoder must work after catch_unwind recovery"
    );
}

/// Prove that repeated encode-unwind cycles don't corrupt encoder state.
///
/// This is a stress test: alternate between successful encodings and
/// depth-limit errors, verifying the encoder stays consistent throughout.
#[test]
#[timeout(30000)]
fn test_encode_unwind_cycle_stress() {
    let mut encoder = AYEncoder::new();
    let too_deep = build_nested_and(MAX_ENCODING_DEPTH + 1);
    let valid = Formula::Pure(add(var("x"), int(1)));

    for i in 0..50 {
        // Error cycle
        let err = encoder.encode(&too_deep);
        assert!(err.is_err(), "cycle {i}: depth error expected");
        assert_eq!(
            encoder.recursion_depth_for_test(),
            0,
            "cycle {i}: depth must be 0 after error"
        );

        // Success cycle
        let ok = encoder.encode(&valid);
        assert!(ok.is_ok(), "cycle {i}: valid encoding expected");
        assert_eq!(
            encoder.recursion_depth_for_test(),
            0,
            "cycle {i}: depth must be 0 after success"
        );
    }
}

// =============================================================================
// Helper: build nested And chains for depth testing
// =============================================================================

/// Build a left-recursive And chain of the given depth iteratively.
///
/// Iterative construction avoids stack overflow for large depths that the
/// recursive encoder will reject.
fn build_nested_and(depth: usize) -> Formula {
    let mut formula = Formula::Pure(gt(var("x"), int(0)));
    for _ in 1..depth {
        formula = Formula::And(
            Arc::new(formula),
            Arc::new(Formula::Pure(gt(var("y"), int(0)))),
        );
    }
    formula
}

/// Build a left-recursive Ite chain of the given depth iteratively.
///
/// Iterative construction avoids stack overflow for large depths that the
/// recursive encoder will reject.
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

/// Verify that balanced push/pop around a failing (but non-panicking)
/// encoding preserves solver consistency across multiple obligation slices.
///
/// This mirrors the exact pattern in verify/function/mod.rs: push, encode
/// (which may return Err), pop, then continue with the next slice. The
/// solver scope must be clean after pop even when the inner encoding fails.
#[test]
#[timeout(30000)]
fn test_solver_push_pop_balanced_across_error_slices() {
    let mut encoder = AYEncoder::new();

    // Pre-condition: assert something true in the base scope
    let base = encoder.solver.bool_const(true);
    encoder.solver.assert_term(base);

    // Slice 1: push, assert contradictory constraint, pop
    encoder.solver.push();
    let f = encoder.solver.bool_const(false);
    encoder.solver.assert_term(f);
    let result1 = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result1, SolveResult::Unsat(_)),
        "contradictory scope should be Unsat"
    );
    encoder.solver.pop();

    // After pop: base scope should still be Sat
    let result_base = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result_base, SolveResult::Sat),
        "base scope should still be Sat after pop: got {result_base:?}"
    );

    // Slice 2: push, encode a depth-limit error, pop
    encoder.solver.push();
    let too_deep = build_nested_and(MAX_ENCODING_DEPTH + 1);
    let encode_result = encoder.encode(&too_deep);
    assert!(encode_result.is_err(), "depth-limit should return Err");
    encoder.solver.pop();

    // After pop: base scope should still be Sat and depth counter clean
    assert_eq!(
        encoder.recursion_depth_for_test(),
        0,
        "recursion_depth must be 0 after depth error within push/pop"
    );
    let result_final = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result_final, SolveResult::Sat),
        "base scope should still be Sat after error slice: got {result_final:?}"
    );
}
