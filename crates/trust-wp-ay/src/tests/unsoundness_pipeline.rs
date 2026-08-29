// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unsoundness demotion pipeline integration tests (#2106, #2202).
//!
//! Tests the thread-local counter isolation, demoting partition invariants,
//! and demotion behavior that is critical for test suite correctness.
//! These tests exercise the public API of `encoder::unsoundness` from
//! outside the module to verify cross-module behavior.

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::helpers::*;
use crate::{
    encoder::{
        closure_sorts::{closure_env_sort_name, StructuredSortContext},
        unsoundness::{self, UnsoundnessCategory},
        AYEncoder,
    },
    verify::{verify_function_with_modes, VerificationRequest, VerificationResult},
};

mod counter_regressions;

/// Verify the exact partition of demoting vs non-demoting categories.
/// This catches unintentional reclassifications — any change to the
/// demoting set must update this test explicitly. (#2202)
#[test]
#[timeout(30000)]
fn test_demoting_partition_exact_counts() {
    let demoting_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_demoting())
        .count();
    let non_demoting_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| !c.is_demoting())
        .count();

    // 8 demoting (5 HIGH + 3 MEDIUM), 12 non-demoting (10 LOW + 2 ELIMINATED)
    // Updated: SortFallbackToIntFromVar split as LOW (#2202),
    // InvariantTrueShortCircuit reclassified LOW (#2201),
    // SortFallbackToIntFromLogicFn reclassified MEDIUM after #2320,
    // BoolCoercionFromNonBool split out as LOW after #2359,
    // ClosureAxiomSkipped added as LOW (#2505),
    // ClosureBodyTrueDefault reclassified non-demoting (ELIMINATED #2541),
    // PhantomVariableUpgrade added as LOW (#2567),
    // IntegerCastIdentity added as HIGH (#938),
    // UnconstrainedResultVar split from SortFallbackToInt as MEDIUM (#2663),
    // BitwiseUfApproximation reclassified non-demoting (ELIMINATED #2666),
    // SortFallbackToIntFromCatchAll split from SortFallbackToInt as LOW (#2663 Phase 1a),
    // PremiseNeutralizedEq added as LOW with a dedicated Failed-arm demotion
    // (arc_and_rc sort-plan fix — non-demoting for Verified by design),
    // FinalCollapseRefused added as HIGH (Final-collapse audit Fix A:
    // fail-closed refusal of the sort-blind ^x -> x collapse),
    // OpaqueClosureValueFallback added as HIGH (vacfix: the opaque Bool
    // closure VALUE whose ite(b,1,0) promotion fabricates a {0,1} bound —
    // reclassified out of the LOW UnsupportedConstructSkip bucket, which is
    // why the non-demoting count is unchanged).
    assert_eq!(
        demoting_count, 10,
        "expected 10 demoting categories (7 HIGH + 3 MEDIUM), got {demoting_count}"
    );
    assert_eq!(
        non_demoting_count, 13,
        "expected 13 non-demoting categories (11 LOW + 2 ELIMINATED), got {non_demoting_count}"
    );
}

/// Verify thread-local isolation — increments in one thread do not
/// affect snapshots in another. This is critical for parallel test
/// correctness since `cargo test` runs tests on multiple threads.
#[test]
#[timeout(30000)]
fn test_thread_local_isolation() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let handle = std::thread::spawn(|| {
        // Increment in a different thread
        unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        let snap = unsoundness::snapshot();
        assert_eq!(
            snap.get(&UnsoundnessCategory::LetAssumeDropped),
            Some(&1),
            "child thread should see its own increment"
        );
    });
    handle.join().expect("child thread panicked");

    // Parent thread should not see child's increments
    let after = unsoundness::snapshot();
    let d = unsoundness::delta(&before, &after);
    assert!(
        d.is_empty(),
        "parent thread should not see child thread increments: {d:?}"
    );

    unsoundness::reset();
}

/// Verify that reset() only affects the calling thread.
#[test]
#[timeout(30000)]
fn test_reset_thread_local_only() {
    unsoundness::reset();
    unsoundness::increment(UnsoundnessCategory::BitwiseUfApproximation);

    let handle = std::thread::spawn(|| {
        unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);
        unsoundness::reset(); // reset child thread only
        assert!(
            unsoundness::snapshot().is_empty(),
            "child thread should be empty after reset"
        );
    });
    handle.join().expect("child thread panicked");

    // Parent thread's counter should be unaffected by child's reset
    let snap = unsoundness::snapshot();
    assert_eq!(
        snap.get(&UnsoundnessCategory::BitwiseUfApproximation),
        Some(&1),
        "parent thread counter should survive child's reset"
    );

    unsoundness::reset();
}

/// End-to-end: OpaqueCallTrueAssumption (HIGH, demoting) demotes Verified
/// when the driver provides a pre-MIR-extraction snapshot (#2206 AC3).
///
/// Simulates the production flow: driver takes snapshot → MIR extraction
/// increments OpaqueCallTrueAssumption → `verify_function_with_modes` uses
/// the driver's snapshot to compute the delta → demotion fires.
#[test]
#[timeout(30000)]
fn test_opaque_call_true_assumption_e2e_demotion() {
    // Run in a dedicated thread to isolate thread-local counters.
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction (counters are zero).
        let driver_snapshot = unsoundness::snapshot();

        // 2. MIR extraction encounters an opaque call — increment fires.
        unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

        // 3. Driver calls verify_function_with_modes with the pre-extraction snapshot.
        //    Contract: ensures(result == true), body: true. Trivially verifiable.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should be demoted from Verified to Unknown.
        match &result {
            VerificationResult::Unknown(reason) => {
                assert!(
                    reason.as_str().contains("demoted"),
                    "should be demoted due to OpaqueCallTrueAssumption: {reason}"
                );
                assert!(
                    reason.as_str().contains("opaque_call_true_assumption"),
                    "demotion reason should cite opaque_call_true_assumption: {reason}"
                );
            }
            other => panic!(
                "OpaqueCallTrueAssumption (HIGH risk) should demote Verified to Unknown: {other:?}"
            ),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: UnsupportedConstructSkip (LOW, non-demoting) does NOT demote
/// when the driver provides a pre-extraction snapshot (#2206 AC3).
///
/// Verifies that LOW-risk categories increment the counter but do not
/// trigger demotion through the full `verify_function_with_modes` pipeline.
#[test]
#[timeout(30000)]
fn test_unsupported_construct_skip_e2e_no_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Encoding encounters an unsupported construct — increment fires.
        unsoundness::increment(UnsoundnessCategory::UnsupportedConstructSkip);

        // 3. Verify with the driver's snapshot.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should remain Verified (LOW risk does not demote).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "UnsupportedConstructSkip (LOW risk) should NOT demote: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: `coerce_bool_operand` should not demote verification after the
/// #2359 split moved it onto `BoolCoercionFromNonBool` (LOW, non-demoting).
///
/// This locks the actual encoder path, not just the enum classification:
/// the driver snapshot is taken first, Bool coercion fires during encoding,
/// and the final verification result must remain `Verified`.
#[test]
#[timeout(30000)]
fn test_bool_coercion_e2e_no_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before any encoding-side coercion.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Trigger the actual #2359 path: Int -> Bool coercion via `!= 0`.
        let mut encoder = AYEncoder::new();
        let int_term = encoder.solver.declare_const("i", Sort::Int);
        let coerced = encoder.coerce_bool_operand(int_term);
        assert_eq!(
            encoder.solver.get_sort(coerced),
            Sort::Bool,
            "Int Bool-coercion should produce a Bool-sorted term"
        );

        // 3. Verify a trivially true function using the pre-coercion snapshot.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. The low-risk Bool coercion category must NOT demote.
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "BoolCoercionFromNonBool should remain non-demoting after #2359: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: Without driver snapshot, pre-extraction counter increments
/// are invisible to the demotion pipeline (regression test for the bug
/// that motivated the snapshot API, #2206).
///
/// This test documents the pre-fix behavior: without passing a snapshot,
/// `verify_function_with_modes` takes its own snapshot AFTER the counter
/// was incremented, making the delta 0. The test confirms that when no
/// snapshot is provided, demotion does NOT fire — demonstrating why the
/// driver MUST pass the snapshot for correct behavior.
#[test]
#[timeout(30000)]
fn test_no_driver_snapshot_misses_pre_extraction_increments() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Simulate driver incrementing OpaqueCallTrueAssumption during
        // MIR extraction, THEN calling verify_function_with_modes WITHOUT
        // passing a snapshot. The internal snapshot captures the existing
        // count, so the delta is 0 and demotion does not fire.
        unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures]).return_expr(Some(&bool_expr(true))),
            // Note: no unsoundness_snapshot — uses internal snapshot
        )
        .expect("verification should not error");

        // Without the driver snapshot, the pre-extraction increment is
        // invisible — result stays Verified (this is the bug behavior).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "without driver snapshot, pre-extraction increments should be invisible: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// resolve_var_sort_or_int unsoundness tracking gap tests (#2231)
//
// These tests document that `resolve_var_sort_or_int` does NOT increment the
// unsoundness counter when it falls back to Sort::Int. This is a known gap:
// FIXED(#2314): The Int fallback now increments `SortFallbackToIntFromVar`.
// ---------------------------------------------------------------------------

/// `resolve_var_sort_or_int` falls back to Sort::Int and correctly increments
/// `SortFallbackToIntFromVar` for observability. Fixed in #2314.
#[test]
#[timeout(30000)]
fn test_resolve_var_sort_or_int_int_fallback_tracking_gap() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        // Create a fresh encoder and resolve an unknown variable.
        // "completely_unknown_var_xyz" has no sort hints, no declared sort,
        // no suffix/prefix patterns — guaranteed to hit the Int fallback.
        let mut enc = AYEncoder::new();
        let sort = enc.resolve_var_sort_or_int("completely_unknown_var_xyz");
        assert_eq!(sort, Sort::Int, "unknown var should fall back to Int");

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert_eq!(
            d.get(&UnsoundnessCategory::SortFallbackToIntFromVar),
            Some(&1),
            "Int fallback in resolve_var_sort_or_int must increment SortFallbackToIntFromVar; delta: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Positive control: when a Bool sort IS resolved (via sort hint), no
/// unsoundness counter should fire — successful resolution is not unsound.
#[test]
#[timeout(30000)]
fn test_resolve_var_sort_or_int_found_sort_no_unsoundness() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut enc = AYEncoder::new();
        enc.sort_resolver_mut_for_test().record_sort_hint(
            "my_bool_var".to_string(),
            trust_wp_core::formula::ExprSort::Bool,
        );
        let sort = enc.resolve_var_sort_or_int("my_bool_var");
        assert_eq!(sort, Sort::Bool, "Bool hint should resolve to Sort::Bool");

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert!(
            d.is_empty(),
            "successful Bool resolution should not fire unsoundness counter: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Positive control: suffix-stripping chain resolution ("x_current" → "x")
/// that finds a non-Int sort should not fire unsoundness.
#[test]
#[timeout(30000)]
fn test_resolve_var_sort_or_int_chain_resolution_no_unsoundness() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut enc = AYEncoder::new();
        enc.sort_resolver_mut_for_test()
            .record_sort_hint("x".to_string(), trust_wp_core::formula::ExprSort::Bool);
        let sort = enc.resolve_var_sort_or_int("x_current");
        assert_eq!(
            sort,
            Sort::Bool,
            "x_current should resolve via x's Bool hint"
        );

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert!(
            d.is_empty(),
            "chain resolution to Bool should not fire unsoundness counter: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Defense gap validation: Bool-sorted variable falling back to Int sort
/// still escapes demotion. This is safe today because the shared equality
/// helper now relies on native Bool equality in the current ay pin, but
/// there is still no demotion safety net if that solver behavior regresses.
///
/// The double gap:
/// 1. `resolve_var_sort_or_int` returns `Sort::Int` for a Bool variable
///    → the compatibility wrapper receives a stale hint while still relying on
///      native solver equality
/// 2. `SortFallbackToIntFromVar` is LOW (non-demoting) → even if the
///    result is wrong, `demote_if_unsound` won't catch it
///
/// This test validates that the result IS currently correct (UNSAT),
/// confirming that the double gap is safe at the current ay revision.
/// If this test fails, ay-dpll #1179 has regressed and at least one of:
/// (a) `SortFallbackToIntFromVar` should be reclassified as HIGH, or
/// (b) the equality helper should stop trusting the solver for Bool equality.
///
/// Re: #2231 — sort mismatch comprehensive fix
/// Re: #2314 — resolve_var_sort_or_int silent Int fallback
#[test]
#[timeout(30000)]
fn test_double_defense_gap_bool_var_int_fallback_currently_safe() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Production scenario: a Bool-sorted variable declared directly in
        // the ay solver (bypassing encoder sort tracking) simulates the
        // case where resolve_var_sort_or_int misses the Bool sort.
        let mut encoder = AYEncoder::new();

        // Declare Bool-sorted variables directly in the solver, bypassing
        // encoder's get_or_declare_var (which would register the sort).
        // This simulates the gap where the encoder doesn't know the var
        // is Bool-sorted.
        let a = encoder.solver.declare_const("__gap_a", Sort::Bool);
        let b = encoder.solver.declare_const("__gap_b", Sort::Bool);

        // Confirm the gap: resolve returns Int because the encoder has no
        // sort information for these solver-declared variables.
        let resolved_sort = encoder.resolve_var_sort_or_int("__gap_a");
        assert_eq!(
            resolved_sort,
            Sort::Int,
            "precondition: sort resolution should fall back to Int without \
             encoder-tracked sort info"
        );

        // eq_or_iff with a stale Int hint should still reject Bool disagreement.
        let eq_term = encoder.eq_or_iff(a, b, &resolved_sort);
        encoder.solver.assert_term(eq_term);

        // Force a == true, b == false (contradicts equality).
        encoder.solver.assert_term(a);
        let not_b = encoder.solver.not(b);
        encoder.solver.assert_term(not_b);

        let result = encoder.check_sat();
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "CRITICAL: Bool equality with a stale Int hint must still be \
             UNSAT. Got {result:?}. If SAT, ay-dpll #1179 has regressed and the \
             defense gap is exploitable — Bool equality is undetected AND \
             non-demoted. Fix: either reclassify SortFallbackToIntFromVar as \
             HIGH, or stop relying on native Bool equality in this path."
        );

        // Document the non-demoting classification — demotion would NOT
        // catch a wrong result on this path.
        assert!(
            !UnsoundnessCategory::SortFallbackToIntFromVar.is_demoting(),
            "SortFallbackToIntFromVar is currently non-demoting — if the UNSAT \
             assertion above ever fails, this is the gap that lets it escape."
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Positive control: ExprSort annotation short-circuit to Bool should not
/// fire unsoundness — the annotation is authoritative.
#[test]
#[timeout(30000)]
fn test_resolve_var_sort_or_int_annotation_no_unsoundness() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut enc = AYEncoder::new();
        let sort =
            enc.resolve_var_sort_or_int_with_annotation("unknown_var", Some(&ExprSort::Bool));
        assert_eq!(
            sort,
            Sort::Bool,
            "Bool annotation should short-circuit to Sort::Bool"
        );

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert!(
            d.is_empty(),
            "annotation-resolved Bool should not fire unsoundness counter: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// restore / restore_category tests (#2002)
//
// These functions roll back false-positive unsoundness counter increments from
// analytical code paths. Zero test coverage before this block despite being
// used at 4 production callsites:
// - verify/function/result_binding.rs:98
// - verify/mut_borrow/mod.rs:111
// - encoder/sort_context/hint_collection.rs:41,210
// ---------------------------------------------------------------------------

/// `restore` rolls back all counters to a previous snapshot, undoing
/// increments that occurred after the snapshot was taken.
#[test]
#[timeout(30000)]
fn test_restore_rolls_back_all_counters() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Take a snapshot at a clean state.
        let snap = unsoundness::snapshot();

        // Increment several categories.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
        unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

        // Confirm increments happened.
        let after = unsoundness::snapshot();
        assert_eq!(after.get(&UnsoundnessCategory::SortFallbackToInt), Some(&2));
        assert_eq!(after.get(&UnsoundnessCategory::LetAssumeDropped), Some(&1));

        // Restore to the clean snapshot.
        unsoundness::restore(&snap);

        // All counters should be back to zero (empty snapshot).
        let restored = unsoundness::snapshot();
        let d = unsoundness::delta(&snap, &restored);
        assert!(
            d.is_empty(),
            "restore should roll back all increments: delta={d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `restore` preserves counters that were already present in the snapshot.
#[test]
#[timeout(30000)]
fn test_restore_preserves_snapshot_counters() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Build a non-empty baseline.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        unsoundness::increment(UnsoundnessCategory::BitwiseUfApproximation);
        let baseline = unsoundness::snapshot();

        // Add more increments after the baseline.
        unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

        // Restore to the baseline.
        unsoundness::restore(&baseline);

        // Baseline counters should be preserved exactly.
        let after = unsoundness::snapshot();
        assert_eq!(
            after.get(&UnsoundnessCategory::SortFallbackToInt),
            Some(&1),
            "baseline SortFallbackToInt count should be preserved"
        );
        assert_eq!(
            after.get(&UnsoundnessCategory::BitwiseUfApproximation),
            Some(&1),
            "baseline BitwiseUfApproximation count should be preserved"
        );
        // The post-baseline increment should be rolled back.
        assert_eq!(
            after.get(&UnsoundnessCategory::LetAssumeDropped),
            None,
            "post-baseline LetAssumeDropped should be rolled back"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `restore` is idempotent — calling it twice with the same snapshot
/// produces the same result.
#[test]
#[timeout(30000)]
fn test_restore_idempotent() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);
        let snap = unsoundness::snapshot();

        // Mutate beyond the snapshot.
        unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);

        // Restore twice.
        unsoundness::restore(&snap);
        let first_restore = unsoundness::snapshot();
        unsoundness::restore(&snap);
        let second_restore = unsoundness::snapshot();

        assert_eq!(
            first_restore, second_restore,
            "restore should be idempotent"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `restore_category` restores only the specified category, leaving others
/// at their current values.
#[test]
#[timeout(30000)]
fn test_restore_category_restores_only_target() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Baseline: SortFallbackToInt=1.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        let snap = unsoundness::snapshot();

        // After baseline: increment both SortFallbackToInt and LetAssumeDropped.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);

        // Restore only SortFallbackToInt to its baseline value (1).
        unsoundness::restore_category(&snap, UnsoundnessCategory::SortFallbackToInt);

        let after = unsoundness::snapshot();
        assert_eq!(
            after.get(&UnsoundnessCategory::SortFallbackToInt),
            Some(&1),
            "SortFallbackToInt should be restored to baseline value 1"
        );
        assert_eq!(
            after.get(&UnsoundnessCategory::LetAssumeDropped),
            Some(&1),
            "LetAssumeDropped should be UNTOUCHED by restore_category"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `restore_category` removes the category when it was absent from the
/// snapshot (exercises the `else` branch: `counters.remove(&category)`).
#[test]
#[timeout(30000)]
fn test_restore_category_removes_when_absent_from_snapshot() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Baseline: empty (no increments).
        let snap = unsoundness::snapshot();

        // After baseline: add an increment.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

        // Confirm it's there.
        let mid = unsoundness::snapshot();
        assert_eq!(
            mid.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
            Some(&1)
        );

        // Restore the category to its baseline value (absent → remove).
        unsoundness::restore_category(&snap, UnsoundnessCategory::SortFallbackToIntFromLogicFn);

        let after = unsoundness::snapshot();
        assert_eq!(
            after.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
            None,
            "restore_category should remove category absent from snapshot"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `restore_category` does not affect the demotion pipeline when used
/// correctly to roll back analytical false positives.
///
/// Simulates the production pattern from `result_binding.rs:98`:
/// take snapshot → analytical code increments a demoting category →
/// restore snapshot → verify → demotion should NOT fire.
#[test]
#[timeout(30000)]
fn test_restore_prevents_false_demotion_e2e() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes pre-extraction snapshot.
        let driver_snap = unsoundness::snapshot();

        // 2. Analytical code path (e.g., result_is_bool_by_postcondition)
        //    triggers a false-positive SortFallbackToInt increment.
        let analytical_snap = unsoundness::snapshot();
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

        // 3. Production code restores to the pre-analytical snapshot.
        unsoundness::restore(&analytical_snap);

        // 4. Verify — the false-positive should be invisible to demotion.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snap)),
        )
        .expect("verification should not error");

        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "restore should prevent false demotion from analytical code path: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// apply_delta tests (#2002)
//
// Merges counter increments from another thread (e.g., hard-timeout worker).
// Zero test coverage before this block despite being used in the production
// hard_timeout path (verify/hard_timeout.rs:153).
// ---------------------------------------------------------------------------

/// `apply_delta` merges positive counts from a delta into the current thread.
#[test]
#[timeout(30000)]
fn test_apply_delta_merges_counts() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Start with one existing increment.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

        // Build a delta as if from a worker thread.
        let mut worker_delta = std::collections::HashMap::new();
        worker_delta.insert(UnsoundnessCategory::SortFallbackToInt, 2_usize);
        worker_delta.insert(UnsoundnessCategory::LetAssumeDropped, 3_usize);

        unsoundness::apply_delta(&worker_delta);

        let snap = unsoundness::snapshot();
        assert_eq!(
            snap.get(&UnsoundnessCategory::SortFallbackToInt),
            Some(&3),
            "apply_delta should add to existing count: 1 + 2 = 3"
        );
        assert_eq!(
            snap.get(&UnsoundnessCategory::LetAssumeDropped),
            Some(&3),
            "apply_delta should create new entry from delta"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `apply_delta` ignores zero counts in the delta.
#[test]
#[timeout(30000)]
fn test_apply_delta_ignores_zero_counts() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        let mut worker_delta = std::collections::HashMap::new();
        worker_delta.insert(UnsoundnessCategory::PanicRecoveryFalse, 0_usize);

        unsoundness::apply_delta(&worker_delta);

        let snap = unsoundness::snapshot();
        assert_eq!(
            snap.get(&UnsoundnessCategory::PanicRecoveryFalse),
            None,
            "apply_delta should skip zero-count entries"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `apply_delta` with an empty delta is a no-op.
#[test]
#[timeout(30000)]
fn test_apply_delta_empty_noop() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        unsoundness::increment(UnsoundnessCategory::BitwiseUfApproximation);

        let before = unsoundness::snapshot();
        unsoundness::apply_delta(&std::collections::HashMap::new());
        let after = unsoundness::snapshot();

        assert_eq!(
            before, after,
            "apply_delta with empty delta should be a no-op"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// IntegerCastIdentity unsoundness demonstration (#938)
//
// Integer casts (IntToInt) are treated as identity in the SMT encoding:
// `x as u8` encodes as just `x`, ignoring truncation/wrapping. This section
// demonstrates the unsoundness and verifies demotion behavior.
// ---------------------------------------------------------------------------
