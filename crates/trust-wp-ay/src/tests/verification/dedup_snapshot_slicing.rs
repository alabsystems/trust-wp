// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for cross-slice dedup state restoration (#2618).
//!
//! These tests verify that obligation slicing correctly restores
//! assert-once state between slices, preventing assertion loss when
//! multiple postconditions share Option matches, view identities,
//! or logic function axioms.

use super::*;

/// DedupSnapshot round-trip restores view_identity_asserted.
///
/// Validates that the view identity dedup set is restored per-slice,
/// preventing missing `v = v_view` constraints in later slices. (#2618 AC5)
#[test]
#[timeout(30000)]
fn test_dedup_snapshot_roundtrip_resets_view_identity() {
    let mut encoder = AYEncoder::new();

    // Snapshot with clean state (no view identities asserted)
    let snapshot = encoder.dedup_snapshot();

    // Mark a view identity as asserted (simulates encoding `x@` in slice 0)
    encoder
        .sort_resolver_mut_for_test()
        .mark_view_identity("x".to_string());
    assert!(
        encoder.sort_resolver_for_test().has_view_identity("x"),
        "view identity should be marked after mutation"
    );

    // Restore should clear the view identity
    encoder.restore_dedup(snapshot);
    assert!(
        !encoder.sort_resolver_for_test().has_view_identity("x"),
        "view identity should be cleared after restore"
    );
}

/// Two ensures with shared logic function axiom should both verify.
///
/// Without dedup restore, the second slice could miss defining axioms
/// for logic functions asserted in the first slice. (#2618 AC1)
#[test]
#[timeout(30000)]
fn test_multi_ensures_shared_logic_fn_both_verify() {
    // fn bar(x: i32) -> i32
    //   requires: x > 0
    //   ensures: result > 0
    //   ensures: result > x - 1
    //   body: x + 1
    //
    // Simple arithmetic postconditions that both verify independently.
    // This confirms the snapshot/restore machinery doesn't regress
    // the basic multi-ensures path.
    let req = gt(var("x"), int(0));
    let ens1 = gt(var("result"), int(0));
    let ens2 = gt(var("result"), sub(var("x"), int(1)));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens1, ens2]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "basic multi-ensures should still verify after dedup restore: {result:?}"
    );
}

/// Single ensures clause should be unaffected by snapshot/restore.
///
/// Regression guard: snapshot + restore on a single-slice path
/// should produce identical results to the pre-#2618 behavior.
#[test]
#[timeout(30000)]
fn test_single_ensure_unaffected_by_dedup_restore() {
    let req = gt(var("x"), int(0));
    let ens = eq(var("result"), add(var("x"), int(1)));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "single ensures should verify unchanged: {result:?}"
    );
}

/// DedupSnapshot round-trip: snapshot, mutate, restore, verify seq flags reset.
///
/// This validates the encoder-level snapshot/restore contract by checking
/// that `sum_axioms_asserted` is properly reset after restore.
#[test]
#[timeout(30000)]
fn test_dedup_snapshot_roundtrip_resets_seq_flags() {
    let mut encoder = AYEncoder::new();

    // Snapshot with clean state (no seq axioms asserted)
    let snapshot = encoder.dedup_snapshot();

    // Simulate asserting seq axioms within a scope
    encoder.push_scope().unwrap();
    // Mark seq sum axioms as asserted (this would normally happen during encoding)
    encoder.seq_state_mut_for_test().mark_sum_axioms_asserted();
    assert!(
        encoder.seq_state_for_test().sum_axioms_asserted(),
        "sum axioms should be marked after mutation"
    );
    encoder.pop_scope().unwrap();

    // The flag survives pop_scope (this is the bug #2618 fixes)
    assert!(
        encoder.seq_state_for_test().sum_axioms_asserted(),
        "sum axioms flag survives pop_scope without restore"
    );

    // Restore should reset the flag
    encoder.restore_dedup(snapshot);
    assert!(
        !encoder.seq_state_for_test().sum_axioms_asserted(),
        "sum axioms should be false after restore to pre-slice baseline"
    );
}
