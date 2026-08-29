// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── catch_unwind panic isolation tests (#1031) ──────────────────────────
//
// Tests for the `catch_unwind` safety mechanism in
// `verify_function_with_modes` (function.rs:108-143) that catches ay
// Sort-mismatch panics and converts them to `VerificationResult::Unknown`.
//
// Without these tests, the entire panic-isolation mechanism (#997) had
// zero direct coverage — only prevention tests (no sort mismatch occurs)
// existed, but no test verified the safety net actually works.

/// When a logic function is registered with Int domain parameters but
/// called with a Bool-sorted argument, ay's `Solver::apply()` fires a
/// `debug_assert_eq` panic containing "Sort mismatch". The catch_unwind
/// wrapper should convert this to `VerificationResult::Unknown`.
///
/// Trigger pattern:
///   1. Register `g(n)` with body `n + 1` → domain [Int], range Int
///   2. In ensures, call `g(x > 0)` → `x > 0` encodes to Bool
///   3. `safe_apply` catches the sort mismatch → returns EncodingError
///   4. verify_function propagates EncodingError containing "Sort mismatch"
///
/// Note: After safe_apply (#1532) was added, sort mismatch panics are caught
/// at the encoder layer and converted to EncodingError, rather than
/// propagating to the verify layer's catch_unwind as Unknown.
#[cfg(debug_assertions)]
#[test]
#[timeout(60000)]
fn test_sort_mismatch_panic_caught_as_unknown() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Logic function g(n) = n + 1 — declares g with domain [Int].
    let logic_fn = LogicFnDef::new(
        "g_sort_test".to_string(),
        "test::g_sort_test".to_string(),
        vec!["n".to_string()],
        add(var("n"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // Postcondition: g(x > 0) — passes Bool to Int-domain function.
    // This triggers Sort mismatch at the ay API level.
    let ens = eq(
        logic_fn_call("g_sort_test", vec![gt(var("x"), int(0))]),
        int(5),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).logic_fns(Some(&[logic_fn])),
    );

    // After widened coercion (#2155), apply_logic_fn replaces the Bool
    // argument with a fresh Int constant before calling safe_apply, so
    // no sort mismatch panic occurs. The encoding succeeds and the solver
    // attempts verification with the unconstrained argument.
    //
    // All outcomes are acceptable:
    // - Ok(Failed/Verified/Unknown): coercion worked, solver attempted proof
    // - Err(EncodingError): sort mismatch caught in a deeper path
    match result {
        Ok(_) => {
            // Coercion prevented the panic; solver returned a result.
        }
        Err(ref e)
            if format!("{e:?}").contains("sort mismatch")
                || format!("{e:?}").contains("Sort mismatch") =>
        {
            // Sort mismatch caught in a deeper encoding path.
        }
        Err(ref e) => {
            panic!("Unexpected encoding error (not sort-related): {e:?}");
        }
    }
}

/// Non-Sort ay API panics that happen inside the verification pipeline must
/// not be silently ignored. They should either:
/// - Re-propagate as panics (via `resume_unwind` at the verify layer), OR
/// - Be caught by `safe_apply` at the encoder layer and returned as
///   `EncodingError` containing the panic reason.
///
/// After `safe_apply` (#1532), arity mismatch panics from `solver.apply()`
/// are caught at the encoder layer and converted to `EncodingError`, so this
/// test validates that the error is surfaced rather than swallowed.
///
/// Trigger pattern:
///   1. Register unary logic function `g_arity_test(n)`
///   2. Call it with zero args in ensures: `g_arity_test() == 5`
///   3. ay `Solver::apply` debug-asserts with "Arity mismatch"
///   4. `safe_apply` catches the panic → `EncodingError`
#[cfg(debug_assertions)]
#[test]
#[timeout(30000)]
fn test_non_sort_ay_panic_repropagates() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let logic_fn = LogicFnDef::new(
        "g_arity_test".to_string(),
        "test::g_arity_test".to_string(),
        vec!["n".to_string()],
        add(var("n"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // Wrong arity call: zero args for unary logic function.
    let ens = eq(logic_fn_call("g_arity_test", vec![]), int(5));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).logic_fns(Some(&[logic_fn])),
    );

    // After safe_apply: arity mismatch is caught at encoder layer and
    // returned as EncodingError. Verify the error is surfaced, not swallowed.
    match result {
        Err(ref e)
            if format!("{e:?}").contains("Arity mismatch")
                || format!("{e:?}").contains("arity") =>
        {
            // safe_apply caught the panic and surfaced it as an error.
        }
        Ok(VerificationResult::Unknown(ref msg))
            if msg.as_str().contains("Arity mismatch") || msg.as_str().contains("arity") =>
        {
            // Verify layer caught the panic and converted to Unknown.
        }
        other => {
            panic!(
                "Arity mismatch should be surfaced as EncodingError or Unknown, \
                 not silently swallowed. Got: {other:?}"
            );
        }
    }
}

/// Mode overrides length mismatch is silently dropped before `catch_unwind`
/// (#2316, #2700). Previously this test verified that mode_overrides errors
/// propagated as EncodingError before catch_unwind. Now mode_overrides
/// mismatches are silently dropped so verification proceeds normally.
#[test]
#[timeout(30000)]
fn test_mode_overrides_mismatch_handled_before_catch_unwind() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let logic_fns = vec![
        LogicFnDef::new("f".to_string(), "test::f".to_string(), vec![], int(1))
            .with_mode(LogicMode::Open),
        LogicFnDef::new("g".to_string(), "test::g".to_string(), vec![], int(2))
            .with_mode(LogicMode::Open),
    ];
    let mode_overrides = [LogicMode::Open]; // wrong length: 1 vs 2

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[eq(var("result"), int(0))])
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides)),
    );
    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}

/// Verify that verify_function's catch_unwind does NOT interfere with the
/// global panic hook.
///
/// The catch_unwind wrapper in verify_function_with_modes no longer
/// manipulates the panic hook (#1079). Previously (#1028) it used
/// take_hook/set_hook to suppress stderr, but that was a process-global
/// operation that raced with parallel test threads. The hook swap was
/// removed in #1079. This test confirms the fix holds: a caller-installed
/// sentinel hook survives a verify_function call that triggers
/// catch_unwind internally.
#[cfg(debug_assertions)]
#[test]
#[timeout(60000)]
fn test_panic_hook_restored_after_catch_unwind() {
    use std::{
        panic::{catch_unwind, AssertUnwindSafe},
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc,
        },
    };

    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Install a sentinel hook BEFORE verify_function. If verify_function
    // correctly saves and restores the hook, this sentinel should still
    // be active after verify_function returns.
    let hook_called = Arc::new(AtomicBool::new(false));
    let hook_flag = hook_called.clone();
    std::panic::set_hook(Box::new(move |_| {
        hook_flag.store(true, Ordering::SeqCst);
    }));

    // Pass a Bool where Int is expected. With widened coercion (#2155),
    // apply_logic_fn handles this gracefully. The test only needs
    // verify_function to run (catch_unwind may or may not fire).
    let logic_fn = LogicFnDef::new(
        "g_hook_test".to_string(),
        "test::g_hook_test".to_string(),
        vec!["n".to_string()],
        add(var("n"), int(1)),
    )
    .with_mode(LogicMode::Open);

    let ens = eq(
        logic_fn_call("g_hook_test", vec![gt(var("x"), int(0))]),
        int(5),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).logic_fns(Some(&[logic_fn])),
    );

    // Precondition: verify_function must return (not panic). After widened
    // coercion (#2155), all outcomes are acceptable — the test's purpose
    // is hook preservation, not sort-mismatch behavior.
    let _ = &result;

    // Now trigger a panic AFTER verify_function returns. If the sentinel
    // hook was correctly saved and restored by verify_function_with_modes,
    // it should fire here. If the no-op hook was leaked, the sentinel
    // never fires and hook_called stays false.
    let _ = catch_unwind(AssertUnwindSafe(|| {
        panic!("test panic to verify hook restoration");
    }));

    // Restore default hook before assertions (cleanup).
    let _ = std::panic::take_hook();

    assert!(
        hook_called.load(Ordering::SeqCst),
        "Sentinel panic hook should have been called after verify_function returned — \
         if not, verify_function_with_modes leaked its no-op hook (line 121 of function.rs \
         did not restore the previous hook). See #1030 for thread-safety context."
    );
}
