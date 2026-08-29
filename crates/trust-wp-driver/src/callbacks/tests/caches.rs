// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Note: MIR_BODIES cannot be tested directly because populating it requires
// running rustc's mir_borrowck query. We verify EXTERN_SPECS behavior and
// trust that the same clear() logic works for MIR_BODIES.

#[test]
fn test_clear_caches_clears_extern_specs() {
    // Clear first to ensure test isolation (other tests may have modified state)
    clear_caches();

    // Insert a dummy entry
    EXTERN_SPECS.with(|state| {
        state.borrow_mut().insert(
            "test::path".to_string(),
            trust_wp_driver::StdSpec {
                requires: vec!["true".to_string()],
                ensures: vec![],
                param_names: None,
            },
        );
    });

    // Verify it's there
    let count_before = EXTERN_SPECS.with(|state| state.borrow().len());
    assert_eq!(count_before, 1);

    // Clear and verify empty
    clear_caches();

    let count_after = EXTERN_SPECS.with(|state| state.borrow().len());
    assert_eq!(count_after, 0);
}

#[test]
fn test_clear_caches_is_idempotent() {
    // Clear multiple times should be fine
    clear_caches();
    clear_caches();
    clear_caches();

    // Both caches should be empty
    let mir_count = MIR_BODIES.with(|state| state.borrow().len());
    let spec_count = EXTERN_SPECS.with(|state| state.borrow().len());
    assert_eq!(mir_count, 0);
    assert_eq!(spec_count, 0);
}

#[test]
fn test_clear_caches_clears_qualified_assoc_const_definitions() {
    clear_caches();
    record_qualified_assoc_const_definition("<I3<T> as Nat>::VALUE".to_string(), PureExpr::Int(4));

    let before = take_qualified_assoc_const_definitions();
    assert_eq!(
        before.len(),
        1,
        "test setup should populate the side channel"
    );

    record_qualified_assoc_const_definition("<I3<T> as Nat>::VALUE".to_string(), PureExpr::Int(4));
    clear_caches();

    let after = take_qualified_assoc_const_definitions();
    assert!(
        after.is_empty(),
        "clear_caches should remove extraction-scoped assoc const definitions"
    );
    clear_qualified_assoc_const_definitions();
}

// =========================================================================
// CacheGuard lifecycle tests (#1025)
// =========================================================================

#[test]
fn test_cache_guard_clears_on_construction() {
    // Simulate stale data from a prior session that exited abnormally
    EXTERN_SPECS.with(|state| {
        state.borrow_mut().insert(
            "stale::entry".to_string(),
            trust_wp_driver::StdSpec {
                requires: vec!["false".to_string()],
                ensures: vec![],
                param_names: None,
            },
        );
    });

    // Guard construction should clear stale data
    let _guard = CacheGuard::new();

    let spec_count = EXTERN_SPECS.with(|state| state.borrow().len());
    assert_eq!(
        spec_count, 0,
        "stale EXTERN_SPECS should be cleared on guard entry"
    );
}

#[test]
fn test_cache_guard_clears_on_drop() {
    {
        let _guard = CacheGuard::new();

        // Simulate data accumulated during a session
        EXTERN_SPECS.with(|state| {
            state.borrow_mut().insert(
                "session::data".to_string(),
                trust_wp_driver::StdSpec {
                    requires: vec![],
                    ensures: vec!["result > 0".to_string()],
                    param_names: None,
                },
            );
        });

        // Data is present during session
        let spec_count = EXTERN_SPECS.with(|state| state.borrow().len());
        assert_eq!(spec_count, 1, "session data should be present before drop");
    }
    // _guard dropped here

    // Verify cleanup happened
    let spec_count = EXTERN_SPECS.with(|state| state.borrow().len());
    assert_eq!(
        spec_count, 0,
        "EXTERN_SPECS should be cleared after guard drop"
    );
}

#[test]
fn test_cache_guard_clears_on_panic_unwind() {
    // Simulate: previous session panicked, leaving stale data
    EXTERN_SPECS.with(|state| {
        state.borrow_mut().insert(
            "leaked::from_panic".to_string(),
            trust_wp_driver::StdSpec {
                requires: vec![],
                ensures: vec![],
                param_names: None,
            },
        );
    });

    // Catch a panic inside a guarded scope
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = CacheGuard::new();

        // Guard construction already cleared the stale data;
        // now add new session data
        EXTERN_SPECS.with(|state| {
            state.borrow_mut().insert(
                "new::session".to_string(),
                trust_wp_driver::StdSpec {
                    requires: vec![],
                    ensures: vec![],
                    param_names: None,
                },
            );
        });
        UNEVAL_CONST_EXPANSION_DEPTH.with(|depth| depth.set(3));

        // Panic simulates abort_if_errors() or any unexpected failure
        panic!("simulated compilation abort");
    }));

    assert!(result.is_err(), "should have caught a panic");

    // After unwind, guard's Drop should have cleared everything
    let spec_count = EXTERN_SPECS.with(|state| state.borrow().len());
    let depth = UNEVAL_CONST_EXPANSION_DEPTH.with(|state| state.get());
    assert_eq!(
        spec_count, 0,
        "CacheGuard must clear caches on panic unwind (#1025)"
    );
    assert_eq!(
        depth, 0,
        "CacheGuard must reset UNEVAL_CONST_EXPANSION_DEPTH on panic unwind (#1712)"
    );
}
