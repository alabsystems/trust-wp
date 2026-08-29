// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_test_only_revision_setters() {
    let mut state = AssertionPipelineState::new();

    state.set_assertion_revision_for_test(42);
    assert_eq!(state.assertion_revision(), 42);

    state.set_quantified_pairs_revision_for_test(41);
    assert_eq!(state.quantified_pairs_revision(), 41);
    assert!(state.needs_disjoint_recheck());

    state.set_quantified_pairs_revision_for_test(42);
    assert!(!state.needs_disjoint_recheck());
}

#[test]
#[timeout(30000)]
fn test_prime_recheck_for_test_forces_recheck() {
    let mut state = AssertionPipelineState::new();

    state.prime_recheck_for_test();
    assert_eq!(state.assertion_revision(), 1);
    assert_eq!(state.quantified_pairs_revision(), 0);
    assert!(
        state.needs_disjoint_recheck(),
        "prime_recheck should create the gap that triggers recheck"
    );
}

#[test]
#[timeout(30000)]
fn test_set_solver_panic_reason_for_test() {
    let mut state = AssertionPipelineState::new();

    state.set_solver_panic_reason_for_test(Some("test panic".to_string()));
    assert!(state.is_panicked());
    assert_eq!(state.solver_panic_reason(), Some("test panic"));

    state.set_solver_panic_reason_for_test(None);
    assert!(!state.is_panicked());
    assert_eq!(state.solver_panic_reason(), None);
}
