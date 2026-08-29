// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// First-write-wins: only the first panic reason is stored.
#[test]
#[timeout(30000)]
fn test_solver_panic_first_write_wins() {
    let mut state = AssertionPipelineState::new();

    assert!(!state.is_panicked(), "fresh state should not be panicked");
    assert_eq!(state.solver_panic_reason(), None);

    state.record_solver_panic("first panic".to_string());
    assert!(state.is_panicked());
    assert_eq!(state.solver_panic_reason(), Some("first panic"));

    state.record_solver_panic("second panic".to_string());
    assert_eq!(
        state.solver_panic_reason(),
        Some("first panic"),
        "first-write-wins: second panic reason must be discarded"
    );
}

/// `record_solver_panic_with` also respects first-write-wins and uses lazy evaluation.
#[test]
#[timeout(30000)]
fn test_solver_panic_with_lazy_first_write_wins() {
    let mut state = AssertionPipelineState::new();

    state.record_solver_panic_with(|| "lazy first".to_string());
    assert_eq!(state.solver_panic_reason(), Some("lazy first"));

    state.record_solver_panic_with(|| panic!("closure should not be called"));
    assert_eq!(
        state.solver_panic_reason(),
        Some("lazy first"),
        "lazy variant must also respect first-write-wins"
    );
}

/// Mixed eager/lazy recording respects first-write-wins.
#[test]
#[timeout(30000)]
fn test_solver_panic_eager_then_lazy() {
    let mut state = AssertionPipelineState::new();

    state.record_solver_panic("eager".to_string());
    state.record_solver_panic_with(|| panic!("should not be called after eager write"));
    assert_eq!(state.solver_panic_reason(), Some("eager"));
}

#[test]
#[timeout(30000)]
fn test_encoded_mark_toggle() {
    let mut state = AssertionPipelineState::new();

    assert!(
        !state.was_encoded_since_assert(),
        "fresh state should have no encoded mark"
    );

    state.mark_encoded();
    assert!(state.was_encoded_since_assert());

    state.clear_encoded_mark();
    assert!(
        !state.was_encoded_since_assert(),
        "clearing should reset the mark"
    );

    state.mark_encoded();
    state.mark_encoded();
    assert!(state.was_encoded_since_assert());
    state.clear_encoded_mark();
    assert!(!state.was_encoded_since_assert());
}
