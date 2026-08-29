// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::AssertionPipelineState;

impl AssertionPipelineState {
    /// Record a solver panic reason (first-write-wins).
    ///
    /// Once set, `check_sat()` returns `Unknown` to prevent unsound results
    /// from a corrupted solver state. Only the first panic reason is stored;
    /// subsequent calls are no-ops.
    pub(crate) fn record_solver_panic(&mut self, reason: String) {
        self.solver_panic_reason.get_or_insert(reason);
    }

    /// Record a solver panic with a lazily-computed reason (first-write-wins).
    pub(crate) fn record_solver_panic_with(&mut self, reason_fn: impl FnOnce() -> String) {
        self.solver_panic_reason.get_or_insert_with(reason_fn);
    }

    /// Check if any solver panic has been recorded.
    pub(crate) fn is_panicked(&self) -> bool {
        self.solver_panic_reason.is_some()
    }

    /// Returns the first solver panic reason, if any.
    pub(crate) fn solver_panic_reason(&self) -> Option<&str> {
        self.solver_panic_reason.as_deref()
    }

    /// Mark that an encoded term was produced since the last `assert_term`.
    pub(crate) fn mark_encoded(&mut self) {
        self.saw_encoded_term_since_assert = true;
    }

    /// Clear the encoded-term flag (called during `assert_term` flush).
    pub(crate) fn clear_encoded_mark(&mut self) {
        self.saw_encoded_term_since_assert = false;
    }

    /// Check if an encoded term was produced since the last `assert_term`.
    pub(crate) fn was_encoded_since_assert(&self) -> bool {
        self.saw_encoded_term_since_assert
    }
}

#[cfg(test)]
mod tests {
    use super::super::AssertionPipelineState;

    // ── solver panic tracking (first-write-wins) ──

    #[test]
    fn test_record_solver_panic_stores_first_reason() {
        let mut state = AssertionPipelineState::new();
        assert!(!state.is_panicked());
        assert!(state.solver_panic_reason().is_none());

        state.record_solver_panic("first panic".to_string());
        assert!(state.is_panicked());
        assert_eq!(state.solver_panic_reason(), Some("first panic"));
    }

    #[test]
    fn test_record_solver_panic_ignores_subsequent_calls() {
        let mut state = AssertionPipelineState::new();
        state.record_solver_panic("first".to_string());
        state.record_solver_panic("second".to_string());
        // First-write-wins: "second" is discarded
        assert_eq!(state.solver_panic_reason(), Some("first"));
    }

    #[test]
    fn test_record_solver_panic_with_lazy_evaluation() {
        let mut state = AssertionPipelineState::new();
        state.record_solver_panic_with(|| format!("lazy {}", "reason"));
        assert_eq!(state.solver_panic_reason(), Some("lazy reason"));
    }

    #[test]
    fn test_record_solver_panic_with_does_not_evaluate_if_already_set() {
        let mut state = AssertionPipelineState::new();
        state.record_solver_panic("already set".to_string());

        // The closure should not be called since a panic reason is already set
        state.record_solver_panic_with(|| panic!("should not be called"));
        assert_eq!(state.solver_panic_reason(), Some("already set"));
    }

    // ── encoded term tracking ──

    #[test]
    fn test_encoded_mark_initially_false() {
        let state = AssertionPipelineState::new();
        assert!(!state.was_encoded_since_assert());
    }

    #[test]
    fn test_mark_encoded_sets_flag() {
        let mut state = AssertionPipelineState::new();
        state.mark_encoded();
        assert!(state.was_encoded_since_assert());
    }

    #[test]
    fn test_clear_encoded_mark_resets_flag() {
        let mut state = AssertionPipelineState::new();
        state.mark_encoded();
        assert!(state.was_encoded_since_assert());

        state.clear_encoded_mark();
        assert!(!state.was_encoded_since_assert());
    }

    #[test]
    fn test_encoded_mark_cycle() {
        let mut state = AssertionPipelineState::new();
        // Simulate encode -> assert -> encode -> assert cycle
        state.mark_encoded();
        assert!(state.was_encoded_since_assert());
        state.clear_encoded_mark();
        assert!(!state.was_encoded_since_assert());
        state.mark_encoded();
        assert!(state.was_encoded_since_assert());
    }
}
