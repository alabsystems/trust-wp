// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::AssertionPipelineState;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AssertionPhase {
    Other,
    Precondition,
    NegatedPostcondition,
    AliasConstraint,
    EncodingAxiom,
    GroundInstance,
}

impl AssertionPhase {
    fn label_prefix(self) -> Option<&'static str> {
        match self {
            Self::Other => None,
            Self::Precondition => Some("__trust_wp_precondition"),
            Self::NegatedPostcondition => Some("__trust_wp_negated_goal"),
            Self::AliasConstraint => Some("__trust_wp_alias_constraint"),
            Self::EncodingAxiom => Some("__trust_wp_encoding_axiom"),
            Self::GroundInstance => Some("__trust_wp_ground_instance"),
        }
    }
}

impl AssertionPipelineState {
    /// The assertion family currently being emitted.
    pub(crate) fn current_phase(&self) -> AssertionPhase {
        self.current_phase
    }

    pub(crate) fn replace_phase(&mut self, phase: AssertionPhase) -> AssertionPhase {
        std::mem::replace(&mut self.current_phase, phase)
    }

    pub(crate) fn next_named_assertion_label(&mut self) -> Option<String> {
        if let Some(label) = self.next_assertion_label.take() {
            return Some(label);
        }

        let prefix = match self.current_phase {
            AssertionPhase::NegatedPostcondition => self
                .negated_goal_label
                .as_deref()
                .or_else(|| self.current_phase.label_prefix()),
            other => other.label_prefix(),
        }?;

        let next = self.named_assertion_counter;
        self.named_assertion_counter = self.named_assertion_counter.saturating_add(1);
        Some(format!("{prefix}_{next}"))
    }

    /// Set the negated-goal label prefix for the current obligation slice.
    pub(crate) fn set_negated_goal_label_prefix(&mut self, label: String) {
        self.negated_goal_label = Some(label);
    }

    /// Returns the negated-goal assertion label prefix, if one was recorded.
    pub(crate) fn negated_goal_label_prefix(&self) -> Option<&str> {
        self.negated_goal_label.as_deref()
    }

    /// Clear the negated-goal label (e.g., between obligation slices).
    pub(crate) fn clear_negated_goal_label(&mut self) {
        self.negated_goal_label = None;
    }
}

#[cfg(test)]
mod tests {
    use super::{super::AssertionPipelineState, AssertionPhase};

    // ── AssertionPhase::label_prefix ──

    #[test]
    fn test_assertion_phase_other_has_no_prefix() {
        assert!(AssertionPhase::Other.label_prefix().is_none());
    }

    #[test]
    fn test_assertion_phase_precondition_prefix() {
        assert_eq!(
            AssertionPhase::Precondition.label_prefix(),
            Some("__trust_wp_precondition")
        );
    }

    #[test]
    fn test_assertion_phase_negated_postcondition_prefix() {
        assert_eq!(
            AssertionPhase::NegatedPostcondition.label_prefix(),
            Some("__trust_wp_negated_goal")
        );
    }

    #[test]
    fn test_assertion_phase_alias_constraint_prefix() {
        assert_eq!(
            AssertionPhase::AliasConstraint.label_prefix(),
            Some("__trust_wp_alias_constraint")
        );
    }

    #[test]
    fn test_assertion_phase_encoding_axiom_prefix() {
        assert_eq!(
            AssertionPhase::EncodingAxiom.label_prefix(),
            Some("__trust_wp_encoding_axiom")
        );
    }

    #[test]
    fn test_assertion_phase_ground_instance_prefix() {
        assert_eq!(
            AssertionPhase::GroundInstance.label_prefix(),
            Some("__trust_wp_ground_instance")
        );
    }

    // ── replace_phase ──

    #[test]
    fn test_replace_phase_returns_old_phase() {
        let mut state = AssertionPipelineState::new();
        let old = state.replace_phase(AssertionPhase::Precondition);
        assert_eq!(old, AssertionPhase::Other);
    }

    #[test]
    fn test_replace_phase_sets_new_phase() {
        let mut state = AssertionPipelineState::new();
        state.replace_phase(AssertionPhase::EncodingAxiom);
        // Replacing again should return the one we just set
        let old = state.replace_phase(AssertionPhase::Other);
        assert_eq!(old, AssertionPhase::EncodingAxiom);
    }

    // ── next_named_assertion_label ──

    #[test]
    fn test_next_named_assertion_label_other_phase_returns_none() {
        let mut state = AssertionPipelineState::new();
        // Default phase is Other, which has no prefix
        assert!(state.next_named_assertion_label().is_none());
    }

    #[test]
    fn test_next_named_assertion_label_precondition_phase_increments() {
        let mut state = AssertionPipelineState::new();
        state.replace_phase(AssertionPhase::Precondition);

        let label0 = state.next_named_assertion_label().unwrap();
        assert_eq!(label0, "__trust_wp_precondition_0");

        let label1 = state.next_named_assertion_label().unwrap();
        assert_eq!(label1, "__trust_wp_precondition_1");
    }

    #[test]
    fn test_next_named_assertion_label_encoding_axiom_phase() {
        let mut state = AssertionPipelineState::new();
        state.replace_phase(AssertionPhase::EncodingAxiom);

        let label = state.next_named_assertion_label().unwrap();
        assert_eq!(label, "__trust_wp_encoding_axiom_0");
    }

    #[test]
    fn test_next_named_assertion_label_counter_persists_across_phases() {
        let mut state = AssertionPipelineState::new();

        // Generate labels in Precondition phase
        state.replace_phase(AssertionPhase::Precondition);
        let _ = state.next_named_assertion_label(); // _0
        let _ = state.next_named_assertion_label(); // _1

        // Switch to EncodingAxiom phase - counter continues from 2
        state.replace_phase(AssertionPhase::EncodingAxiom);
        let label = state.next_named_assertion_label().unwrap();
        assert_eq!(label, "__trust_wp_encoding_axiom_2");
    }

    #[test]
    fn test_next_named_assertion_label_negated_postcondition_uses_custom_label() {
        let mut state = AssertionPipelineState::new();
        state.replace_phase(AssertionPhase::NegatedPostcondition);

        // Without a custom negated-goal label, uses the default prefix
        let label = state.next_named_assertion_label().unwrap();
        assert_eq!(label, "__trust_wp_negated_goal_0");
    }

    #[test]
    fn test_next_named_assertion_label_negated_postcondition_custom_prefix() {
        let mut state = AssertionPipelineState::new();
        state.replace_phase(AssertionPhase::NegatedPostcondition);
        state.set_negated_goal_label_prefix("__custom_goal".to_string());

        let label = state.next_named_assertion_label().unwrap();
        assert_eq!(label, "__custom_goal_0");
    }

    // ── negated goal label management ──

    #[test]
    fn test_negated_goal_label_initially_none() {
        let state = AssertionPipelineState::new();
        assert!(state.negated_goal_label_prefix().is_none());
    }

    #[test]
    fn test_set_and_get_negated_goal_label() {
        let mut state = AssertionPipelineState::new();
        state.set_negated_goal_label_prefix("my_label".to_string());
        assert_eq!(state.negated_goal_label_prefix(), Some("my_label"));
    }

    #[test]
    fn test_clear_negated_goal_label() {
        let mut state = AssertionPipelineState::new();
        state.set_negated_goal_label_prefix("my_label".to_string());
        state.clear_negated_goal_label();
        assert!(state.negated_goal_label_prefix().is_none());
    }
}
