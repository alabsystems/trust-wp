// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_next_named_assertion_label_scopes_prefixes_and_counter() {
    let mut state = AssertionPipelineState::new();

    assert_eq!(
        state.next_named_assertion_label(),
        None,
        "Other-phase assertions should stay unnamed"
    );

    let previous = state.replace_phase(AssertionPhase::Precondition);
    assert_eq!(previous, AssertionPhase::Other);
    assert_eq!(
        state.next_named_assertion_label().as_deref(),
        Some("__trust_wp_precondition_0"),
        "precondition phase should use the precondition prefix"
    );

    let nested_previous = state.replace_phase(AssertionPhase::AliasConstraint);
    assert_eq!(nested_previous, AssertionPhase::Precondition);
    assert_eq!(
        state.next_named_assertion_label().as_deref(),
        Some("__trust_wp_alias_constraint_1"),
        "nested phase should switch prefixes but keep the global counter monotonic"
    );

    assert_eq!(
        state.replace_phase(nested_previous),
        AssertionPhase::AliasConstraint
    );
    assert_eq!(
        state.next_named_assertion_label().as_deref(),
        Some("__trust_wp_precondition_2"),
        "restoring the previous phase should restore its prefix without resetting the counter"
    );

    assert_eq!(state.replace_phase(previous), AssertionPhase::Precondition);
    assert_eq!(
        state.next_named_assertion_label(),
        None,
        "restoring Other should suppress named labels again"
    );
}

#[test]
#[timeout(30000)]
fn test_negated_goal_label_prefix_overrides_default_then_clears() {
    let mut state = AssertionPipelineState::new();
    state.replace_phase(AssertionPhase::NegatedPostcondition);

    assert_eq!(
        state.next_named_assertion_label().as_deref(),
        Some("__trust_wp_negated_goal_0"),
        "negated goals without a slice label should use the default goal prefix"
    );

    state.set_negated_goal_label_prefix("__trust_wp_negated_goal_slice_7".to_string());
    assert_eq!(
        state.negated_goal_label_prefix(),
        Some("__trust_wp_negated_goal_slice_7")
    );
    assert_eq!(
        state.next_named_assertion_label().as_deref(),
        Some("__trust_wp_negated_goal_slice_7_1"),
        "recorded slice labels should override the default negated-goal prefix"
    );

    state.clear_negated_goal_label();
    assert_eq!(state.negated_goal_label_prefix(), None);
    assert_eq!(
        state.next_named_assertion_label().as_deref(),
        Some("__trust_wp_negated_goal_2"),
        "clearing the slice label should fall back to the default negated-goal prefix"
    );
}

#[test]
#[timeout(30000)]
fn test_with_negated_goal_label_prefix_restores_nested_prefixes() {
    let mut encoder = AYEncoder::new();

    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .negated_goal_label_prefix(),
        None
    );

    encoder.with_negated_goal_label_prefix("outer_goal".to_string(), |encoder| {
        assert_eq!(
            encoder
                .assertion_pipeline_for_test()
                .negated_goal_label_prefix(),
            Some("outer_goal")
        );

        let outer_label =
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |enc| {
                enc.assertion_pipeline_mut_for_test()
                    .next_named_assertion_label()
            });
        assert_eq!(outer_label.as_deref(), Some("outer_goal_0"));

        encoder.with_negated_goal_label_prefix("inner_goal".to_string(), |encoder| {
            assert_eq!(
                encoder
                    .assertion_pipeline_for_test()
                    .negated_goal_label_prefix(),
                Some("inner_goal")
            );

            let inner_label =
                encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |enc| {
                    enc.assertion_pipeline_mut_for_test()
                        .next_named_assertion_label()
                });
            assert_eq!(inner_label.as_deref(), Some("inner_goal_1"));
        });

        assert_eq!(
            encoder
                .assertion_pipeline_for_test()
                .negated_goal_label_prefix(),
            Some("outer_goal"),
            "inner override should restore the outer goal prefix"
        );

        let resumed_outer =
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |enc| {
                enc.assertion_pipeline_mut_for_test()
                    .next_named_assertion_label()
            });
        assert_eq!(resumed_outer.as_deref(), Some("outer_goal_2"));
    });

    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .negated_goal_label_prefix(),
        None,
        "the outer guard should restore the pre-existing None state"
    );
}

#[test]
#[timeout(30000)]
fn test_all_assertion_phase_label_prefixes() {
    let mut state = AssertionPipelineState::new();

    assert_eq!(state.next_named_assertion_label(), None);

    state.replace_phase(AssertionPhase::Precondition);
    let label = state.next_named_assertion_label().unwrap();
    assert!(label.starts_with("__trust_wp_precondition_"));

    state.replace_phase(AssertionPhase::NegatedPostcondition);
    let label = state.next_named_assertion_label().unwrap();
    assert!(label.starts_with("__trust_wp_negated_goal_"));

    state.replace_phase(AssertionPhase::AliasConstraint);
    let label = state.next_named_assertion_label().unwrap();
    assert!(label.starts_with("__trust_wp_alias_constraint_"));

    state.replace_phase(AssertionPhase::EncodingAxiom);
    let label = state.next_named_assertion_label().unwrap();
    assert!(label.starts_with("__trust_wp_encoding_axiom_"));

    state.replace_phase(AssertionPhase::GroundInstance);
    let label = state.next_named_assertion_label().unwrap();
    assert!(label.starts_with("__trust_wp_ground_instance_"));
}
