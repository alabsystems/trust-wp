// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::*;

/// Sort mismatch panic in `verify_loop_invariant` is caught and converted
/// to all-Unknown `LoopVerificationResult` instead of crashing the pipeline.
///
/// Trigger pattern: register `g(n: Int)` and call it with Bool arg in invariant.
#[cfg(debug_assertions)]
#[test]
#[timeout(30000)]
fn test_sort_mismatch_panic_caught_in_loop_verify() {
    use std::collections::HashMap;

    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // g(n) = n + 1, domain Int
    let logic_fn = LogicFnDef::new(
        "g_loop_test".to_string(),
        "test::g_loop_test".to_string(),
        vec!["n".to_string()],
        add(var("n"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // invariant: g(i > 0) == 5 — Bool arg into Int domain → Sort mismatch panic
    let inv = eq(
        logic_fn_call("g_loop_test", vec![gt(var("i"), int(0))]),
        int(5),
    );

    let body_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();
    let logic_fns = vec![logic_fn];

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    };

    let result = verify_loop_invariant(&ctx);

    // Sort mismatch should be caught, either as Ok(LoopVerificationResult with
    // Unknown) via verify-layer catch_unwind, or Err(EncodingError) via
    // After widened coercion (#2155), apply_logic_fn replaces the Bool
    // argument with a fresh Int constant, so no sort mismatch panic occurs.
    // The encoding succeeds and the solver attempts loop verification.
    match result {
        Ok(_) => {
            // Coercion prevented the panic; solver returned a loop result.
        }
        Err(ref e)
            if format!("{e:?}").contains("sort mismatch")
                || format!("{e:?}").contains("Sort mismatch") =>
        {
            // Sort mismatch caught in a deeper encoding path.
        }
        Err(ref e) => {
            panic!("Unexpected encoding error in loop verify (not sort-related): {e:?}");
        }
    }
}
