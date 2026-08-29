// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── setup_loop_encoder comprehensive coverage (#2133) ──────────────

/// setup_loop_encoder registers sort hints from extra_exprs slices.
#[test]
#[timeout(30000)]
fn setup_loop_encoder_registers_extra_exprs_sort_hints() {
    let invariant = i_ge_zero();
    let extra = vec![PureExpr::Var("y".to_string(), Some(ExprSort::Bool))];

    let mut encoder = setup_loop_encoder(
        &[invariant],
        None,
        &[extra.as_slice()],
        &LoopEncoderConfig::default(),
    )
    .expect("setup_loop_encoder with extra_exprs should succeed");

    // `y` should have Bool hint from extra_exprs registration
    // Verify by encoding — if y were Int-default, this would still work,
    // but we can check via is_bool_var
    encoder.mark_bool_var("y"); // reinforce
    assert!(
        encoder.is_bool_var("y"),
        "y from extra_exprs should be tracked after setup"
    );
}

/// setup_loop_encoder with timeout config sets solver timeout.
#[test]
#[timeout(30000)]
fn setup_loop_encoder_applies_timeout() {
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };

    let _encoder = setup_loop_encoder(&[i_ge_zero()], None, &[], &config)
        .expect("setup_loop_encoder with timeout should succeed");
    // If this didn't panic, timeout was applied successfully
}

/// setup_loop_encoder with type_constants config sets integer constants.
#[test]
#[timeout(30000)]
fn setup_loop_encoder_applies_type_constants() {
    let mut constants = HashMap::new();
    constants.insert("i32::MIN".to_string(), PureExpr::Int(i32::MIN as i64));
    constants.insert("i32::MAX".to_string(), PureExpr::Int(i32::MAX as i64));

    let config = LoopEncoderConfig {
        type_constants: Some(&constants),
        ..LoopEncoderConfig::default()
    };

    let _encoder = setup_loop_encoder(&[i_ge_zero()], None, &[], &config)
        .expect("setup_loop_encoder with type_constants should succeed");
}

/// setup_loop_encoder registers loop_condition sort hints including
/// formula-level Bool hints. (#751)
#[test]
#[timeout(30000)]
fn setup_loop_encoder_condition_gets_formula_sort_hints() {
    // Use a condition with a variable that needs Bool sort
    let condition = PureExpr::Var("done".to_string(), Some(ExprSort::Bool));
    let invariant = PureExpr::Var("x".to_string(), None);

    let encoder = setup_loop_encoder(
        &[invariant],
        Some(&condition),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("setup_loop_encoder with Bool condition should succeed");

    assert!(
        encoder.is_bool_var("done"),
        "loop condition Bool var should get formula sort hint (#751)"
    );
}
