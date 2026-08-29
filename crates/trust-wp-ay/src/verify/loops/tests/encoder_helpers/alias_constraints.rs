// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct helper coverage for loop-specific aliasing and prophecy bridges
//! in `verify/loops/encoder_setup.rs` and `verify/loops/prime_substitutions.rs`.
//! Part of #2514.

use super::*;

/// The loop wrapper should delegate current-chain aliasing to the shared helper,
/// preserving the `_current_current = _current` link used by nested derefs.
#[test]
#[timeout(30000)]
fn loop_current_chain_alias_wrapper_links_deep_currents() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let f_current = encoder
        .get_or_declare_var("f_current", Sort::Int)
        .expect("f_current should declare");
    let f_current_current = encoder
        .get_or_declare_var("f_current_current", Sort::Int)
        .expect("f_current_current should declare");

    let seven = encoder.solver.int_const(7);
    let eq = encoder.solver.eq(f_current, seven);
    encoder.assert_term(eq);

    crate::verify::loops::encoder_setup::assert_loop_current_chain_alias_constraints(&mut encoder)
        .expect("loop current-chain alias constraints should succeed");

    let ninety_nine = encoder.solver.int_const(99);
    let eq = encoder.solver.eq(f_current_current, ninety_nine);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        ay_dpll::api::SolveResult::unsat(),
        "loop wrapper should enforce f_current_current = f_current"
    );
}

/// When a loop local has both a direct body effect and a deref body effect,
/// the bridge must still constrain `var_prime_current` to the deref write.
#[test]
#[timeout(30000)]
fn deref_prophecy_bridge_dual_effect_constrains_prime_current() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let mut direct = HashMap::new();
    direct.insert("k2".to_string(), var("source"));

    let mut deref = HashMap::new();
    deref.insert("k2".to_string(), int(1));

    let double_deref = HashMap::new();
    crate::verify::loops::prime_substitutions::assert_deref_prophecy_bridge(
        &mut encoder,
        effects(&direct, &deref, &double_deref),
        &[],
    )
    .expect("dual-effect prophecy bridge should succeed");

    let k2_prime_current = encoder
        .get_or_declare_var("k2_prime_current", Sort::Int)
        .expect("k2_prime_current should declare");
    let one = encoder.solver.int_const(1);
    let eq = encoder.solver.eq(k2_prime_current, one);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        ay_dpll::api::SolveResult::unsat(),
        "dual-effect bridge should constrain k2_prime_current = 1"
    );
}

/// Even without loop-element borrow resolution, deref prophecy bridging must
/// keep the pre-loop and post-step prophecy values equal.
#[test]
#[timeout(30000)]
fn deref_prophecy_bridge_links_final_to_prime_final() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let direct = HashMap::new();
    let mut deref = HashMap::new();
    deref.insert("k2".to_string(), int(1));
    let double_deref = HashMap::new();

    crate::verify::loops::prime_substitutions::assert_deref_prophecy_bridge(
        &mut encoder,
        effects(&direct, &deref, &double_deref),
        &[],
    )
    .expect("prophecy continuity bridge should succeed");

    let k2_final = encoder
        .get_or_declare_var("k2_final", Sort::Int)
        .expect("k2_final should declare");
    let k2_prime_final = encoder
        .get_or_declare_var("k2_prime_final", Sort::Int)
        .expect("k2_prime_final should declare");
    let eq = encoder.solver.eq(k2_final, k2_prime_final);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        ay_dpll::api::SolveResult::unsat(),
        "prophecy bridge should enforce k2_final = k2_prime_final"
    );
}

/// Loop-element borrow vars must additionally link `var_prime_final` to
/// `var_prime_current`, resolving the consumed borrow through the loop body.
#[test]
#[timeout(30000)]
fn deref_prophecy_bridge_loop_element_borrow_links_prime_final_to_current() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    let direct = HashMap::new();
    let mut deref = HashMap::new();
    deref.insert("k2".to_string(), int(1));
    let double_deref = HashMap::new();

    let k2_prime_current = encoder
        .get_or_declare_var("k2_prime_current", Sort::Int)
        .expect("k2_prime_current should declare");
    let seven = encoder.solver.int_const(7);
    let eq = encoder.solver.eq(k2_prime_current, seven);
    encoder.assert_term(eq);

    crate::verify::loops::prime_substitutions::assert_deref_prophecy_bridge(
        &mut encoder,
        effects(&direct, &deref, &double_deref),
        &["k2".to_string()],
    )
    .expect("loop-element borrow prophecy bridge should succeed");

    let k2_prime_final = encoder
        .get_or_declare_var("k2_prime_final", Sort::Int)
        .expect("k2_prime_final should declare");
    let eq = encoder.solver.eq(k2_prime_final, seven);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        ay_dpll::api::SolveResult::unsat(),
        "loop-element borrow bridge should enforce k2_prime_final = k2_prime_current"
    );
}
