// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

/// Diagnostic test for #6214: bypass trust-wp encoding, use raw ay API.
/// If this passes but test_frame_preservation_unchanged_local_postcondition fails,
/// the bug is in trust-wp's encoding layer, not ay.
#[test]
#[timeout(30000)]
fn test_6214_raw_ay_api_preservation_vc() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    let i = solver.declare_const("i", Sort::Int);
    let bound = solver.declare_const("bound", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Premises: i >= 0, i <= bound, i < bound
    let c1 = solver.ge(i, zero);
    solver.assert_term(c1);
    let c2 = solver.le(i, bound);
    solver.assert_term(c2);
    let c3 = solver.lt(i, bound);
    solver.assert_term(c3);

    // Body effect: i_prime = i + 1
    let i_plus_one = solver.add(i, one);
    let c4 = solver.eq(i_prime, i_plus_one);
    solver.assert_term(c4);

    // Negated conclusion: NOT(i_prime >= 0 AND i_prime <= bound)
    let ip_ge_0 = solver.ge(i_prime, zero);
    let ip_le_bound = solver.le(i_prime, bound);
    let conj = solver.and(ip_ge_0, ip_le_bound);
    let neg = solver.not(conj);
    solver.assert_term(neg);

    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Raw ay API should return UNSAT for this preservation VC"
    );
}

/// Diagnostic test for #6214: use trust-wp encoder but manual assertions.
/// Tests if the issue is in how assertions are created vs how they're asserted.
#[test]
#[timeout(30000)]
fn test_6214_trust_wp_encoder_manual_preservation_vc() {
    use ay_dpll::api::{SolveResult, Sort};

    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();

    let i = encoder.get_or_declare_var("i", Sort::Int).unwrap();
    let bound = encoder.get_or_declare_var("bound", Sort::Int).unwrap();
    let i_prime = encoder.get_or_declare_var("i_prime", Sort::Int).unwrap();
    let zero = encoder.solver_mut().int_const(0);
    let one = encoder.solver_mut().int_const(1);

    // Premises
    let c1 = encoder.solver_mut().ge(i, zero);
    encoder.assert_term(c1);
    let c2 = encoder.solver_mut().le(i, bound);
    encoder.assert_term(c2);
    let c3 = encoder.solver_mut().lt(i, bound);
    encoder.assert_term(c3);

    // Body effect
    let i_plus_one = encoder.solver_mut().add(i, one);
    let c4 = encoder.solver_mut().eq(i_prime, i_plus_one);
    encoder.assert_term(c4);

    // Negated conclusion
    let ip_ge_0 = encoder.solver_mut().ge(i_prime, zero);
    let ip_le_bound = encoder.solver_mut().le(i_prime, bound);
    let conj = encoder.solver_mut().and(ip_ge_0, ip_le_bound);
    let neg = encoder.solver_mut().not(conj);
    encoder.assert_term(neg);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "trust-wp encoder with manual assertions should return UNSAT"
    );
}

/// ROOT CAUSE test for #6214: alias substitution replaces `bound → n` in invariants
/// but NOT in loop condition, making the preservation VC satisfiable.
///
/// The preservation formula becomes:
///   i >= 0 ∧ i <= n ∧ i < bound ∧ i' = i + 1 ∧ ¬(i' >= 0 ∧ i' <= n)
///
/// This is SAT because bound is unconstrained: set n=0, i=0, bound=1, i'=1.
/// Then ¬(1 >= 0 ∧ 1 <= 0) = ¬false = true.
#[test]
#[timeout(30000)]
fn test_6214_alias_sub_mismatch_is_root_cause() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    let i = solver.declare_const("i", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let bound = solver.declare_const("bound", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Substituted invariants: i >= 0, i <= n (was i <= bound)
    let c1 = solver.ge(i, zero);
    solver.assert_term(c1);
    let c2 = solver.le(i, n);
    solver.assert_term(c2);

    // UNsubstituted condition: i < bound (not i < n!)
    let c3 = solver.lt(i, bound);
    solver.assert_term(c3);

    let i_plus_one = solver.add(i, one);
    let c4 = solver.eq(i_prime, i_plus_one);
    solver.assert_term(c4);

    // Negated primed invariants: NOT(i' >= 0 AND i' <= n)
    let ip_ge_0 = solver.ge(i_prime, zero);
    let ip_le_n = solver.le(i_prime, n);
    let conj = solver.and(ip_ge_0, ip_le_n);
    let neg = solver.not(conj);
    solver.assert_term(neg);

    // This IS satisfiable: n=0, i=0, bound=1, i'=1
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "With alias mismatch, this is SAT (the trust-wp bug root cause)"
    );
}

/// Diagnostic test for #6214: use trust-wp's encode_pure for the same formula.
/// Tests if the issue is in encode_pure specifically.
#[test]
#[timeout(30000)]
fn test_6214_trust_wp_encode_pure_preservation_vc() {
    use ay_dpll::api::{SolveResult, Sort};
    use trust_wp_core::formula::{BinOp, PureExpr};

    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();

    // Pre-declare variables (matching trust-wp's propagate_bool_and_predeclare flow)
    encoder.get_or_declare_var("i", Sort::Int).unwrap();
    encoder.get_or_declare_var("bound", Sort::Int).unwrap();
    encoder.get_or_declare_var("i_prime", Sort::Int).unwrap();

    // Register sort hints (matching trust-wp flow)
    let inv1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let inv2 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("bound".to_string(), None)),
    );
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("bound".to_string(), None)),
    );

    encoder.register_sort_hints(&[inv1.clone(), inv2.clone()]);
    encoder.register_formula_sort_hints(&[inv1.clone(), inv2.clone()]);
    encoder.register_sort_hints(std::slice::from_ref(&cond));
    encoder.register_formula_sort_hints(std::slice::from_ref(&cond));

    // 1. Assert invariants via encode_pure
    let inv1_term = encoder.encode_pure(&inv1).unwrap();
    encoder.assert_term(inv1_term);
    let inv2_term = encoder.encode_pure(&inv2).unwrap();
    encoder.assert_term(inv2_term);

    // 2. Assert condition
    let cond_term = encoder.encode_pure(&cond).unwrap();
    encoder.assert_term(cond_term);

    // 3. Assert body effect: i_prime = i + 1
    let effect = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let i_prime_var = encoder.get_or_declare_var("i_prime", Sort::Int).unwrap();
    let effect_term = encoder.encode_pure(&effect).unwrap();
    let eq_term = encoder.solver_mut().eq(i_prime_var, effect_term);
    encoder.assert_term(eq_term);

    // 4. Negated primed invariants: NOT(i_prime >= 0 AND i_prime <= bound)
    let primed_inv1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i_prime".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let primed_inv2 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i_prime".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("bound".to_string(), None)),
    );

    encoder.register_sort_hints(&[primed_inv1.clone(), primed_inv2.clone()]);
    encoder.register_formula_sort_hints(&[primed_inv1.clone(), primed_inv2.clone()]);

    let pi1_term = encoder.encode_pure(&primed_inv1).unwrap();
    let pi2_term = encoder.encode_pure(&primed_inv2).unwrap();
    let conj = encoder.solver_mut().and(pi1_term, pi2_term);
    let neg = encoder.solver_mut().not(conj);
    encoder.assert_term(neg);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "trust-wp encode_pure with same formula should return UNSAT"
    );
}
