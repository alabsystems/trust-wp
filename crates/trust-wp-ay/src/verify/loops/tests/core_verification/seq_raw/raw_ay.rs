// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Raw ay-dpll test: pure LIA without any encoder. Confirms ay-dpll can
/// handle `a + b = c, NOT((a+1) + b = c+1)` → UNSAT.
#[test]
#[timeout(30000)]
fn raw_ay_lia_three_var_unsat() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    let mut solver = Solver::new(Logic::QfAuflia);

    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);

    // Assert: a + b = c
    let sum = solver.add(a, b);
    let eq1 = solver.eq(sum, c);
    solver.assert_term(eq1);

    // Assert: NOT((a + 1) + b = c + 1)
    let one = solver.int_const(1);
    let a_plus_1 = solver.add(a, one);
    let sum2 = solver.add(a_plus_1, b);
    let c_plus_1 = solver.add(c, one);
    let eq2 = solver.eq(sum2, c_plus_1);
    let neg = solver.not(eq2);
    solver.assert_term(neg);

    let result = solver.check_sat().into_inner();
    assert_eq!(result, SolveResult::unsat(), "pure LIA should be UNSAT");
}

/// Documents ay-dpll theory combination limitation (#2323): UF applications
/// embedded directly in LIA expressions are not properly propagated between
/// the EUF and LIA solvers. This problem `f(x) + b = c, f(x') = f(x) + 1,
/// NOT(f(x') + b = c + 1)` is mathematically UNSAT but ay-dpll returns SAT.
/// The workaround (see `raw_ay_uf_lia_with_auxiliary_int_vars`) introduces
/// auxiliary Int variables bridging UF applications into pure LIA.
#[test]
#[timeout(30000)]
fn raw_ay_uf_lia_three_var_known_bug() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    let mut solver = Solver::new(Logic::QfAuflia);

    let seq_sort = Sort::seq(Sort::Int);
    let f = solver.declare_fun("f", &[seq_sort.clone()], Sort::Int);
    let g = solver.declare_fun("g", &[seq_sort.clone(), Sort::Int], seq_sort.clone());

    let x = solver.declare_const("x", seq_sort.clone());
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);
    let e = solver.declare_const("e", Sort::Int);
    let x_prime = solver.declare_const("x_prime", seq_sort);

    // f(x) + b = c
    let fx = solver.apply(&f, &[x]);
    let fx_plus_b = solver.add(fx, b);
    let eq1 = solver.eq(fx_plus_b, c);
    solver.assert_term(eq1);

    // x' = g(x, e)
    let gx = solver.apply(&g, &[x, e]);
    let eq2 = solver.eq(x_prime, gx);
    solver.assert_term(eq2);

    // f(x') = f(x) + 1  (explicit — like the congruence hint)
    let fx_prime = solver.apply(&f, &[x_prime]);
    let one = solver.int_const(1);
    let fx_plus_1 = solver.add(fx, one);
    let eq3 = solver.eq(fx_prime, fx_plus_1);
    solver.assert_term(eq3);

    // c' = c + 1
    let c_prime = solver.declare_const("c_prime", Sort::Int);
    let c_plus_1 = solver.add(c, one);
    let eq4 = solver.eq(c_prime, c_plus_1);
    solver.assert_term(eq4);

    // NOT(f(x') + b = c')
    let fx_prime_plus_b = solver.add(fx_prime, b);
    let eq5 = solver.eq(fx_prime_plus_b, c_prime);
    let neg = solver.not(eq5);
    solver.assert_term(neg);

    let result = solver.check_sat().into_inner();
    // ay-dpll theory combination bug (#2323) has been fixed.
    // This problem is mathematically UNSAT: f(x) + b = c, f(x') = f(x) + 1,
    // c' = c + 1, but NOT(f(x') + b = c'). Substituting gives
    // f(x)+1+b = c+1 which simplifies to f(x)+b = c, contradicting eq1.
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ay-dpll should correctly return UNSAT for this theory combination problem, got {result:?}"
    );
}

/// Workaround test: use auxiliary Int variables to bridge UF applications into
/// pure LIA. If ay-dpll can't combine UF+LIA directly, we can introduce
/// `len_produced: Int = f(x)` and use `len_produced` in arithmetic.
#[test]
#[timeout(30000)]
fn raw_ay_uf_lia_with_auxiliary_int_vars() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    let mut solver = Solver::new(Logic::QfAuflia);

    let seq_sort = Sort::seq(Sort::Int);
    let f = solver.declare_fun("f", &[seq_sort.clone()], Sort::Int);

    let x = solver.declare_const("x", seq_sort.clone());
    let x_prime = solver.declare_const("x_prime", seq_sort);
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);
    let c_prime = solver.declare_const("c_prime", Sort::Int);

    // Introduce auxiliary Int variables for UF results
    let fx_val = solver.declare_const("fx_val", Sort::Int);
    let fx_prime_val = solver.declare_const("fx_prime_val", Sort::Int);

    // Bridge: fx_val = f(x), fx_prime_val = f(x')
    let fx = solver.apply(&f, &[x]);
    let fx_prime = solver.apply(&f, &[x_prime]);
    let eq_bridge1 = solver.eq(fx_val, fx);
    let eq_bridge2 = solver.eq(fx_prime_val, fx_prime);
    solver.assert_term(eq_bridge1);
    solver.assert_term(eq_bridge2);

    // Now use pure Int variables in arithmetic:
    // fx_val + b = c
    let sum1 = solver.add(fx_val, b);
    let eq1 = solver.eq(sum1, c);
    solver.assert_term(eq1);

    // fx_prime_val = fx_val + 1
    let one = solver.int_const(1);
    let fx_val_plus_1 = solver.add(fx_val, one);
    let eq2 = solver.eq(fx_prime_val, fx_val_plus_1);
    solver.assert_term(eq2);

    // c' = c + 1
    let c_plus_1 = solver.add(c, one);
    let eq3 = solver.eq(c_prime, c_plus_1);
    solver.assert_term(eq3);

    // NOT(fx_prime_val + b = c')
    let sum2 = solver.add(fx_prime_val, b);
    let eq4 = solver.eq(sum2, c_prime);
    let neg = solver.not(eq4);
    solver.assert_term(neg);

    let result = solver.check_sat().into_inner();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "UF+LIA with aux Int vars should be UNSAT"
    );
}
