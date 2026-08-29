// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Diagnostic: body only (no pre), check sum invariance via tuple congruence.
///
/// Tests: body: result = tuple2(get_0(self_)+1, get_1(self_)-1),
///        post: NOT(get_0(result)+get_1(result) == get_0(self_)+get_1(self_))
///
/// This is a weaker version of SumTo10 — no precondition needed, since
/// (a+1)+(b-1) = a+b algebraically, regardless of what a+b equals.
///
/// **ay #724 FIXED:** ay now combines EUF tuple congruence with LIA arithmetic
/// to prove the sum equality (a+1)+(b-1) = a+b. Previously returned spurious Sat,
/// then Unknown. Now correctly returns Unsat. Updated per #1603 Category C.
#[test]
#[timeout(5000)]
fn test_ay_tuple_sum_invariance_no_precondition() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    let tuple2_decl = solver.declare_fun("tuple2", &[Sort::Int, Sort::Int], Sort::Int);
    let get_0_decl = solver.declare_fun("get_0", &[Sort::Int], Sort::Int);
    let get_1_decl = solver.declare_fun("get_1", &[Sort::Int], Sort::Int);

    // Tuple axioms with triggers
    let x0 = solver.fresh_var("x0", Sort::Int);
    let x1 = solver.fresh_var("x1", Sort::Int);
    let ctor = solver.apply(&tuple2_decl, &[x0, x1]);

    let g0_ctor = solver.apply(&get_0_decl, &[ctor]);
    let ax0_body = solver.eq(g0_ctor, x0);
    let ax0 = solver.forall_with_triggers(&[x0, x1], ax0_body, &[&[ctor]]);
    solver.assert_term(ax0);

    let g1_ctor = solver.apply(&get_1_decl, &[ctor]);
    let ax1_body = solver.eq(g1_ctor, x1);
    let ax1 = solver.forall_with_triggers(&[x0, x1], ax1_body, &[&[ctor]]);
    solver.assert_term(ax1);

    // Ground
    let self_ = solver.declare_const("self_", Sort::Int);
    let result = solver.declare_const("result", Sort::Int);

    // Body: result = tuple2(get_0(self_)+1, get_1(self_)-1)
    let g0_self = solver.apply(&get_0_decl, &[self_]);
    let g1_self = solver.apply(&get_1_decl, &[self_]);
    let one = solver.int_const(1);
    let g0_plus_1 = solver.add(g0_self, one);
    let one2 = solver.int_const(1);
    let g1_minus_1 = solver.sub(g1_self, one2);
    let tuple_val = solver.apply(&tuple2_decl, &[g0_plus_1, g1_minus_1]);
    let body_eq = solver.eq(result, tuple_val);
    solver.assert_term(body_eq);

    // Negated post: NOT(get_0(result)+get_1(result) == get_0(self_)+get_1(self_))
    // This should hold algebraically: (a+1)+(b-1) = a+b
    let g0_result = solver.apply(&get_0_decl, &[result]);
    let g1_result = solver.apply(&get_1_decl, &[result]);
    let sum_post = solver.add(g0_result, g1_result);
    let sum_pre = solver.add(g0_self, g1_self);
    let eq_sums = solver.eq(sum_post, sum_pre);
    let neg = solver.not(eq_sums);
    solver.assert_term(neg);

    // ay has fixed #724: EUF+LIA theory combination now works. ay fires E-match
    // instantiations for the tuple axioms AND combines the resulting equalities
    // with LIA arithmetic to prove (a+1)+(b-1) = a+b. The correct result is Unsat.
    // Previously: Sat (spurious) → Unknown → now Unsat (correct). (#1603 Category C)
    let sat_result = solver.check_sat().into_inner();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "ay #724 fixed: EUF+LIA combination should prove (a+1)+(b-1)=a+b, got {sat_result:?}"
    );
}

/// Diagnostic: separate field checks (no arithmetic combination).
///
/// Tests: body: result = tuple2(get_0(self_)+1, get_1(self_)-1),
///        post: NOT(get_0(result) == get_0(self_)+1 AND get_1(result) == get_1(self_)-1)
///
/// If this passes but the sum version fails, ay can derive individual
/// field values via congruence but can't combine them arithmetically.
#[test]
#[timeout(5000)]
fn test_ay_tuple_individual_field_congruence() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    let tuple2_decl = solver.declare_fun("tuple2", &[Sort::Int, Sort::Int], Sort::Int);
    let get_0_decl = solver.declare_fun("get_0", &[Sort::Int], Sort::Int);
    let get_1_decl = solver.declare_fun("get_1", &[Sort::Int], Sort::Int);

    let x0 = solver.fresh_var("x0", Sort::Int);
    let x1 = solver.fresh_var("x1", Sort::Int);
    let ctor = solver.apply(&tuple2_decl, &[x0, x1]);

    let g0_ctor = solver.apply(&get_0_decl, &[ctor]);
    let ax0_body = solver.eq(g0_ctor, x0);
    let ax0 = solver.forall_with_triggers(&[x0, x1], ax0_body, &[&[ctor]]);
    solver.assert_term(ax0);

    let g1_ctor = solver.apply(&get_1_decl, &[ctor]);
    let ax1_body = solver.eq(g1_ctor, x1);
    let ax1 = solver.forall_with_triggers(&[x0, x1], ax1_body, &[&[ctor]]);
    solver.assert_term(ax1);

    let self_ = solver.declare_const("self_", Sort::Int);
    let result = solver.declare_const("result", Sort::Int);

    // Body: result = tuple2(get_0(self_)+1, get_1(self_)-1)
    let g0_self = solver.apply(&get_0_decl, &[self_]);
    let g1_self = solver.apply(&get_1_decl, &[self_]);
    let one = solver.int_const(1);
    let g0_plus_1 = solver.add(g0_self, one);
    let one2 = solver.int_const(1);
    let g1_minus_1 = solver.sub(g1_self, one2);
    let tuple_val = solver.apply(&tuple2_decl, &[g0_plus_1, g1_minus_1]);
    let body_eq = solver.eq(result, tuple_val);
    solver.assert_term(body_eq);

    // Negated post: NOT(get_0(result) == get_0(self_)+1 AND get_1(result) == get_1(self_)-1)
    let g0_result = solver.apply(&get_0_decl, &[result]);
    let g1_result = solver.apply(&get_1_decl, &[result]);
    let one3 = solver.int_const(1);
    let expected_0 = solver.add(g0_self, one3);
    let one4 = solver.int_const(1);
    let expected_1 = solver.sub(g1_self, one4);
    let eq0 = solver.eq(g0_result, expected_0);
    let eq1 = solver.eq(g1_result, expected_1);
    let conj = solver.and(eq0, eq1);
    let neg = solver.not(conj);
    solver.assert_term(neg);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "ay should derive individual field values via tuple congruence"
    );
}
