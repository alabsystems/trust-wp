// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

/// Direct ay API test: minimal `QF_LIA` query that should be UNSAT.
/// Confirms ay can solve individual preservation clauses.
#[test]
#[timeout(30000)]
fn test_ay_direct_qflia_preservation_clause() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    // Query: i >= 0 ∧ i <= n ∧ i < n ∧ ¬((i+1) >= 0)
    // This is trivially UNSAT: i >= 0 implies i+1 >= 1 >= 0
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let i = solver.declare_const("i", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Assert: i >= 0
    let i_ge_0 = solver.ge(i, zero);
    solver.assert_term(i_ge_0);

    // Assert: i <= n
    let i_le_n = solver.le(i, n);
    solver.assert_term(i_le_n);

    // Assert: i < n
    let i_lt_n = solver.lt(i, n);
    solver.assert_term(i_lt_n);

    // Assert: ¬((i+1) >= 0)
    let i_plus_1 = solver.add(i, one);
    let i1_ge_0 = solver.ge(i_plus_1, zero);
    let neg = solver.not(i1_ge_0);
    solver.assert_term(neg);

    let result = solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Direct ay QF_LIA: i>=0 ∧ i<=n ∧ i<n ∧ (i+1)<0 should be UNSAT, got {result:?}"
    );
}

/// `ay` `QF_LIA` previously returned Unknown for `not(le(add(i,1), n))`.
/// Query: i >= 0 ∧ i <= n ∧ i < n ∧ ¬((i+1) <= n) should be UNSAT.
/// This limitation (ay#1836 residual) has been resolved; ay now returns Unsat.
/// The proxy variable workaround is kept as a secondary verification.
#[test]
#[timeout(30000)]
fn test_ay_qflia_compound_arith_unknown_regression() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    // Without proxy: gt(add(i,1), n) → Unsat (previously Unknown)
    let result_without = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);

        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        let c3 = solver.lt(i, n);
        solver.assert_term(c3);
        let i_plus_1 = solver.add(i, one);
        let c4 = solver.gt(i_plus_1, n);
        solver.assert_term(c4);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_without, SolveResult::Unsat(_)),
        "Compound arith without proxy should be Unsat (ay QF_LIA limitation resolved), got {result_without:?}"
    );

    // With proxy: j = i+1, gt(j, n) → Unsat
    let result_with = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let j = solver.declare_const("j", Sort::Int);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);

        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        let c3 = solver.lt(i, n);
        solver.assert_term(c3);
        let i_plus_1 = solver.add(i, one);
        let j_eq = solver.eq(j, i_plus_1);
        solver.assert_term(j_eq);
        let c4 = solver.gt(j, n);
        solver.assert_term(c4);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_with, SolveResult::Unsat(_)),
        "Proxy var workaround should be Unsat, got {result_with:?}"
    );
}

/// `ay` `QF_LIA` previously returned Unknown for `sub()` with 3+ constraints.
/// This limitation has been resolved; all variants now correctly return Unsat.
/// i >= 0 ∧ i <= n ∧ i < n ∧ `lt(sub(n,i), 0)` → Unsat (previously Unknown).
/// Contrast: i <= n ∧ `lt(sub(n,i), 0)` → Unsat (always worked).
#[test]
#[timeout(30000)]
fn test_ay_qflia_sub_multi_constraint_unknown() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    // 2 constraints: works
    let result_2 = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let zero = solver.int_const(0);
        let c1 = solver.le(i, n);
        solver.assert_term(c1);
        let n_minus_i = solver.sub(n, i);
        let c2 = solver.lt(n_minus_i, zero);
        solver.assert_term(c2);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_2, SolveResult::Unsat(_)),
        "2-constraint sub pattern should be Unsat, got {result_2:?}"
    );

    // 4 constraints: Unsat (previously Unknown)
    let result_4 = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let zero = solver.int_const(0);
        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        let c3 = solver.lt(i, n);
        solver.assert_term(c3);
        let n_minus_i = solver.sub(n, i);
        let c4 = solver.lt(n_minus_i, zero);
        solver.assert_term(c4);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_4, SolveResult::Unsat(_)),
        "4-constraint sub pattern should be Unsat (ay QF_LIA limitation resolved), got {result_4:?}"
    );

    // lt(i,n) ∧ lt(n,i) is trivially UNSAT.
    // Previously ay returned Unknown due to QF_LIA lt() branch-and-bound oscillation,
    // but this limitation has been resolved in the current pinned ay rev.
    let result_lt_lt = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let c1 = solver.lt(i, n);
        solver.assert_term(c1);
        let c2 = solver.lt(n, i);
        solver.assert_term(c2);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_lt_lt, SolveResult::Unsat(_)),
        "lt(i,n) ∧ lt(n,i) should be Unsat (ay QF_LIA limitation resolved), got {result_lt_lt:?}"
    );

    // Workaround: rewrite lt(i,n) as c=i+1 ∧ le(c,n) — avoids ay lt() limitation
    let result_le_proxy = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let c = solver.declare_const("c", Sort::Int);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        let i_plus_1 = solver.add(i, one);
        let c_eq = solver.eq(c, i_plus_1);
        solver.assert_term(c_eq);
        let c3 = solver.le(c, n);
        solver.assert_term(c3);
        let n_minus_i = solver.sub(n, i);
        let c4 = solver.lt(n_minus_i, zero);
        solver.assert_term(c4);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_le_proxy, SolveResult::Unsat(_)),
        "le-proxy workaround should be Unsat, got {result_le_proxy:?}"
    );
}

/// `ay` `QF_LIA` previously returned Unknown for `gt(n,i)` ∧ `gt(i,n)`.
/// This limitation has been resolved; ay now correctly returns Unsat.
/// Verifies both the direct encoding and the gt-avoidance workaround (ge + proxy).
#[test]
#[timeout(30000)]
fn test_ay_qflia_gt_unknown_and_workaround() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    // gt(n,i) ∧ gt(i,n) should be UNSAT (previously ay returned Unknown, now resolved)
    let result_gt = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let c1 = solver.gt(n, i);
        solver.assert_term(c1);
        let c2 = solver.gt(i, n);
        solver.assert_term(c2);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_gt, SolveResult::Unsat(_)),
        "gt(n,i) ∧ gt(i,n) should be Unsat (ay QF_LIA limitation resolved), got {result_gt:?}"
    );

    // Workaround: gt(a,b) → proxy = b+1, ge(a, proxy)
    let result_ge_proxy = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let p1 = solver.declare_const("p1", Sort::Int);
        let p2 = solver.declare_const("p2", Sort::Int);
        let one = solver.int_const(1);
        // gt(n, i) → p1 = i+1, ge(n, p1)
        let i_plus_1 = solver.add(i, one);
        let eq1 = solver.eq(p1, i_plus_1);
        solver.assert_term(eq1);
        let c1 = solver.ge(n, p1);
        solver.assert_term(c1);
        // gt(i, n) → p2 = n+1, ge(i, p2)
        let n_plus_1 = solver.add(n, one);
        let eq2 = solver.eq(p2, n_plus_1);
        solver.assert_term(eq2);
        let c2 = solver.ge(i, p2);
        solver.assert_term(c2);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_ge_proxy, SolveResult::Unsat(_)),
        "ge-proxy workaround for gt should be Unsat, got {result_ge_proxy:?}"
    );
}

/// ay#1998 regression: variant non-negativity with subtraction (direct solver).
///
/// ay#1998 caused LIA to return incorrect SAT for formulas involving
/// subtraction in strict comparisons. The trigger pattern for variant
/// non-negativity is:
///
///   i >= 0 AND i <= n AND i < n AND lt(sub(n, i), 0)
///
/// This should be UNSAT (if i < n then n - i > 0, so n - i < 0 is false).
/// ay#1998 would return SAT (soundness bug, now fixed in pinned ay rev).
///
/// Historical proxy encoding (kept here as a direct-solver reference) rewrites
/// `variant < 0` as:
///   `__neg_proxy = variant + 1, le(__neg_proxy, 0)`
///
/// This test verifies both:
/// 1. Direct encoding does NOT return SAT (regression guard)
/// 2. Proxy encoding returns UNSAT
#[test]
#[timeout(30000)]
fn test_ay_1998_variant_nonneg_subtraction_regression() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    // Direct encoding: lt(sub(n, i), 0) with invariant constraints
    // ay#1998 would incorrectly return SAT here.
    let result_direct = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let zero = solver.int_const(0);

        // Invariants
        let c1 = solver.ge(i, zero); // i >= 0
        solver.assert_term(c1);
        let c2 = solver.le(i, n); // i <= n
        solver.assert_term(c2);
        // Loop condition
        let c3 = solver.lt(i, n); // i < n
        solver.assert_term(c3);
        // Negated non-negativity: variant < 0, i.e., n - i < 0
        let n_minus_i = solver.sub(n, i);
        let c4 = solver.lt(n_minus_i, zero);
        solver.assert_term(c4);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_direct, SolveResult::Unsat(_)),
        "ay#1998 regression guard: direct encoding should be Unsat (ay QF_LIA limitation resolved), got {result_direct:?}"
    );

    // Proxy workaround: __neg_proxy = sub(n, i) + 1, le(__neg_proxy, 0)
    let result_proxy = {
        let mut solver = Solver::try_new(Logic::QfLia).unwrap();
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let neg_proxy = solver.declare_const("__neg_proxy", Sort::Int);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);

        // Invariants
        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        // Loop condition
        let c3 = solver.lt(i, n);
        solver.assert_term(c3);
        // Proxy rewrite: __neg_proxy = (n - i) + 1, le(__neg_proxy, 0)
        let n_minus_i = solver.sub(n, i);
        let variant_plus_1 = solver.add(n_minus_i, one);
        let eq = solver.eq(neg_proxy, variant_plus_1);
        solver.assert_term(eq);
        let c4 = solver.le(neg_proxy, zero);
        solver.assert_term(c4);
        solver.check_sat().into_inner()
    };
    assert!(
        matches!(result_proxy, SolveResult::Unsat(_)),
        "Proxy workaround for variant nonneg should be Unsat, got {result_proxy:?}"
    );
}
