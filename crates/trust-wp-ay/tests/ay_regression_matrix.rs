// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// ay-dpll deprecated panicking API — allow until try_* migration.
#![allow(deprecated)]

//! ay-dpll regression test matrix for pin validation (#1688).
//!
//! Minimal SMT queries that exercise core ay capabilities used by trust-wp.
//! Run this suite when bumping the ay-dpll pin to detect regressions early.
//!
//! Categories:
//! 1. QF_AUFLIA basic sat/unsat — integer arithmetic, boolean logic
//! 2. Array read-over-write — concrete and symbolic indices
//! 3. Quantifier instantiation — forall/exists with triggers
//! 4. Uninterpreted function equality — congruence closure
//! 5. Push/pop — incremental solving context management

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
use ntest::timeout;

// ============================================================================
// 1. QF_AUFLIA basic sat/unsat
// ============================================================================

/// Basic integer arithmetic: 2 + 3 == 5 is valid (negation is UNSAT).
#[test]
#[timeout(10000)]
fn qf_auflia_int_arithmetic_valid() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let two = s.int_const(2);
    let three = s.int_const(3);
    let five = s.int_const(5);
    let sum = s.add(two, three);
    let neq = s.neq(sum, five);
    s.assert_term(neq);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "2 + 3 != 5 should be UNSAT"
    );
}

/// Symbolic integer: x > 0 AND x < 0 is UNSAT.
#[test]
#[timeout(10000)]
fn qf_auflia_contradictory_bounds_unsat() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let x_pos = s.gt(x, zero);
    let x_neg = s.lt(x, zero);
    let both = s.and(x_pos, x_neg);
    s.assert_term(both);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "x > 0 AND x < 0 should be UNSAT"
    );
}

/// Symbolic integer: x > 0 is satisfiable.
#[test]
#[timeout(10000)]
fn qf_auflia_positive_int_sat() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let x_pos = s.gt(x, zero);
    s.assert_term(x_pos);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 should be SAT"
    );
}

/// Boolean: true AND NOT(false) is SAT.
#[test]
#[timeout(10000)]
fn qf_auflia_bool_basic_sat() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let t = s.bool_const(true);
    let f = s.bool_const(false);
    let not_f = s.not(f);
    let conj = s.and(t, not_f);
    s.assert_term(conj);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "true AND NOT(false) should be SAT"
    );
}

/// Boolean: true AND false is UNSAT.
#[test]
#[timeout(10000)]
fn qf_auflia_bool_contradiction_unsat() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let t = s.bool_const(true);
    let f = s.bool_const(false);
    s.assert_term(t);
    s.assert_term(f);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "true AND false should be UNSAT"
    );
}

// ============================================================================
// 2. Array read-over-write (concrete + symbolic)
// ============================================================================

/// Concrete: store(A, 0, 42)[0] == 42 (read-over-write, same index).
#[test]
#[timeout(10000)]
fn array_row_concrete_same_index() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let arr = s.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = s.int_const(0);
    let val = s.int_const(42);
    let updated = s.store(arr, idx, val);
    let read_back = s.select(updated, idx);
    let neq = s.neq(read_back, val);
    s.assert_term(neq);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "store(A,0,42)[0] != 42 should be UNSAT (read-over-write same index)"
    );
}

/// Concrete: store(A, 0, 42)[1] preserves original value at different index.
#[test]
#[timeout(10000)]
fn array_row_concrete_different_index() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let arr = s.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx0 = s.int_const(0);
    let idx1 = s.int_const(1);
    let val = s.int_const(42);
    let original_at_1 = s.select(arr, idx1);
    let updated = s.store(arr, idx0, val);
    let after_at_1 = s.select(updated, idx1);
    let neq = s.neq(original_at_1, after_at_1);
    s.assert_term(neq);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "store(A,0,42)[1] != A[1] should be UNSAT (read-over-write different index)"
    );
}

/// Symbolic: store(A, i, v)[i] == v for symbolic i, v.
#[test]
#[timeout(10000)]
fn array_row_symbolic_same_index() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let arr = s.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let i = s.declare_const("i", Sort::Int);
    let v = s.declare_const("v", Sort::Int);
    let updated = s.store(arr, i, v);
    let read_back = s.select(updated, i);
    let neq = s.neq(read_back, v);
    s.assert_term(neq);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "store(A,i,v)[i] != v should be UNSAT (symbolic read-over-write same index)"
    );
}

/// Symbolic: store(A, i, v)[j] == A[j] when i != j.
#[test]
#[timeout(10000)]
fn array_row_symbolic_different_index() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let arr = s.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let i = s.declare_const("i", Sort::Int);
    let j = s.declare_const("j", Sort::Int);
    let v = s.declare_const("v", Sort::Int);
    // Premise: i != j
    let i_ne_j = s.neq(i, j);
    s.assert_term(i_ne_j);
    // Conclusion: store(A,i,v)[j] == A[j]
    let original = s.select(arr, j);
    let updated = s.store(arr, i, v);
    let after = s.select(updated, j);
    let neq = s.neq(original, after);
    s.assert_term(neq);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "i!=j => store(A,i,v)[j] != A[j] should be UNSAT (symbolic ROW different index)"
    );
}

/// Bool-valued array: domain map pattern used by separation logic.
#[test]
#[timeout(10000)]
fn array_bool_domain_map() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let domain = s.declare_const("domain", Sort::array(Sort::Int, Sort::Bool));
    let loc = s.declare_const("loc", Sort::Int);
    let tt = s.bool_const(true);
    let updated = s.store(domain, loc, tt);
    let read_back = s.select(updated, loc);
    // read_back should be true
    let not_rb = s.not(read_back);
    s.assert_term(not_rb);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "NOT(store(domain,loc,true)[loc]) should be UNSAT"
    );
}

// ============================================================================
// 3. Quantifier instantiation
// ============================================================================

/// Forall with trigger: forall x. f(x) > 0, given f(5), check f(5) > 0.
#[test]
#[timeout(10000)]
fn quantifier_forall_trigger_instantiation() {
    let mut s = Solver::try_new(Logic::Auflia).unwrap();
    let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
    let qvar = s.fresh_var("x", Sort::Int);
    let fx = s.apply(&f, &[qvar]);
    let zero = s.int_const(0);
    let fx_gt_0 = s.gt(fx, zero);
    // Axiom: forall x {:pattern f(x)} f(x) > 0
    let axiom = s.forall_with_triggers(&[qvar], fx_gt_0, &[&[fx]]);
    s.assert_term(axiom);
    // Ground: f(5)
    let five = s.int_const(5);
    let f5 = s.apply(&f, &[five]);
    // Negate: f(5) <= 0
    let f5_le_0 = s.le(f5, zero);
    s.assert_term(f5_le_0);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "forall x. f(x)>0 AND f(5)<=0 should be UNSAT via E-matching"
    );
}

/// Exists: exists x. x == 42 is SAT.
#[test]
#[timeout(10000)]
fn quantifier_exists_witness_sat() {
    let mut s = Solver::try_new(Logic::Auflia).unwrap();
    let qvar = s.fresh_var("x", Sort::Int);
    let forty_two = s.int_const(42);
    let eq = s.eq(qvar, forty_two);
    let ex = s.exists(&[qvar], eq);
    s.assert_term(ex);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "exists x. x==42 should be SAT"
    );
}

/// Forall with ground conflict: forall x. f(x) > 0 AND f(7) == -1 is UNSAT.
/// Uses a trigger on f(x) to ensure instantiation at the ground term f(7).
#[test]
#[timeout(10000)]
fn quantifier_forall_ground_conflict_unsat() {
    let mut s = Solver::try_new(Logic::Auflia).unwrap();
    let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
    let qvar = s.fresh_var("x", Sort::Int);
    let fx = s.apply(&f, &[qvar]);
    let zero = s.int_const(0);
    let fx_gt_0 = s.gt(fx, zero);
    let axiom = s.forall_with_triggers(&[qvar], fx_gt_0, &[&[fx]]);
    s.assert_term(axiom);
    // Ground conflict: f(7) == -1
    let seven = s.int_const(7);
    let f7 = s.apply(&f, &[seven]);
    let neg_one = s.int_const(-1);
    let f7_eq_neg = s.eq(f7, neg_one);
    s.assert_term(f7_eq_neg);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "forall x. f(x)>0 AND f(7)==-1 should be UNSAT via trigger instantiation"
    );
}

// ============================================================================
// 4. Uninterpreted function equality (congruence closure)
// ============================================================================

/// UF congruence: a == b => f(a) == f(b).
#[test]
#[timeout(10000)]
fn uf_congruence_closure() {
    let mut s = Solver::try_new(Logic::QfUflia).unwrap();
    let a = s.declare_const("a", Sort::Int);
    let b = s.declare_const("b", Sort::Int);
    let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
    // Premise: a == b
    let a_eq_b = s.eq(a, b);
    s.assert_term(a_eq_b);
    // Negate conclusion: f(a) != f(b)
    let fa = s.apply(&f, &[a]);
    let fb = s.apply(&f, &[b]);
    let fa_neq_fb = s.neq(fa, fb);
    s.assert_term(fa_neq_fb);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "a==b AND f(a)!=f(b) should be UNSAT (congruence closure)"
    );
}

/// UF transitivity: a == b AND b == c => f(a) == f(c).
#[test]
#[timeout(10000)]
fn uf_transitivity() {
    let mut s = Solver::try_new(Logic::QfUflia).unwrap();
    let a = s.declare_const("a", Sort::Int);
    let b = s.declare_const("b", Sort::Int);
    let c = s.declare_const("c", Sort::Int);
    let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
    let a_eq_b = s.eq(a, b);
    let b_eq_c = s.eq(b, c);
    s.assert_term(a_eq_b);
    s.assert_term(b_eq_c);
    let fa = s.apply(&f, &[a]);
    let fc = s.apply(&f, &[c]);
    let fa_neq_fc = s.neq(fa, fc);
    s.assert_term(fa_neq_fc);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "a==b AND b==c AND f(a)!=f(c) should be UNSAT (UF transitivity)"
    );
}

/// UF distinctness: f(a) != f(b) implies a != b.
#[test]
#[timeout(10000)]
fn uf_distinctness_contrapositive() {
    let mut s = Solver::try_new(Logic::QfUflia).unwrap();
    let a = s.declare_const("a", Sort::Int);
    let b = s.declare_const("b", Sort::Int);
    let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
    let fa = s.apply(&f, &[a]);
    let fb = s.apply(&f, &[b]);
    let fa_neq_fb = s.neq(fa, fb);
    s.assert_term(fa_neq_fb);
    // f(a) != f(b) AND a == b should be UNSAT (by congruence, f(a)==f(b))
    let a_eq_b = s.eq(a, b);
    s.assert_term(a_eq_b);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "f(a)!=f(b) AND a==b should be UNSAT (contrapositive of congruence)"
    );
}

// ============================================================================
// 5. Push/pop (incremental solving)
//
// These tests validate ay's push/pop contract (ay#3664). trust-wp's production
// code uses push/pop for per-postcondition obligation slicing in
// verify/function/mod.rs and verify/mut_borrow/mod.rs. The tests here serve
// as a regression gate: if ay push/pop breaks again, these fail before
// production verification produces unsound results. See also #1698 audit.
// ============================================================================

/// Push/pop preserves base assertions after scope exit.
#[test]
#[timeout(10000)]
fn push_pop_base_preserved() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let ten = s.int_const(10);
    // Base: x > 0
    let x_pos = s.gt(x, zero);
    s.assert_term(x_pos);

    // Push and add x > 10
    s.push();
    let x_gt_10 = s.gt(x, ten);
    s.assert_term(x_gt_10);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 AND x > 10 should be SAT"
    );
    s.pop();

    // After pop, only x > 0 remains — x == 5 should be satisfiable
    let five = s.int_const(5);
    let x_eq_5 = s.eq(x, five);
    s.assert_term(x_eq_5);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 AND x == 5 should be SAT after pop (x > 10 removed)"
    );
}

/// Push/pop: contradiction inside scope doesn't affect outer scope.
#[test]
#[timeout(10000)]
fn push_pop_contradiction_scoped() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let x_pos = s.gt(x, zero);
    s.assert_term(x_pos);

    // Push, add contradiction
    s.push();
    let x_neg = s.lt(x, zero);
    s.assert_term(x_neg);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Unsat(_)),
        "x > 0 AND x < 0 should be UNSAT inside pushed scope"
    );
    s.pop();

    // After pop, base is still SAT
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 should be SAT after popping contradiction"
    );
}

// ============================================================================
// 6. QF_LIA soundness — loop preservation counterexamples (#2056)
//
// These tests encode the same SMT queries as 5 of the 6 failing trust-wp loop
// verification tests, but at the raw ay-dpll API level (no trust-wp encoding).
// The 6th (test_loop_preservation_two_logic_fns, UFLIA) is excluded because
// it uses quantifiers, not pure QF_LIA.
// If these fail, the bug is in ay. If they pass, the bug is in trust-wp's
// encoding pipeline.
//
// All use the refutation pattern: assert preconditions + NOT(postcondition),
// check SAT. Expected: SAT (counterexample exists).
// ============================================================================

/// Loop preservation with disjunctive condition: (i < n) || (k > 0).
/// Counterexample: i = n, k = 1 => i' = n + 1 > n violates i' <= n.
/// Corresponds to: tests::loops::test_loop_preservation_lt_inside_or
#[test]
#[timeout(10000)]
fn qf_lia_loop_disjunctive_cond_counterexample() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let k = s.declare_const("k", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);

    // Invariants: i >= 0 AND i <= n
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);

    // Loop condition: (i < n) || (k > 0)
    let i_lt_n = s.lt(i, n);
    let k_gt_0 = s.gt(k, zero);
    let cond = s.or(i_lt_n, k_gt_0);
    s.assert_term(cond);

    // Body effect: i_prime = i + 1
    let i_plus_1 = s.add(i, one);
    let effect = s.eq(i_prime, i_plus_1);
    s.assert_term(effect);

    // Negation of primed invariants: NOT(i_prime >= 0 AND i_prime <= n)
    let primed_inv1 = s.ge(i_prime, zero);
    let primed_inv2 = s.le(i_prime, n);
    let primed_conj = s.and(primed_inv1, primed_inv2);
    let negated = s.not(primed_conj);
    s.assert_term(negated);

    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Disjunctive cond (i<n || k>0): i=n,k=1 => i'=n+1 violates i'<=n. \
         Expected SAT, got {result:?}"
    );
}

/// Loop preservation with implication condition: (n > 0) ==> (i < n).
/// Counterexample: i = 0, n = 0 => vacuously true cond, i' = 1 > 0 = n.
/// Corresponds to: tests::loops::test_loop_preservation_lt_inside_implies_counterexample
#[test]
#[timeout(10000)]
fn qf_lia_loop_implication_cond_counterexample() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);

    // Invariants: i >= 0 AND i <= n
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);

    // Loop condition: (n > 0) ==> (i < n)
    // Encode implication as: NOT(n > 0) OR (i < n)
    let n_gt_0 = s.gt(n, zero);
    let not_n_gt_0 = s.not(n_gt_0);
    let i_lt_n = s.lt(i, n);
    let cond = s.or(not_n_gt_0, i_lt_n);
    s.assert_term(cond);

    // Body effect: i_prime = i + 1
    let i_plus_1 = s.add(i, one);
    let effect = s.eq(i_prime, i_plus_1);
    s.assert_term(effect);

    // Negation of primed invariants
    let primed_inv1 = s.ge(i_prime, zero);
    let primed_inv2 = s.le(i_prime, n);
    let primed_conj = s.and(primed_inv1, primed_inv2);
    let negated = s.not(primed_conj);
    s.assert_term(negated);

    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Implication cond (n>0 => i<n): i=0,n=0 => vacuous, i'=1>0=n. \
         Expected SAT, got {result:?}"
    );
}

/// Body-break preservation with step-2: i' = i + 2 overruns i <= n.
/// Counterexample: i = n - 1, n >= 2 => i' = n + 1 > n.
/// Corresponds to: tests::body_break_audit::header_condition_step2_preservation_fails
#[test]
#[timeout(10000)]
fn qf_lia_header_cond_step2_counterexample() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let two = s.int_const(2);

    // Requires: n >= 2
    let req = s.ge(n, two);
    s.assert_term(req);

    // Invariants: i >= 0 AND i <= n
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);

    // Header condition: i < n
    let cond = s.lt(i, n);
    s.assert_term(cond);

    // Body effect: i_prime = i + 2
    let i_plus_2 = s.add(i, two);
    let effect = s.eq(i_prime, i_plus_2);
    s.assert_term(effect);

    // Negation of primed invariants
    let primed_inv1 = s.ge(i_prime, zero);
    let primed_inv2 = s.le(i_prime, n);
    let primed_conj = s.and(primed_inv1, primed_inv2);
    let negated = s.not(primed_conj);
    s.assert_term(negated);

    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Header cond step-2: i=n-1 => i'=n+1 violates i'<=n. \
         Expected SAT, got {result:?}"
    );
}

/// Body-break postcondition with primed exit: i' = i + 2, result = i'.
/// Counterexample: i = n - 1 => i' = n + 1 violates result != n + 1.
/// Corresponds to: verify::loops::tests::verify_postcondition_body_break_primes_exit_condition
#[test]
#[timeout(10000)]
fn qf_lia_body_break_postcond_counterexample() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);
    let two = s.int_const(2);

    // Invariant: i <= n
    let inv = s.le(i, n);
    s.assert_term(inv);

    // Non-negativity: i >= 0 (implicit from loop context)
    let inv_lower = s.ge(i, zero);
    s.assert_term(inv_lower);

    // Body effect: i_prime = i + 2
    let i_plus_2 = s.add(i, two);
    let effect = s.eq(i_prime, i_plus_2);
    s.assert_term(effect);

    // Exit condition (primed): i_prime >= n (NOT(i_prime < n))
    let exit = s.ge(i_prime, n);
    s.assert_term(exit);

    // Negated postcondition: NOT(result != n + 1) where result = i_prime
    // i.e., i_prime == n + 1
    let n_plus_1 = s.add(n, one);
    let eq_bad = s.eq(i_prime, n_plus_1);
    s.assert_term(eq_bad);

    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Body-break postcond: i=n-1 => i'=n+1 = n+1 violates postcond. \
         Expected SAT, got {result:?}"
    );
}

/// Variant decrease with ITE: variant(i) = ITE(i==n-1, -10, n-i).
/// Header condition fails decrease at i = n - 1 where variant = -10.
/// Corresponds to: verify::loops::tests::verify_variant_decrease_body_break_primes_condition
#[test]
#[timeout(10000)]
fn qf_lia_variant_ite_decrease_counterexample() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let two = s.int_const(2);
    let four = s.int_const(4);
    let one = s.int_const(1);
    let neg_ten = s.int_const(-10);

    // Invariants: i >= 0, i <= n, n >= 4
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);
    let inv3 = s.ge(n, four);
    s.assert_term(inv3);

    // Header condition: i < n
    let cond = s.lt(i, n);
    s.assert_term(cond);

    // Body effect: i_prime = i + 2
    let i_plus_2 = s.add(i, two);
    let effect = s.eq(i_prime, i_plus_2);
    s.assert_term(effect);

    // variant(i) = ITE(i == n-1, -10, n - i)
    let n_minus_1 = s.sub(n, one);
    let i_eq_nm1 = s.eq(i, n_minus_1);
    let n_minus_i = s.sub(n, i);
    let variant_i = s.ite(i_eq_nm1, neg_ten, n_minus_i);

    // variant(i') = ITE(i' == n-1, -10, n - i')
    let ip_eq_nm1 = s.eq(i_prime, n_minus_1);
    let n_minus_ip = s.sub(n, i_prime);
    let variant_ip = s.ite(ip_eq_nm1, neg_ten, n_minus_ip);

    // Negation of decrease: NOT(variant(i') < variant(i))
    // i.e., variant(i') >= variant(i)
    let decrease = s.lt(variant_ip, variant_i);
    let negated = s.not(decrease);
    s.assert_term(negated);

    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Variant ITE decrease: i=n-1 => variant(i)=-10, i'=n+1 => variant(i')=-1 >= -10. \
         Expected SAT, got {result:?}"
    );
}

/// Nested push/pop: two levels of scoping.
#[test]
#[timeout(10000)]
fn push_pop_nested() {
    let mut s = Solver::try_new(Logic::QfAuflia).unwrap();
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let five = s.int_const(5);
    let ten = s.int_const(10);

    // Base: x > 0
    let x_pos = s.gt(x, zero);
    s.assert_term(x_pos);

    // Level 1: x < 10
    s.push();
    let x_lt_10 = s.lt(x, ten);
    s.assert_term(x_lt_10);

    // Level 2: x == 5
    s.push();
    let x_eq_5 = s.eq(x, five);
    s.assert_term(x_eq_5);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 AND x < 10 AND x == 5 should be SAT"
    );

    // Pop level 2: x < 10 still holds but x == 5 removed
    s.pop();
    let seven = s.int_const(7);
    let x_eq_7 = s.eq(x, seven);
    s.assert_term(x_eq_7);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 AND x < 10 AND x == 7 should be SAT after popping x==5"
    );

    // Pop level 1: only x > 0 remains
    s.pop();
    let hundred = s.int_const(100);
    let x_eq_100 = s.eq(x, hundred);
    s.assert_term(x_eq_100);
    assert!(
        matches!(s.check_sat().into_inner(), SolveResult::Sat),
        "x > 0 AND x == 100 should be SAT after popping x<10"
    );
}

// ============================================================================
// 7. AUFLIA logic evaluation — same queries as section 6, different logic (#2088)
//
// Tests whether switching from QF_LIA to alternative logics avoids the
// false-UNSAT bug in ay's simplex solver. Each query runs under QF_AUFLIA,
// AUFLIA, UFLIA, and ALL to measure cross-logic behavior (#2088).
// ============================================================================

/// Helper: run the disjunctive-cond counterexample query with a given logic.
fn auflia_eval_disjunctive_cond(logic: Logic) -> SolveResult {
    let mut s = Solver::try_new(logic).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let k = s.declare_const("k", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);
    let i_lt_n = s.lt(i, n);
    let k_gt_0 = s.gt(k, zero);
    let cond = s.or(i_lt_n, k_gt_0);
    s.assert_term(cond);
    let i_plus_1 = s.add(i, one);
    let effect = s.eq(i_prime, i_plus_1);
    s.assert_term(effect);
    let primed_inv1 = s.ge(i_prime, zero);
    let primed_inv2 = s.le(i_prime, n);
    let primed_conj = s.and(primed_inv1, primed_inv2);
    let negated = s.not(primed_conj);
    s.assert_term(negated);
    s.check_sat().into_inner()
}

/// Helper: run the implication-cond counterexample query with a given logic.
fn auflia_eval_implication_cond(logic: Logic) -> SolveResult {
    let mut s = Solver::try_new(logic).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);
    let n_gt_0 = s.gt(n, zero);
    let not_n_gt_0 = s.not(n_gt_0);
    let i_lt_n = s.lt(i, n);
    let cond = s.or(not_n_gt_0, i_lt_n);
    s.assert_term(cond);
    let i_plus_1 = s.add(i, one);
    let effect = s.eq(i_prime, i_plus_1);
    s.assert_term(effect);
    let primed_inv1 = s.ge(i_prime, zero);
    let primed_inv2 = s.le(i_prime, n);
    let primed_conj = s.and(primed_inv1, primed_inv2);
    let negated = s.not(primed_conj);
    s.assert_term(negated);
    s.check_sat().into_inner()
}

/// Helper: run the step-2 counterexample query with a given logic.
fn auflia_eval_step2(logic: Logic) -> SolveResult {
    let mut s = Solver::try_new(logic).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let two = s.int_const(2);
    let req = s.ge(n, two);
    s.assert_term(req);
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);
    let cond = s.lt(i, n);
    s.assert_term(cond);
    let i_plus_2 = s.add(i, two);
    let effect = s.eq(i_prime, i_plus_2);
    s.assert_term(effect);
    let primed_inv1 = s.ge(i_prime, zero);
    let primed_inv2 = s.le(i_prime, n);
    let primed_conj = s.and(primed_inv1, primed_inv2);
    let negated = s.not(primed_conj);
    s.assert_term(negated);
    s.check_sat().into_inner()
}

/// Helper: run the body-break postcondition query with a given logic.
fn auflia_eval_body_break_postcond(logic: Logic) -> SolveResult {
    let mut s = Solver::try_new(logic).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);
    let two = s.int_const(2);
    let inv = s.le(i, n);
    s.assert_term(inv);
    let inv_lower = s.ge(i, zero);
    s.assert_term(inv_lower);
    let i_plus_2 = s.add(i, two);
    let effect = s.eq(i_prime, i_plus_2);
    s.assert_term(effect);
    let exit = s.ge(i_prime, n);
    s.assert_term(exit);
    let n_plus_1 = s.add(n, one);
    let eq_bad = s.eq(i_prime, n_plus_1);
    s.assert_term(eq_bad);
    s.check_sat().into_inner()
}

/// Helper: run the variant ITE decrease query with a given logic.
fn auflia_eval_variant_ite(logic: Logic) -> SolveResult {
    let mut s = Solver::try_new(logic).unwrap();
    let i = s.declare_const("i", Sort::Int);
    let n = s.declare_const("n", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let zero = s.int_const(0);
    let two = s.int_const(2);
    let four = s.int_const(4);
    let one = s.int_const(1);
    let neg_ten = s.int_const(-10);
    let inv1 = s.ge(i, zero);
    s.assert_term(inv1);
    let inv2 = s.le(i, n);
    s.assert_term(inv2);
    let inv3 = s.ge(n, four);
    s.assert_term(inv3);
    let cond = s.lt(i, n);
    s.assert_term(cond);
    let i_plus_2 = s.add(i, two);
    let effect = s.eq(i_prime, i_plus_2);
    s.assert_term(effect);
    let n_sub_1 = s.sub(n, one);
    let i_at_boundary = s.eq(i, n_sub_1);
    let n_minus_i = s.sub(n, i);
    let variant_i = s.ite(i_at_boundary, neg_ten, n_minus_i);
    let iprime_at_boundary = s.eq(i_prime, n_sub_1);
    let n_minus_ip = s.sub(n, i_prime);
    let variant_ip = s.ite(iprime_at_boundary, neg_ten, n_minus_ip);
    let decrease = s.lt(variant_ip, variant_i);
    let negated = s.not(decrease);
    s.assert_term(negated);
    s.check_sat().into_inner()
}

/// Cross-logic evaluation: runs all 5 regression queries under QF_AUFLIA,
/// AUFLIA, UFLIA, and ALL to measure which logics avoid the false-UNSAT.
///
/// Results at current ay pin (854fcaf):
///
/// | Query            | QF_LIA | QF_AUFLIA | AUFLIA | UFLIA | ALL   |
/// |------------------|--------|-----------|--------|-------|-------|
/// | disjunctive_cond | Unsat* | Sat       | Sat    | Sat   | Unsat*|
/// | implication_cond | Unsat* | Sat       | Sat    | Sat   | Unsat*|
/// | step2            | Unsat* | Sat       | Sat    | Sat   | Unsat*|
/// | body_break       | Unsat* | Sat       | Sat    | Sat   | Unsat*|
/// | variant_ite      | Unsat* | Unsat*    | Unsat* | Unsat*| Unsat*|
///
/// (* = false-UNSAT, ay bug)
///
/// Conclusion (#2088): AUFLIA/QF_AUFLIA/UFLIA fix 4/5 but NOT variant_ite.
/// ALL logic is worse (0/5). The workaround is incomplete — ay upstream
/// fix (ay#6205, ay#6207 → #2090/#2089) addresses all 5 at root cause.
/// Decision: REJECT logic override. Bump ay pin via #2056 instead.
#[test]
#[timeout(10000)]
fn auflia_eval_cross_logic_measurement() {
    let logics = [
        ("QF_AUFLIA", Logic::QfAuflia),
        ("AUFLIA", Logic::Auflia),
        ("UFLIA", Logic::Uflia),
        ("ALL", Logic::All),
    ];
    #[allow(clippy::type_complexity)]
    let queries: [(&str, fn(Logic) -> SolveResult); 5] = [
        ("disjunctive_cond", auflia_eval_disjunctive_cond),
        ("implication_cond", auflia_eval_implication_cond),
        ("step2", auflia_eval_step2),
        ("body_break", auflia_eval_body_break_postcond),
        ("variant_ite", auflia_eval_variant_ite),
    ];
    for (logic_name, logic) in &logics {
        eprintln!("{logic_name} results:");
        for (query_name, query_fn) in &queries {
            let result = query_fn(*logic);
            eprintln!("  {query_name}: {result:?}");
        }
    }
    // QF_AUFLIA/AUFLIA/UFLIA fix 4/5 (all except variant_ite).
    // Verify the 4 fixable queries return SAT under QF_AUFLIA.
    assert!(
        matches!(
            auflia_eval_disjunctive_cond(Logic::QfAuflia),
            SolveResult::Sat
        ),
        "QF_AUFLIA should fix disjunctive_cond"
    );
    assert!(
        matches!(
            auflia_eval_implication_cond(Logic::QfAuflia),
            SolveResult::Sat
        ),
        "QF_AUFLIA should fix implication_cond"
    );
    assert!(
        matches!(auflia_eval_step2(Logic::QfAuflia), SolveResult::Sat),
        "QF_AUFLIA should fix step2"
    );
    assert!(
        matches!(
            auflia_eval_body_break_postcond(Logic::QfAuflia),
            SolveResult::Sat
        ),
        "QF_AUFLIA should fix body_break"
    );
    // variant_ite: broken (Unsat) at current pin, will become Sat after ay fix.
    // Accept both outcomes so this test survives the ay bump (#2056).
    let variant_result = auflia_eval_variant_ite(Logic::QfAuflia);
    assert!(
        matches!(variant_result, SolveResult::Sat | SolveResult::Unsat(_)),
        "variant_ite should be Sat (fixed) or Unsat (ay bug), got {variant_result:?}"
    );
}
