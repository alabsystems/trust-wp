// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `AYEncoder::try_decompose_mut_ref_equality` with zero prior
//! test coverage. The existing inline test in `mut_ref_sort.rs` only covers
//! `bind_whole_mut_ref`; this module covers the decomposition path.
//!
//! Targets:
//! - `try_decompose_mut_ref_equality`: None path (non-MutRef sorts, mismatched sorts)
//! - `try_decompose_mut_ref_equality`: Some path (MutRef decomposition produces
//!   conjunction of component equalities)

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use crate::encoder::AYEncoder;

// ── Helper ──────────────────────────────────────────────────────────

fn mutref_int_sort(encoder: &mut AYEncoder) -> Sort {
    encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)))
}

// ── None paths (early returns) ──────────────────────────────────────

/// Two Int-sorted terms are not MutRef → returns None.
#[test]
#[timeout(30000)]
fn test_decompose_int_terms_returns_none() {
    let mut encoder = AYEncoder::new_all();
    let a = encoder
        .get_or_declare_var("a", Sort::Int)
        .expect("a should declare");
    let b = encoder
        .get_or_declare_var("b", Sort::Int)
        .expect("b should declare");

    let result = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error");
    assert!(result.is_none(), "Int terms should return None");
}

/// Two Bool-sorted terms are not MutRef → returns None.
#[test]
#[timeout(30000)]
fn test_decompose_bool_terms_returns_none() {
    let mut encoder = AYEncoder::new_all();
    let a = encoder
        .get_or_declare_var("a", Sort::Bool)
        .expect("a should declare");
    let b = encoder
        .get_or_declare_var("b", Sort::Bool)
        .expect("b should declare");

    let result = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error");
    assert!(result.is_none(), "Bool terms should return None");
}

/// Mismatched sorts (Int vs MutRef) → returns None.
#[test]
#[timeout(30000)]
fn test_decompose_mismatched_sorts_returns_none() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let a = encoder
        .get_or_declare_var("a", whole_sort)
        .expect("a should declare");
    let b = encoder
        .get_or_declare_var("b", Sort::Int)
        .expect("b should declare");

    let result = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error");
    assert!(result.is_none(), "mismatched sorts should return None");
}

/// Uninterpreted sort that is NOT a MutRef encoding → returns None.
#[test]
#[timeout(30000)]
fn test_decompose_uninterpreted_non_mutref_returns_none() {
    let mut encoder = AYEncoder::new_all();
    let custom = Sort::Uninterpreted("MyType".to_string());
    let a = encoder
        .get_or_declare_var("a", custom.clone())
        .expect("a should declare");
    let b = encoder
        .get_or_declare_var("b", custom)
        .expect("b should declare");

    let result = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error");
    assert!(
        result.is_none(),
        "non-MutRef Uninterpreted sort should return None"
    );
}

// ── Some path (MutRef decomposition) ────────────────────────────────

/// Two MutRef<Int> terms produce a decomposed equality term.
#[test]
#[timeout(30000)]
fn test_decompose_mutref_int_returns_some() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let a = encoder
        .get_or_declare_var("a", whole_sort.clone())
        .expect("a should declare");
    let b = encoder
        .get_or_declare_var("b", whole_sort)
        .expect("b should declare");

    let result = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error");
    assert!(result.is_some(), "MutRef<Int> terms should decompose");
}

/// Decomposed MutRef equality is SAT when components are unconstrained.
#[test]
#[timeout(30000)]
fn test_decompose_mutref_unconstrained_is_sat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let a = encoder
        .get_or_declare_var("a", whole_sort.clone())
        .expect("a should declare");
    let b = encoder
        .get_or_declare_var("b", whole_sort)
        .expect("b should declare");

    let decomposed = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error")
        .expect("should return Some for MutRef");

    encoder.assert_term(decomposed);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "unconstrained MutRef decomposed equality should be SAT"
    );
}

/// When bound components are equal, the decomposed equality holds.
///
/// Setup: bind lhs and rhs with identical current/final/id, assert the
/// decomposed equality, check SAT.
#[test]
#[timeout(30000)]
fn test_decompose_equal_bound_components_sat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let inner_sort = Sort::Int;

    let lhs = encoder
        .get_or_declare_var("lhs", whole_sort.clone())
        .expect("lhs");
    let rhs = encoder
        .get_or_declare_var("rhs", whole_sort.clone())
        .expect("rhs");

    let shared_current = encoder
        .get_or_declare_var("c", inner_sort.clone())
        .expect("c");
    let shared_final = encoder
        .get_or_declare_var("f", inner_sort.clone())
        .expect("f");
    let shared_id = encoder.get_or_declare_var("id", Sort::Int).expect("id");

    encoder
        .bind_whole_mut_ref(
            &whole_sort,
            &inner_sort,
            lhs,
            shared_current,
            shared_final,
            shared_id,
        )
        .expect("bind lhs");
    encoder
        .bind_whole_mut_ref(
            &whole_sort,
            &inner_sort,
            rhs,
            shared_current,
            shared_final,
            shared_id,
        )
        .expect("bind rhs");

    let decomposed = encoder
        .try_decompose_mut_ref_equality(lhs, rhs)
        .expect("should not error")
        .expect("should decompose");

    encoder.assert_term(decomposed);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "equal components should make decomposed equality SAT"
    );
}

/// When bound components differ, the decomposed equality is refutable.
///
/// Setup: bind lhs and rhs with DIFFERENT current values, assert the
/// decomposed equality, check UNSAT (components disagree → conjunction false).
#[test]
#[timeout(30000)]
fn test_decompose_different_components_unsat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let inner_sort = Sort::Int;

    let lhs = encoder
        .get_or_declare_var("lhs", whole_sort.clone())
        .expect("lhs");
    let rhs = encoder
        .get_or_declare_var("rhs", whole_sort.clone())
        .expect("rhs");

    let c1 = encoder.solver.int_const(1);
    let c2 = encoder.solver.int_const(2);
    let shared_final = encoder
        .get_or_declare_var("f", inner_sort.clone())
        .expect("f");
    let shared_id = encoder.get_or_declare_var("id", Sort::Int).expect("id");

    encoder
        .bind_whole_mut_ref(&whole_sort, &inner_sort, lhs, c1, shared_final, shared_id)
        .expect("bind lhs");
    encoder
        .bind_whole_mut_ref(&whole_sort, &inner_sort, rhs, c2, shared_final, shared_id)
        .expect("bind rhs");

    let decomposed = encoder
        .try_decompose_mut_ref_equality(lhs, rhs)
        .expect("should not error")
        .expect("should decompose");

    // The decomposed equality requires current_eq && final_eq && id_eq.
    // current values differ (1 != 2), so the conjunction should be false.
    encoder.assert_term(decomposed);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "different current components should make decomposed equality UNSAT"
    );
}

/// When final components differ, the decomposed equality is refutable.
///
/// This isolates the `final_eq` conjunct so a regression that drops the final
/// selector equality cannot slip through the current-only mismatch test.
#[test]
#[timeout(30000)]
fn test_decompose_different_final_components_unsat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let inner_sort = Sort::Int;

    let lhs = encoder
        .get_or_declare_var("lhs", whole_sort.clone())
        .expect("lhs");
    let rhs = encoder
        .get_or_declare_var("rhs", whole_sort.clone())
        .expect("rhs");

    let shared_current = encoder
        .get_or_declare_var("c", inner_sort.clone())
        .expect("c");
    let f1 = encoder.solver.int_const(1);
    let f2 = encoder.solver.int_const(2);
    let shared_id = encoder.get_or_declare_var("id", Sort::Int).expect("id");

    encoder
        .bind_whole_mut_ref(&whole_sort, &inner_sort, lhs, shared_current, f1, shared_id)
        .expect("bind lhs");
    encoder
        .bind_whole_mut_ref(&whole_sort, &inner_sort, rhs, shared_current, f2, shared_id)
        .expect("bind rhs");

    let decomposed = encoder
        .try_decompose_mut_ref_equality(lhs, rhs)
        .expect("should not error")
        .expect("should decompose");

    encoder.assert_term(decomposed);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "different final components should make decomposed equality UNSAT"
    );
}

/// When ids differ, the decomposed equality is refutable.
///
/// This isolates the `id_eq` conjunct so the borrow-id component remains part
/// of MutRef equality decomposition.
#[test]
#[timeout(30000)]
fn test_decompose_different_ids_unsat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let inner_sort = Sort::Int;

    let lhs = encoder
        .get_or_declare_var("lhs", whole_sort.clone())
        .expect("lhs");
    let rhs = encoder
        .get_or_declare_var("rhs", whole_sort.clone())
        .expect("rhs");

    let shared_current = encoder
        .get_or_declare_var("c", inner_sort.clone())
        .expect("c");
    let shared_final = encoder
        .get_or_declare_var("f", inner_sort.clone())
        .expect("f");
    let id1 = encoder.solver.int_const(1);
    let id2 = encoder.solver.int_const(2);

    encoder
        .bind_whole_mut_ref(
            &whole_sort,
            &inner_sort,
            lhs,
            shared_current,
            shared_final,
            id1,
        )
        .expect("bind lhs");
    encoder
        .bind_whole_mut_ref(
            &whole_sort,
            &inner_sort,
            rhs,
            shared_current,
            shared_final,
            id2,
        )
        .expect("bind rhs");

    let decomposed = encoder
        .try_decompose_mut_ref_equality(lhs, rhs)
        .expect("should not error")
        .expect("should decompose");

    encoder.assert_term(decomposed);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "different ids should make decomposed equality UNSAT"
    );
}

/// Negating the decomposed equality when components are equal is UNSAT.
///
/// This is the complement of the `bind_whole_mut_ref` inline test: that test
/// proves bind implies whole equality; this proves decompose produces an
/// equivalent conjunction that is also forced true.
#[test]
#[timeout(30000)]
fn test_decompose_negated_with_equal_components_unsat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = mutref_int_sort(&mut encoder);
    let inner_sort = Sort::Int;

    let lhs = encoder
        .get_or_declare_var("lhs", whole_sort.clone())
        .expect("lhs");
    let rhs = encoder
        .get_or_declare_var("rhs", whole_sort.clone())
        .expect("rhs");

    let shared_current = encoder
        .get_or_declare_var("c", inner_sort.clone())
        .expect("c");
    let shared_final = encoder
        .get_or_declare_var("f", inner_sort.clone())
        .expect("f");
    let shared_id = encoder.get_or_declare_var("id", Sort::Int).expect("id");

    encoder
        .bind_whole_mut_ref(
            &whole_sort,
            &inner_sort,
            lhs,
            shared_current,
            shared_final,
            shared_id,
        )
        .expect("bind lhs");
    encoder
        .bind_whole_mut_ref(
            &whole_sort,
            &inner_sort,
            rhs,
            shared_current,
            shared_final,
            shared_id,
        )
        .expect("bind rhs");

    let decomposed = encoder
        .try_decompose_mut_ref_equality(lhs, rhs)
        .expect("should not error")
        .expect("should decompose");

    let negated = encoder.solver.not(decomposed);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negating decomposed equality of equal-bound MutRefs should be UNSAT"
    );
}

/// MutRef<Bool> decomposition also works (different inner sort).
#[test]
#[timeout(30000)]
fn test_decompose_mutref_bool_returns_some() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Bool)));
    let a = encoder
        .get_or_declare_var("a", whole_sort.clone())
        .expect("a");
    let b = encoder.get_or_declare_var("b", whole_sort).expect("b");

    let result = encoder
        .try_decompose_mut_ref_equality(a, b)
        .expect("should not error");
    assert!(result.is_some(), "MutRef<Bool> should decompose");
}
