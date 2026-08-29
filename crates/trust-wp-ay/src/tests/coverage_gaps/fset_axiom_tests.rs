// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for FSet interaction axioms (#2115).
//!
//! Each test negates an axiom conclusion and checks UNSAT, proving the
//! axiom holds in the solver's model. Follows the pattern in
//! `fmap_axiom_tests.rs`.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use crate::AYEncoder;

/// Peek-contains axiom: `!is_empty(s) ==> contains(s, peek(s))`.
///
/// For a non-empty set, peek returns an element that is in the set.
#[test]
#[timeout(30000)]
fn fset_peek_contains_nonempty() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let fset_is_empty = encoder.get_or_declare_spec_fn("fset_is_empty", &[Sort::Int], Sort::Bool);
    let fset_peek = encoder.get_or_declare_spec_fn("fset_peek", &[Sort::Int], Sort::Int);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);

    // Assume s is non-empty
    let is_empty_s = encoder.solver.apply(&fset_is_empty, &[s]);
    let not_empty = encoder.solver.not(is_empty_s);
    encoder.solver.assert_term(not_empty);

    // Negate: NOT contains(s, peek(s))
    let peek_s = encoder.solver.apply(&fset_peek, &[s]);
    let contains_peek = encoder.solver.apply(&fset_contains, &[s, peek_s]);
    let not_contains = encoder.solver.not(contains_peek);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT contains(s, peek(s)) with !is_empty(s) should be UNSAT, got: {result:?}"
    );
}

/// Insert-contains axiom: `contains(insert(s, x), x)`.
///
/// After inserting x, the set must contain x.
#[test]
#[timeout(30000)]
fn fset_insert_contains_same_elem() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let fset_insert =
        encoder.get_or_declare_spec_fn("fset_insert", &[Sort::Int, Sort::Int], Sort::Int);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);

    let inserted = encoder.solver.apply(&fset_insert, &[s, x]);

    // Negate: NOT contains(insert(s, x), x)
    let contains_x = encoder.solver.apply(&fset_contains, &[inserted, x]);
    let not_contains = encoder.solver.not(contains_x);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT contains(insert(s, x), x) should be UNSAT, got: {result:?}"
    );
}

/// Insert-frame axiom: `x != y ==> contains(insert(s, x), y) == contains(s, y)`.
///
/// Inserting x does not affect membership of any other element y.
#[test]
#[timeout(30000)]
fn fset_insert_frame_contains() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let fset_insert =
        encoder.get_or_declare_spec_fn("fset_insert", &[Sort::Int, Sort::Int], Sort::Int);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let y = encoder.solver.fresh_var("y", Sort::Int);

    // Assume x != y
    let x_eq_y = encoder.solver.eq(x, y);
    let x_neq_y = encoder.solver.not(x_eq_y);
    encoder.solver.assert_term(x_neq_y);

    let inserted = encoder.solver.apply(&fset_insert, &[s, x]);
    let contains_ins_y = encoder.solver.apply(&fset_contains, &[inserted, y]);
    let contains_s_y = encoder.solver.apply(&fset_contains, &[s, y]);

    // Negate frame: contains(insert(s,x), y) != contains(s, y)
    let eq = encoder.solver.iff(contains_ins_y, contains_s_y);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "frame violation should be UNSAT when x != y, got: {result:?}"
    );
}

/// Remove-contains-self axiom: `!contains(remove(s, x), x)`.
///
/// After removing x, the set must not contain x.
#[test]
#[timeout(30000)]
fn fset_remove_contains_self() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let fset_remove =
        encoder.get_or_declare_spec_fn("fset_remove", &[Sort::Int, Sort::Int], Sort::Int);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);

    let removed = encoder.solver.apply(&fset_remove, &[s, x]);

    // Negate: contains(remove(s, x), x) — should be false
    let contains_x = encoder.solver.apply(&fset_contains, &[removed, x]);
    encoder.solver.assert_term(contains_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "contains(remove(s, x), x) should be UNSAT, got: {result:?}"
    );
}

/// Remove-frame axiom: `x != y ==> contains(remove(s, x), y) == contains(s, y)`.
///
/// Removing x does not affect membership of any other element y.
#[test]
#[timeout(30000)]
fn fset_remove_frame_contains() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let fset_remove =
        encoder.get_or_declare_spec_fn("fset_remove", &[Sort::Int, Sort::Int], Sort::Int);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let y = encoder.solver.fresh_var("y", Sort::Int);

    // Assume x != y
    let x_eq_y = encoder.solver.eq(x, y);
    let x_neq_y = encoder.solver.not(x_eq_y);
    encoder.solver.assert_term(x_neq_y);

    let removed = encoder.solver.apply(&fset_remove, &[s, x]);
    let contains_rem_y = encoder.solver.apply(&fset_contains, &[removed, y]);
    let contains_s_y = encoder.solver.apply(&fset_contains, &[s, y]);

    // Negate frame: contains(remove(s,x), y) != contains(s, y)
    let eq = encoder.solver.iff(contains_rem_y, contains_s_y);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "frame violation should be UNSAT when x != y, got: {result:?}"
    );
}

// ── Proxy variable tests (#2116) ──
//
// In the loop preservation pipeline, `build_prime_substitutions` creates
// proxy variables (e.g., `result_prime`) and asserts equality with the
// collection operation result. If ay-dpll's E-matching is purely syntactic
// (not modulo E-graph), axiom triggers won't fire through proxy variables.
// These tests verify that FSet axioms work through proxy indirection.

/// Proxy variable test: does `fset_contains(proxy, x)` work when
/// `proxy = fset_insert(s, x)` is asserted as an equality?
///
/// Parallel to `fmap_insert_contains_through_proxy_variable` in fmap_axiom_tests.rs.
#[test]
#[timeout(30000)]
fn fset_insert_contains_through_proxy_variable() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_insert =
        encoder.get_or_declare_spec_fn("fset_insert", &[Sort::Int, Sort::Int], Sort::Int);
    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);

    // Create proxy variable: result_prime = fset_insert(s, x)
    let proxy = encoder.solver.fresh_var("result_prime", Sort::Int);
    let insert_term = encoder.solver.apply(&fset_insert, &[s, x]);
    let proxy_eq = encoder.solver.eq(proxy, insert_term);
    encoder.solver.assert_term(proxy_eq);

    // Query: fset_contains(result_prime, x) should be true
    let contains_proxy = encoder.solver.apply(&fset_contains, &[proxy, x]);
    let not_contains = encoder.solver.not(contains_proxy);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    eprintln!("[fset-proxy-test] fset_contains(proxy, x) through equality: {result:?}");
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_contains(result_prime, x) should be UNSAT when result_prime = fset_insert(s, x), \
         got: {result:?}. If Sat/Unknown, E-matching doesn't fire through proxy variables."
    );
}

/// Proxy variable frame test: does `fset_contains(proxy, y)` correctly equal
/// `fset_contains(s, y)` when `proxy = fset_insert(s, x)` and `x != y`?
///
/// Parallel to `fmap_insert_frame_lookup_through_proxy_variable` in fmap_axiom_tests.rs.
/// Tests the frame axiom trigger through a proxy variable — critical for loop
/// preservation where primed invariants reference proxy variables.
#[test]
#[timeout(30000)]
fn fset_insert_frame_contains_through_proxy_variable() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_insert =
        encoder.get_or_declare_spec_fn("fset_insert", &[Sort::Int, Sort::Int], Sort::Int);
    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let y = encoder.solver.fresh_var("y", Sort::Int);

    // x != y
    let eq_x_y = encoder.solver.eq(x, y);
    let neq = encoder.solver.not(eq_x_y);
    encoder.solver.assert_term(neq);

    // Proxy: result_prime = fset_insert(s, x)
    let proxy = encoder.solver.fresh_var("result_prime", Sort::Int);
    let insert_term = encoder.solver.apply(&fset_insert, &[s, x]);
    let proxy_eq = encoder.solver.eq(proxy, insert_term);
    encoder.solver.assert_term(proxy_eq);

    // Query: fset_contains(result_prime, y) == fset_contains(s, y)
    let contains_proxy_y = encoder.solver.apply(&fset_contains, &[proxy, y]);
    let contains_s_y = encoder.solver.apply(&fset_contains, &[s, y]);
    let frame_eq = encoder.solver.iff(contains_proxy_y, contains_s_y);
    let not_frame = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(not_frame);

    let result = encoder.check_sat();
    eprintln!("[fset-proxy-frame-test] frame through proxy: {result:?}");
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset frame through proxy should be UNSAT when x != y, got: {result:?}. \
         If Sat/Unknown, E-matching frame trigger doesn't fire through proxy variables."
    );
}

/// Proxy variable remove test: does `fset_contains(proxy, x)` correctly
/// return false when `proxy = fset_remove(s, x)`?
///
/// Tests the remove-contains-self axiom through a proxy variable.
#[test]
#[timeout(30000)]
fn fset_remove_contains_through_proxy_variable() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fset_remove =
        encoder.get_or_declare_spec_fn("fset_remove", &[Sort::Int, Sort::Int], Sort::Int);
    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.fresh_var("x", Sort::Int);

    // Proxy: result_prime = fset_remove(s, x)
    let proxy = encoder.solver.fresh_var("result_prime", Sort::Int);
    let remove_term = encoder.solver.apply(&fset_remove, &[s, x]);
    let proxy_eq = encoder.solver.eq(proxy, remove_term);
    encoder.solver.assert_term(proxy_eq);

    // Query: fset_contains(result_prime, x) should be false
    let contains_proxy = encoder.solver.apply(&fset_contains, &[proxy, x]);
    encoder.solver.assert_term(contains_proxy);

    let result = encoder.check_sat();
    eprintln!("[fset-proxy-remove-test] contains(proxy, x) after remove: {result:?}");
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_contains(result_prime, x) should be UNSAT when result_prime = fset_remove(s, x), \
         got: {result:?}. If Sat/Unknown, E-matching doesn't fire through proxy variables."
    );
}
