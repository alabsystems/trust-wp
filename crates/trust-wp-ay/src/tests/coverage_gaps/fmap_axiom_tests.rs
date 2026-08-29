// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use crate::AYEncoder;

/// Canonical FMap sort for tests — matches `fmap_sort()` in sort_inference.rs.
fn fmap_sort() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

#[test]
#[timeout(30000)]
fn fmap_axioms_skip_non_int_insert_signature_without_panic() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();
    let perm_cell = Sort::Uninterpreted("PermCell".to_string());
    let seq_int = Sort::Seq(Box::new(Sort::Int));

    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), perm_cell.clone(), seq_int.clone()],
        fmap.clone(),
    );
    let fmap_contains = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), perm_cell.clone()],
        Sort::Bool,
    );

    encoder.assert_fmap_axioms();

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", perm_cell);
    let v = encoder.solver.fresh_var("v", seq_int);
    let inserted = encoder.solver.apply(&fmap_insert, &[m, k, v]);
    let contains = encoder.solver.apply(&fmap_contains, &[inserted, k]);

    assert_eq!(encoder.solver.get_sort(contains), Sort::Bool);
}

/// Insert-contains axiom: `fmap_contains(fmap_insert(m, k, v), k)` is true.
///
/// After inserting key k with value v, the map must contain k.
/// Without the insert-contains axiom, the solver has no way to derive
/// this relationship and would return Unknown or Sat (wrong).
#[test]
#[timeout(30000)]
fn fmap_insert_contains_same_key() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    // Declare UFs with FMap sort for map parameters (#2059)
    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_contains =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap.clone(), Sort::Int], Sort::Bool);

    // Assert axioms
    encoder.assert_fmap_axioms();

    // Setup: m is a map (FMap sort), k is a key, v is a value
    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // fmap_insert(m, k, v)
    let inserted = encoder.solver.apply(&fmap_insert, &[m, k, v]);

    // Negate the axiom conclusion: NOT fmap_contains(fmap_insert(m, k, v), k)
    let contains_k = encoder.solver.apply(&fmap_contains, &[inserted, k]);
    let not_contains = encoder.solver.not(contains_k);
    encoder.solver.assert_term(not_contains);

    // Should be UNSAT — the axiom guarantees contains is true
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT fmap_contains(fmap_insert(m, k, v), k) should be UNSAT, got: {result:?}"
    );
}

/// Insert-lookup axiom: `fmap_lookup(fmap_insert(m, k, v), k) == v`.
///
/// After inserting (k, v), looking up k returns v.
#[test]
#[timeout(30000)]
fn fmap_insert_lookup_same_key() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_lookup =
        encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);

    encoder.assert_fmap_axioms();

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    let inserted = encoder.solver.apply(&fmap_insert, &[m, k, v]);
    let lookup_k = encoder.solver.apply(&fmap_lookup, &[inserted, k]);

    // Negate: fmap_lookup(fmap_insert(m, k, v), k) != v
    let eq_lookup_v = encoder.solver.eq(lookup_k, v);
    let neq = encoder.solver.not(eq_lookup_v);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_lookup(fmap_insert(m, k, v), k) != v should be UNSAT, got: {result:?}"
    );
}

/// Frame axiom: insert on key k1 does not affect lookup at key k2 (k1 != k2).
///
/// `k1 != k2 ==> fmap_lookup(fmap_insert(m, k1, v), k2) == fmap_lookup(m, k2)`
#[test]
#[timeout(30000)]
fn fmap_insert_frame_lookup() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_lookup =
        encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);

    encoder.assert_fmap_axioms();

    let m = encoder.solver.fresh_var("m", fmap);
    let k1 = encoder.solver.fresh_var("k1", Sort::Int);
    let k2 = encoder.solver.fresh_var("k2", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // Assume k1 != k2
    let eq_k1_k2 = encoder.solver.eq(k1, k2);
    let k1_neq_k2 = encoder.solver.not(eq_k1_k2);
    encoder.solver.assert_term(k1_neq_k2);

    let inserted = encoder.solver.apply(&fmap_insert, &[m, k1, v]);
    let lookup_ins_k2 = encoder.solver.apply(&fmap_lookup, &[inserted, k2]);
    let lookup_m_k2 = encoder.solver.apply(&fmap_lookup, &[m, k2]);

    // Negate frame: fmap_lookup(insert(m,k1,v), k2) != fmap_lookup(m, k2)
    let eq_lookups = encoder.solver.eq(lookup_ins_k2, lookup_m_k2);
    let neq = encoder.solver.not(eq_lookups);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "frame violation should be UNSAT when k1 != k2, got: {result:?}"
    );
}

/// Len non-negativity: `fmap_len(m) >= 0` for any map m.
#[test]
#[timeout(30000)]
fn fmap_len_nonneg() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_len =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    // Need to declare fmap_insert to trigger axiom assertion
    let _fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );

    encoder.assert_fmap_axioms();

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.solver.apply(&fmap_len, &[m]);
    let zero = encoder.solver.int_const(0);

    // Assert len(m) < 0 — should be UNSAT
    let len_neg = encoder.solver.lt(len_m, zero);
    encoder.solver.assert_term(len_neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) < 0 should be UNSAT, got: {result:?}"
    );
}

/// Concrete scenario: insert two different keys, lookup both.
///
/// Models: `m2 = insert(insert(empty, 1, 10), 2, 20)`
/// Verifies: `lookup(m2, 1) == 10 && lookup(m2, 2) == 20`
#[test]
#[timeout(30000)]
fn fmap_two_inserts_both_lookups() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_lookup =
        encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);

    encoder.assert_fmap_axioms();

    let empty = encoder.solver.fresh_var("empty", fmap);
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let ten = encoder.solver.int_const(10);
    let twenty = encoder.solver.int_const(20);

    // m1 = insert(empty, 1, 10)
    let m1 = encoder.solver.apply(&fmap_insert, &[empty, one, ten]);
    // m2 = insert(m1, 2, 20)
    let m2 = encoder.solver.apply(&fmap_insert, &[m1, two, twenty]);

    // lookup(m2, 1) should be 10 (frame: inserting key 2 doesn't affect key 1)
    let lookup_1 = encoder.solver.apply(&fmap_lookup, &[m2, one]);
    // lookup(m2, 2) should be 20 (direct: just inserted)
    let lookup_2 = encoder.solver.apply(&fmap_lookup, &[m2, two]);

    // Negate: NOT (lookup(m2, 1) == 10 AND lookup(m2, 2) == 20)
    let eq_10 = encoder.solver.eq(lookup_1, ten);
    let eq_20 = encoder.solver.eq(lookup_2, twenty);
    let both = encoder.solver.and(eq_10, eq_20);
    let negated = encoder.solver.not(both);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "two-insert lookup chain should verify (UNSAT negation), got: {result:?}"
    );
}

/// Proxy variable test: does `fmap_contains(proxy, k)` work when
/// `proxy = fmap_insert(m, k, v)` is asserted as an equality?
///
/// In the loop preservation pipeline, `build_prime_substitutions` creates
/// a proxy variable `result_prime` and asserts `result_prime = fmap_insert(m, k, v)`.
/// The primed invariant then uses `fmap_contains(result_prime, k)`.
/// If ay-dpll's E-matching only does syntactic trigger matching (not modulo
/// E-graph), the insert-contains axiom trigger `fmap_insert(m, k, v)` won't
/// match through the proxy, causing the axiom not to fire. (#2116)
#[test]
#[timeout(30000)]
fn fmap_insert_contains_through_proxy_variable() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_contains =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap.clone(), Sort::Int], Sort::Bool);

    encoder.assert_fmap_axioms();

    let m = encoder.solver.fresh_var("m", fmap.clone());
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // Create proxy variable: result_prime = fmap_insert(m, k, v)
    let proxy = encoder.solver.fresh_var("result_prime", fmap);
    let insert_term = encoder.solver.apply(&fmap_insert, &[m, k, v]);
    let proxy_eq = encoder.solver.eq(proxy, insert_term);
    encoder.solver.assert_term(proxy_eq);

    // Query: fmap_contains(result_prime, k) should be true
    // But the trigger for insert-contains axiom is fmap_insert(m, k, v),
    // and the contains call uses the proxy variable, not the insert term.
    let contains_proxy = encoder.solver.apply(&fmap_contains, &[proxy, k]);
    let not_contains = encoder.solver.not(contains_proxy);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    eprintln!("[proxy-test] fmap_contains(proxy, k) through equality: {result:?}");
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_contains(result_prime, k) should be UNSAT when result_prime = fmap_insert(m, k, v), \
         got: {result:?}. If Sat/Unknown, E-matching doesn't fire through proxy variables."
    );
}

/// Proxy variable frame test: does `fmap_lookup(proxy, k2)` correctly equal
/// `fmap_lookup(m, k2)` when `proxy = fmap_insert(m, k1, v)` and `k1 != k2`?
///
/// This tests the frame axiom trigger `fmap_lookup(fmap_insert(m, k1, v), k2)`
/// through a proxy variable. This is the critical axiom for the `complicated_identity`
/// preservation step where the primed invariant uses `fmap_lookup(result_prime, k)`. (#2116)
#[test]
#[timeout(30000)]
fn fmap_insert_frame_lookup_through_proxy_variable() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_lookup =
        encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);

    encoder.assert_fmap_axioms();

    let m = encoder.solver.fresh_var("m", fmap.clone());
    let k1 = encoder.solver.fresh_var("k1", Sort::Int);
    let k2 = encoder.solver.fresh_var("k2", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // k1 != k2
    let eq_k1_k2 = encoder.solver.eq(k1, k2);
    let neq = encoder.solver.not(eq_k1_k2);
    encoder.solver.assert_term(neq);

    // Proxy: result_prime = fmap_insert(m, k1, v)
    let proxy = encoder.solver.fresh_var("result_prime", fmap);
    let insert_term = encoder.solver.apply(&fmap_insert, &[m, k1, v]);
    let proxy_eq = encoder.solver.eq(proxy, insert_term);
    encoder.solver.assert_term(proxy_eq);

    // Query: fmap_lookup(result_prime, k2) == fmap_lookup(m, k2)
    // Frame axiom should give this, but trigger needs fmap_lookup(fmap_insert(...), k2)
    let lookup_proxy_k2 = encoder.solver.apply(&fmap_lookup, &[proxy, k2]);
    let lookup_m_k2 = encoder.solver.apply(&fmap_lookup, &[m, k2]);
    let frame_eq = encoder.solver.eq(lookup_proxy_k2, lookup_m_k2);
    let not_frame = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(not_frame);

    let result = encoder.check_sat();
    eprintln!("[proxy-frame-test] frame through proxy: {result:?}");
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "frame lookup through proxy should be UNSAT when k1 != k2, got: {result:?}. \
         If Sat/Unknown, E-matching frame trigger doesn't fire through proxy variables."
    );
}

/// Empty FMap contains no keys: `fmap_contains(fmap_empty, k)` is false for any k.
///
/// Tests the empty-contains axiom added in #2549. Before this axiom,
/// `fmap_empty` was a bare constant with no semantic connection to
/// `fmap_contains`, so the solver couldn't derive that an empty map
/// has no keys.
#[test]
#[timeout(30000)]
fn fmap_empty_contains_no_keys() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_contains =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap.clone(), Sort::Int], Sort::Bool);

    // Declare fmap_insert so axiom assertion doesn't early-return
    let _fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );

    encoder.assert_fmap_axioms();

    // fmap_empty is a canonical constant declared by the axiom system
    let fmap_empty = encoder.solver.declare_const("fmap_empty", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);

    // Assert: fmap_contains(fmap_empty, k) — should be UNSAT
    let contains_empty_k = encoder.solver.apply(&fmap_contains, &[fmap_empty, k]);
    encoder.solver.assert_term(contains_empty_k);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_contains(fmap_empty, k) should be UNSAT via empty-contains axiom (#2549), got: {result:?}"
    );
}

/// Empty FMap has length zero: `fmap_len(fmap_empty) == 0`.
///
/// Tests the empty-len axiom added in #2549.
#[test]
#[timeout(30000)]
fn fmap_empty_len_is_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let fmap_len =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    // Declare fmap_insert so axiom assertion path includes empty axioms
    let _fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );

    encoder.assert_fmap_axioms();

    let fmap_empty = encoder.solver.declare_const("fmap_empty", fmap);
    let len_empty = encoder.solver.apply(&fmap_len, &[fmap_empty]);
    let zero = encoder.solver.int_const(0);

    // Assert: fmap_len(fmap_empty) != 0 — should be UNSAT
    let len_eq_zero = encoder.solver.eq(len_empty, zero);
    let not_zero = encoder.solver.not(len_eq_zero);
    encoder.solver.assert_term(not_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(fmap_empty) != 0 should be UNSAT via empty-len axiom (#2549), got: {result:?}"
    );
}
