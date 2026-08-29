// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic round-trip tests for FMap method-call dispatch (#2514).
//!
//! These tests bridge the gap between:
//! - **Dispatch tests** (`fmap_method_tests.rs`): verify `encode_pure` routes to
//!   the correct UF, but only check UF consistency (UNSAT dual), not axiom semantics.
//! - **Axiom tests** (`fmap_axiom_tests.rs`): verify axioms hold, but use manually
//!   declared UFs rather than going through `encode_pure` dispatch.
//!
//! Round-trip tests here go through `encode_pure` (dispatch layer) AND assert axioms,
//! proving that the UFs produced by dispatch are correctly connected by axiom reasoning.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::super::{super::*, helpers::*};

fn fmap_sort() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

// ── Insert-then-lookup: fmap_lookup(fmap_insert(m, k, v), k) == v ──

/// Encode `m.insert(1, 42)` via encode_pure, then verify via axiom that
/// `fmap_lookup(result, 1) == 42`.
///
/// This is the encode_pure-level semantic proof that the axiom-level test
/// `fmap_insert_lookup_same_key` exercises at the UF level. The difference:
/// here the UFs are declared by the dispatch pipeline, not manually.
#[test]
#[timeout(30000)]
fn fmap_insert_then_lookup_same_key_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // FMap-annotated variable ensures dispatch routes to fmap_insert
    let m = var_with_sort("m", ExprSort::FMap);
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);

    let insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("m.insert(1,42) should encode via fmap dispatch");

    // Declare fmap_lookup BEFORE asserting axioms — assert_fmap_axioms only
    // links UFs that are already declared (conditional axiom bodies).
    let fmap = fmap_sort();
    let fmap_lookup = encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap, Sort::Int], Sort::Int);

    // Assert FMap axioms — now insert-lookup axiom body is included
    encoder.assert_fmap_axioms();

    let one = encoder.solver.int_const(1);
    let lookup_result = encoder.solver.apply(&fmap_lookup, &[insert_term, one]);

    // Negate: lookup(insert(m,1,42), 1) != 42
    let forty_two = encoder.solver.int_const(42);
    let eq = encoder.solver.eq(lookup_result, forty_two);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_lookup(fmap_insert(m,1,42), 1) != 42 should be UNSAT via axiom, got: {result:?}"
    );
}

// ── Insert-then-contains: fmap_contains(fmap_insert(m, k, v), k) ──

/// Encode `m.insert(1, 42)` via encode_pure, then verify via axiom that
/// `fmap_contains(result, 1)` is true.
#[test]
#[timeout(30000)]
fn fmap_insert_then_contains_same_key_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let m = var_with_sort("m", ExprSort::FMap);
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);

    let insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("m.insert(1,42) should encode via fmap dispatch");

    // Declare fmap_contains before axiom assertion
    let fmap = fmap_sort();
    let fmap_contains =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap, Sort::Int], Sort::Bool);

    encoder.assert_fmap_axioms();

    let one = encoder.solver.int_const(1);
    let contains_result = encoder.solver.apply(&fmap_contains, &[insert_term, one]);

    // Negate: NOT contains(insert(m,1,42), 1) — axiom says this is true
    let not_contains = encoder.solver.not(contains_result);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT fmap_contains(fmap_insert(m,1,42), 1) should be UNSAT via axiom, got: {result:?}"
    );
}

// ── Into-seq membership: fmap_insert(...).into_seq().contains((k, v)) ──

/// Encode `m.insert(1, 42).into_seq().contains((1, 42))` via dispatch and
/// verify the canonical map-to-sequence witness axioms.
#[test]
#[timeout(30000)]
fn fmap_into_seq_contains_inserted_pair_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fmap = fmap_sort();
    let _ = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let _ = encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);
    let _ = encoder.get_or_declare_spec_fn(
        "fmap_into_seq",
        std::slice::from_ref(&fmap),
        Sort::seq(Sort::Int),
    );
    let _ = encoder.ensure_seq_theory();

    let m = var_with_sort("m", ExprSort::FMap);
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);
    let into_seq_expr = method_call(insert_expr.clone(), "into_seq", vec![]);
    let map_contains_expr = method_call(insert_expr.clone(), "contains", vec![int(1)]);
    let lookup_expr = method_call(insert_expr.clone(), "lookup", vec![int(1)]);

    let tuple2_name = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);
    let pair_expr = logic_fn_call(&tuple2_name, vec![int(1), int(42)]);
    let contains_expr = method_call(into_seq_expr, "contains", vec![pair_expr]);
    let contains_term = encoder
        .encode_pure(&contains_expr)
        .expect("insert(...).into_seq().contains((1,42)) should encode");
    let map_contains_term = encoder
        .encode_pure(&map_contains_expr)
        .expect("insert(...).contains(1) should encode");
    let lookup_term = encoder
        .encode_pure(&lookup_expr)
        .expect("insert(...).lookup(1) should encode");

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "nested insert(...).contains(...) should route to fmap_contains; got {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "insert(...).lookup(...) should route to fmap_lookup; got {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    encoder.assert_fmap_axioms();

    let forty_two = encoder.solver.int_const(42);
    encoder.solver.assert_term(map_contains_term);
    let lookup_eq = encoder.solver.eq(lookup_term, forty_two);
    encoder.solver.assert_term(lookup_eq);

    let not_contains = encoder.solver.not(contains_term);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT fmap.insert(1,42).into_seq().contains((1,42)) should be UNSAT via witness axiom, got: {result:?}"
    );
}

// ── Insert-frame-lookup: k1 != k2 ==> lookup(insert(m,k1,v),k2) == lookup(m,k2) ──

/// Encode two insert+lookup operations via encode_pure and verify the
/// frame axiom through the dispatch pipeline.
#[test]
#[timeout(30000)]
fn fmap_insert_frame_lookup_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode m.insert(1, 42) via dispatch
    let m = var_with_sort("m", ExprSort::FMap);
    let insert_expr = method_call(m.clone(), "insert", vec![int(1), int(42)]);
    let insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("m.insert(1,42) should encode");

    // Also encode m.get(2) via dispatch — this will use fmap_lookup
    let get_m_2 = method_call(m, "get", vec![int(2)]);
    let lookup_m_2 = encoder
        .encode_pure(&get_m_2)
        .expect("m.get(2) should encode");

    encoder.assert_fmap_axioms();

    // lookup(insert(m,1,42), 2) via the declared fmap_lookup UF
    let fmap = fmap_sort();
    let fmap_lookup = encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap, Sort::Int], Sort::Int);
    let two = encoder.solver.int_const(2);
    let lookup_insert_2 = encoder.solver.apply(&fmap_lookup, &[insert_term, two]);

    // Frame: lookup(insert(m,1,42), 2) == lookup(m, 2) since 1 != 2
    let eq = encoder.solver.eq(lookup_insert_2, lookup_m_2);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "frame violation should be UNSAT (key 1 != key 2), got: {result:?}"
    );
}

// ── Len non-negativity through dispatch ──

/// Encode `m.len()` via encode_pure and verify `len(m) >= 0` via axiom.
#[test]
#[timeout(30000)]
fn fmap_len_nonneg_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let m = var_with_sort("m", ExprSort::FMap);
    let len_expr = method_call(m.clone(), "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("m.len() should encode via fmap_len");

    // Trigger axiom assertion — need insert declared for axioms to fire
    let insert_expr = method_call(m, "insert", vec![int(0), int(0)]);
    let _insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("need insert for axiom trigger");

    encoder.assert_fmap_axioms();

    // Assert len(m) < 0 — should be UNSAT via len non-negativity axiom
    let zero = encoder.solver.int_const(0);
    let len_neg = encoder.solver.lt(len_term, zero);
    encoder.solver.assert_term(len_neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) < 0 should be UNSAT via len non-neg axiom, got: {result:?}"
    );
}

// ── Nested method-call composition through encode_pure ──

/// Test the full nested dispatch: `m.insert(1, 42).get(1)` as a single
/// PureExpr through encode_pure. This exercises the dispatch chain where
/// `get` must recognize the FMap-sorted return of `insert` and route to
/// fmap_lookup without an explicit sort annotation on the outer expression.
#[test]
#[timeout(30000)]
fn fmap_nested_insert_get_full_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let m = var_with_sort("m", ExprSort::FMap);
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);
    // Nested: insert result becomes the receiver of .get(1)
    let get_on_insert = method_call(insert_expr, "get", vec![int(1)]);

    let lookup_term = encoder
        .encode_pure(&get_on_insert)
        .expect("m.insert(1,42).get(1) should encode through nested dispatch");

    encoder.assert_fmap_axioms();

    // The result should equal 42 via insert-lookup axiom
    let forty_two = encoder.solver.int_const(42);
    let eq = encoder.solver.eq(lookup_term, forty_two);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "m.insert(1,42).get(1) != 42 should be UNSAT via axiom + nested dispatch, got: {result:?}"
    );
}

/// Nested: `m.insert(1, 42).contains(1)` as a single PureExpr.
#[test]
#[timeout(30000)]
fn fmap_nested_insert_contains_full_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let m = var_with_sort("m", ExprSort::FMap);
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);
    let contains_on_insert = method_call(insert_expr, "contains", vec![int(1)]);

    let contains_term = encoder
        .encode_pure(&contains_on_insert)
        .expect("m.insert(1,42).contains(1) should encode");

    encoder.assert_fmap_axioms();

    // Negate: NOT contains(insert(m,1,42), 1)
    let not_contains = encoder.solver.not(contains_term);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT m.insert(1,42).contains(1) should be UNSAT, got: {result:?}"
    );
}

// ── Two-insert chain through dispatch ──

/// Concrete scenario: insert two different keys via dispatch,
/// then verify both lookups return correct values via axioms.
///
/// Models: m2 = m.insert(1, 10).insert(2, 20)
/// Verifies: lookup(m2, 1) == 10 && lookup(m2, 2) == 20
#[test]
#[timeout(30000)]
fn fmap_two_insert_chain_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let m = var_with_sort("m", ExprSort::FMap);
    let insert1 = method_call(m, "insert", vec![int(1), int(10)]);
    let insert2 = method_call(insert1, "insert", vec![int(2), int(20)]);

    let m2 = encoder
        .encode_pure(&insert2)
        .expect("chained insert should encode");

    // Declare fmap_lookup before axiom assertion
    let fmap = fmap_sort();
    let fmap_lookup = encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap, Sort::Int], Sort::Int);

    encoder.assert_fmap_axioms();

    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let ten = encoder.solver.int_const(10);
    let twenty = encoder.solver.int_const(20);

    let lookup_1 = encoder.solver.apply(&fmap_lookup, &[m2, one]);
    let lookup_2 = encoder.solver.apply(&fmap_lookup, &[m2, two]);

    // Negate: NOT (lookup(m2,1)==10 AND lookup(m2,2)==20)
    let eq_10 = encoder.solver.eq(lookup_1, ten);
    let eq_20 = encoder.solver.eq(lookup_2, twenty);
    let both = encoder.solver.and(eq_10, eq_20);
    let negated = encoder.solver.not(both);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "two-insert chain lookups should verify via axioms, got: {result:?}"
    );
}
