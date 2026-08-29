// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SAT-side companion tests for FMap dispatch semantic round-trips (#2514).
//!
//! The main `fmap_dispatch_semantic_tests.rs` suite proves specific positive
//! properties via UNSAT refutations. These companions prove the encoded
//! operations remain contingent on non-target keys, so those proofs do not pass
//! vacuously because `contains` or `lookup` got overconstrained.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::super::{super::*, helpers::*};

fn fmap_sort() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

/// Companion to the same-key contains proof: inserting key 1 must not force key
/// 2 to appear.
#[test]
#[timeout(30000)]
fn fmap_insert_other_key_contains_can_stay_false_via_dispatch() {
    let mut encoder = AYEncoder::new();

    let m = var_with_sort("m", ExprSort::FMap);
    let m_term = encoder
        .encode_pure(&m)
        .expect("FMap receiver should encode");
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);
    let contains_other = method_call(insert_expr, "contains", vec![int(2)]);

    let contains_term = encoder
        .encode_pure(&contains_other)
        .expect("m.insert(1,42).contains(2) should encode");

    let fmap = fmap_sort();
    let contains_decl =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap, Sort::Int], Sort::Bool);
    let two = encoder.solver.int_const(2);
    let contains_m_two = encoder.solver.apply(&contains_decl, &[m_term, two]);

    // Ground instance of the FMap insert-frame axiom for 1 != 2:
    // contains(insert(m, 1, 42), 2) == contains(m, 2). This keeps the SAT
    // witness quantifier-free while still exercising the dispatch-produced UFs.
    let frame = encoder.eq_term(contains_term, contains_m_two);
    encoder.solver.assert_term(frame);

    let not_contains = encoder.solver.not(contains_term);
    let not_base_contains = encoder.solver.not(contains_m_two);
    encoder.solver.assert_term(not_base_contains);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "NOT m.insert(1,42).contains(2) should stay SAT; only the inserted key is forced, got: {result:?}"
    );
}

/// Companion to the same-key lookup proof: inserting key 1 must not force an
/// unrelated lookup to the inserted value.
#[test]
#[timeout(30000)]
fn fmap_insert_other_key_lookup_can_vary_via_dispatch() {
    let mut encoder = AYEncoder::new();

    let m = var_with_sort("m", ExprSort::FMap);
    let m_term = encoder
        .encode_pure(&m)
        .expect("FMap receiver should encode");
    let insert_expr = method_call(m, "insert", vec![int(1), int(42)]);
    let get_other = method_call(insert_expr, "get", vec![int(2)]);

    let lookup_term = encoder
        .encode_pure(&get_other)
        .expect("m.insert(1,42).get(2) should encode");

    let fmap = fmap_sort();
    let lookup_decl = encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap, Sort::Int], Sort::Int);
    let two = encoder.solver.int_const(2);
    let lookup_m_two = encoder.solver.apply(&lookup_decl, &[m_term, two]);

    let ninety_nine = encoder.solver.int_const(99);
    // Ground instance of the FMap insert-frame axiom for 1 != 2:
    // lookup(insert(m, 1, 42), 2) == lookup(m, 2).
    let frame = encoder.eq_term(lookup_term, lookup_m_two);
    encoder.solver.assert_term(frame);
    let base_eq_ninety_nine = encoder.solver.eq(lookup_m_two, ninety_nine);
    let eq_ninety_nine = encoder.solver.eq(lookup_term, ninety_nine);
    encoder.solver.assert_term(base_eq_ninety_nine);
    encoder.solver.assert_term(eq_ninety_nine);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "m.insert(1,42).get(2) == 99 should stay SAT; non-target lookups remain unconstrained by the insert, got: {result:?}"
    );
}
