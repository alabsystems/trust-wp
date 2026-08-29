// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SAT-side companion tests for FSet dispatch semantic round-trips (#2514).
//!
//! The primary FSet round-trip suite proves positive semantic facts via UNSAT
//! refutations. These companions show the encoded operations stay contingent on
//! unrelated elements, preventing the main proofs from passing because
//! `contains` got globally overconstrained.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::super::{super::*, helpers::*};

/// Companion to the same-element insert proof: inserting 5 must not force 7 to
/// be present.
#[test]
#[timeout(30000)]
fn fset_insert_other_elem_contains_can_stay_false_via_dispatch() {
    let mut encoder = AYEncoder::new();

    let s_term = encoder
        .encode_pure(&var("s"))
        .expect("base set should encode");

    let insert_expr = method_call(var("s"), "insert", vec![int(5)]);
    let contains_other = method_call(insert_expr, "contains", vec![int(7)]);

    let contains_term = encoder
        .encode_pure(&contains_other)
        .expect("s.insert(5).contains(7) should encode");

    let contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let seven = encoder.solver.int_const(7);
    let contains_s_seven = encoder.solver.apply(&contains_decl, &[s_term, seven]);

    // Ground instance of the FSet insert-frame axiom for 5 != 7:
    // contains(insert(s, 5), 7) == contains(s, 7). Keeping this quantifier-free
    // checks the contingency witness without relying on SAT model generation
    // through the full universal FSet axiom set.
    let frame = encoder.eq_term(contains_term, contains_s_seven);
    encoder.solver.assert_term(frame);

    let not_contains = encoder.solver.not(contains_term);
    let not_base_contains = encoder.solver.not(contains_s_seven);
    encoder.solver.assert_term(not_base_contains);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "NOT s.insert(5).contains(7) should stay SAT; insert must only force the inserted element, got: {result:?}"
    );
}

/// Companion to the remove-self proof: removing 5 must not erase unrelated
/// membership facts.
#[test]
#[timeout(30000)]
fn fset_remove_other_elem_can_remain_present_via_dispatch() {
    let mut encoder = AYEncoder::new();

    let s_term = encoder
        .encode_pure(&var("s"))
        .expect("base set should encode");

    let remove_expr = method_call(var("s"), "remove", vec![int(5)]);
    let contains_other = method_call(remove_expr, "contains", vec![int(7)]);

    let contains_term = encoder
        .encode_pure(&contains_other)
        .expect("s.remove(5).contains(7) should encode");

    let contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let seven = encoder.solver.int_const(7);
    let contains_s_seven = encoder.solver.apply(&contains_decl, &[s_term, seven]);

    // Ground instance of the FSet remove-frame axiom for 5 != 7:
    // contains(remove(s, 5), 7) == contains(s, 7).
    let frame = encoder.eq_term(contains_term, contains_s_seven);
    encoder.solver.assert_term(frame);

    encoder.solver.assert_term(contains_s_seven);
    encoder.solver.assert_term(contains_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "s.remove(5).contains(7) should stay SAT; removing one element must not collapse the set, got: {result:?}"
    );
}
