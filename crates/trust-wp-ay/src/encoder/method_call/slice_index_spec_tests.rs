// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for SliceIndexSpec predicate encoding (in_bounds, has_value,
//! resolve_elsewhere) with usize (Int) indices.

use ay_dpll::api::{SolveResult, Term, TermKind};
use ntest::timeout;
use trust_wp_core::{
    formula::{intern_sort_name, ExprSort, PureExpr},
    logic::logic_fn_smt_name,
};

use crate::{
    encoder::AYEncoder,
    tests::helpers::{deref, ge, lt, method_call, not, var, var_with_sort, view},
};

fn seq_var(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::Seq)
}

fn range_inclusive_var(name: &str) -> PureExpr {
    var_with_sort(
        name,
        ExprSort::Datatype(intern_sort_name("std::ops::RangeInclusive")),
    )
}

fn mut_vec_var(name: &str) -> PureExpr {
    var_with_sort(
        name,
        ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name(
            "std::vec::Vec",
        )))),
    )
}

fn assert_eq_term(enc: &mut AYEncoder, lhs: Term, rhs: Term) {
    let eq = enc.solver.eq(lhs, rhs);
    enc.solver.assert_term(eq);
}

fn assert_int_eq(enc: &mut AYEncoder, term: Term, value: i64) {
    let rhs = enc.solver.int_const(value);
    assert_eq_term(enc, term, rhs);
}

fn term_contains_app(enc: &AYEncoder, term: Term, expected: &str) -> bool {
    matches!(
        enc.solver.term_kind(term),
        TermKind::App { ref name, .. } if name == expected
    ) || enc
        .solver
        .term_children(term)
        .into_iter()
        .any(|child| term_contains_app(enc, child, expected))
}

// ── in_bounds ──────────────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_in_bounds_usize_sat_within_range() {
    // ix = 2, seq has len 5 => in_bounds should be satisfiable
    let mut enc = AYEncoder::new();

    let receiver = PureExpr::Int(2);
    let seq_expr = seq_var("seq");
    let term = enc
        .encode_in_bounds(&receiver, &[seq_expr.clone()], None)
        .expect("encoding should succeed");

    // Assert in_bounds is true
    enc.solver.assert_term(term);

    // Assert seq.len() == 5
    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let seq_len = enc.seq_len_term(seq_term).unwrap();
    let five = enc.solver.int_const(5);
    let len_eq = enc.solver.eq(seq_len, five);
    enc.solver.assert_term(len_eq);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "ix=2, len=5 in_bounds should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_in_bounds_usize_unsat_out_of_range() {
    // ix = 5, seq has len 5 => in_bounds should be UNSAT (ix >= len)
    let mut enc = AYEncoder::new();

    let receiver = PureExpr::Int(5);
    let seq_expr = seq_var("seq");
    let term = enc
        .encode_in_bounds(&receiver, &[seq_expr.clone()], None)
        .expect("encoding should succeed");

    enc.solver.assert_term(term);

    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let seq_len = enc.seq_len_term(seq_term).unwrap();
    let five = enc.solver.int_const(5);
    let len_eq = enc.solver.eq(seq_len, five);
    enc.solver.assert_term(len_eq);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ix=5, len=5 in_bounds should be UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_in_bounds_negative_index_unsat() {
    // ix = -1 => in_bounds should be UNSAT (ix < 0)
    let mut enc = AYEncoder::new();

    let receiver = PureExpr::Int(-1);
    let seq_expr = seq_var("seq");
    let term = enc
        .encode_in_bounds(&receiver, &[seq_expr.clone()], None)
        .expect("encoding should succeed");

    enc.solver.assert_term(term);

    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let seq_len = enc.seq_len_term(seq_term).unwrap();
    let five = enc.solver.int_const(5);
    let len_eq = enc.solver.eq(seq_len, five);
    enc.solver.assert_term(len_eq);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ix=-1 in_bounds should be UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_in_bounds_range_inclusive_sat_within_range() {
    let mut enc = AYEncoder::new();

    let receiver = range_inclusive_var("ix");
    let seq_expr = seq_var("seq");
    let term = enc
        .encode_in_bounds(&receiver, &[seq_expr.clone()], None)
        .expect("encoding should succeed");
    enc.solver.assert_term(term);

    let start = enc
        .encode_pure_impl(&method_call(receiver.clone(), "start_log", vec![]), None)
        .unwrap();
    let end = enc
        .encode_pure_impl(&method_call(receiver, "end_log", vec![]), None)
        .unwrap();
    assert_int_eq(&mut enc, start, 1);
    assert_int_eq(&mut enc, end, 2);

    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let seq_len = enc.seq_len_term(seq_term).unwrap();
    assert_int_eq(&mut enc, seq_len, 4);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "1..=2 over len 4 should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_in_bounds_range_inclusive_unsat_out_of_range() {
    let mut enc = AYEncoder::new();

    let receiver = range_inclusive_var("ix");
    let seq_expr = seq_var("seq");
    let term = enc
        .encode_in_bounds(&receiver, &[seq_expr.clone()], None)
        .expect("encoding should succeed");
    enc.solver.assert_term(term);

    let start = enc
        .encode_pure_impl(&method_call(receiver.clone(), "start_log", vec![]), None)
        .unwrap();
    let end = enc
        .encode_pure_impl(&method_call(receiver, "end_log", vec![]), None)
        .unwrap();
    assert_int_eq(&mut enc, start, 1);
    assert_int_eq(&mut enc, end, 4);

    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let seq_len = enc.seq_len_term(seq_term).unwrap();
    assert_int_eq(&mut enc, seq_len, 4);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "1..=4 over len 4 should be UNSAT, got {result:?}"
    );
}

// ── has_value ──────────────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_has_value_usize_encodes_equality() {
    // has_value(ix, seq, out) should be equivalent to seq[ix] == out.
    // Assert has_value(ix, seq, out) AND seq[ix] != out => should be UNSAT.
    let mut enc = AYEncoder::new();

    let ix_expr = var("ix");
    let seq_expr = seq_var("seq");
    let out_expr = var("out");

    let hv_term = enc
        .encode_has_value(&ix_expr, &[seq_expr.clone(), out_expr.clone()], None)
        .expect("encoding should succeed");

    // Assert has_value is true
    enc.solver.assert_term(hv_term);

    // Get the actual terms
    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let ix_term = enc.encode_pure_impl(&ix_expr, None).unwrap();
    let out_term = enc.encode_pure_impl(&out_expr, None).unwrap();

    // Assert seq[ix] != out (should contradict has_value)
    let indexed = enc.seq_index_term(seq_term, ix_term).unwrap();
    let eq = enc.solver.eq(indexed, out_term);
    let neq = enc.solver.not(eq);
    enc.solver.assert_term(neq);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "has_value(ix, seq, out) AND seq[ix] != out should be UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_has_value_usize_satisfiable() {
    // has_value(0, seq, out) with a fresh seq should be SAT (model can choose)
    let mut enc = AYEncoder::new();

    let receiver = PureExpr::Int(0);
    let seq_expr = seq_var("seq");
    let out_expr = var("out");

    let hv_term = enc
        .encode_has_value(&receiver, &[seq_expr, out_expr], None)
        .expect("encoding should succeed");

    enc.solver.assert_term(hv_term);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "has_value(0, seq, out) should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_has_value_range_inclusive_accepts_matching_subsequence() {
    let mut enc = AYEncoder::new();

    let range_expr = range_inclusive_var("ix");
    let seq_expr = seq_var("seq");
    let out_expr = seq_var("out");

    let hv_term = enc
        .encode_has_value(&range_expr, &[seq_expr.clone(), out_expr.clone()], None)
        .expect("encoding should succeed");
    enc.solver.assert_term(hv_term);

    let start = enc
        .encode_pure_impl(&method_call(range_expr.clone(), "start_log", vec![]), None)
        .unwrap();
    let end = enc
        .encode_pure_impl(&method_call(range_expr, "end_log", vec![]), None)
        .unwrap();
    assert_int_eq(&mut enc, start, 1);
    assert_int_eq(&mut enc, end, 2);

    let subseq_expr = method_call(
        seq_expr,
        "subsequence",
        vec![PureExpr::Int(1), PureExpr::Int(3)],
    );
    let subseq_term = enc.encode_pure_impl(&subseq_expr, None).unwrap();
    let out_term = enc.encode_pure_impl(&out_expr, None).unwrap();
    let expected = enc.eq_term(subseq_term, out_term);
    enc.solver.assert_term(expected);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Sat | SolveResult::Unknown),
        "range has_value should accept the matching subsequence or fail closed, got {result:?}"
    );
}

// ── resolve_elsewhere ──────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_encoding_succeeds() {
    // Just verify that encoding resolve_elsewhere doesn't panic/error
    let mut enc = AYEncoder::new();

    let receiver = PureExpr::Int(2);
    let old_seq = seq_var("old_seq");
    let new_seq = seq_var("new_seq");

    let result = enc.encode_resolve_elsewhere(&receiver, &[old_seq, new_seq], None);
    assert!(
        result.is_ok(),
        "resolve_elsewhere encoding should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_axiom_fires() {
    // Assert resolve_elsewhere(ix, old, new) is true AND old[0] != new[0]
    // for ix=2 within bounds => should be UNSAT because the frame condition
    // protects all indices j != ix.
    //
    // Uses encode_pure_impl on index_logic method calls so the seq_index_logic
    // UF application appears in the e-graph for trigger matching.
    let mut enc = AYEncoder::new();

    let ix = PureExpr::Int(2);
    let old_seq = seq_var("old_seq");
    let new_seq = seq_var("new_seq");

    let re_term = enc
        .encode_resolve_elsewhere(&ix, &[old_seq.clone(), new_seq.clone()], None)
        .expect("encoding should succeed");

    // Assert resolve_elsewhere is true
    enc.solver.assert_term(re_term);

    // Assert len(old) = 5 and len(new) = 5 via encode_pure_impl
    let old_len_expr = method_call(old_seq.clone(), "len", vec![]);
    let new_len_expr = method_call(new_seq.clone(), "len", vec![]);
    let old_len_term = enc.encode_pure_impl(&old_len_expr, None).unwrap();
    let new_len_term = enc.encode_pure_impl(&new_len_expr, None).unwrap();
    let five = enc.solver.int_const(5);
    let old_len_eq = enc.solver.eq(old_len_term, five);
    enc.solver.assert_term(old_len_eq);
    let new_len_eq = enc.solver.eq(new_len_term, five);
    enc.solver.assert_term(new_len_eq);

    // Build old.index_logic(0) and new.index_logic(0) through the method
    // call encoder so seq_index_logic UF applications exist in the e-graph.
    let old_at_0_expr = method_call(old_seq, "index_logic", vec![PureExpr::Int(0)]);
    let new_at_0_expr = method_call(new_seq, "index_logic", vec![PureExpr::Int(0)]);
    let old_at_0 = enc.encode_pure_impl(&old_at_0_expr, None).unwrap();
    let new_at_0 = enc.encode_pure_impl(&new_at_0_expr, None).unwrap();

    // Assert old[0] != new[0] (index 0 != ix=2, so should be protected)
    let eq_at_0 = enc.solver.eq(old_at_0, new_at_0);
    let ne_at_0 = enc.solver.not(eq_at_0);
    enc.solver.assert_term(ne_at_0);

    assert_eq!(
        enc.assert_resolve_elsewhere_ground_instances(),
        1,
        "one protected observed index should produce one finite frame consequence"
    );

    let result = enc.check_sat();
    // The resolve_elsewhere quantifier says all indices j != ix must be equal
    // between old and new. Asserting index 0 differs should be UNSAT.
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "resolve_elsewhere(2, old, new) with old[0] != new[0] should be UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_range_inclusive_axiom_fires_outside_range() {
    let mut enc = AYEncoder::new();

    let range_expr = range_inclusive_var("ix");
    let old_seq = seq_var("old_seq");
    let new_seq = seq_var("new_seq");

    let re_term = enc
        .encode_resolve_elsewhere(&range_expr, &[old_seq.clone(), new_seq.clone()], None)
        .expect("encoding should succeed");
    enc.solver.assert_term(re_term);

    let start = enc
        .encode_pure_impl(&method_call(range_expr.clone(), "start_log", vec![]), None)
        .unwrap();
    let end = enc
        .encode_pure_impl(&method_call(range_expr, "end_log", vec![]), None)
        .unwrap();
    assert_int_eq(&mut enc, start, 1);
    assert_int_eq(&mut enc, end, 2);

    let old_len_expr = method_call(old_seq.clone(), "len", vec![]);
    let new_len_expr = method_call(new_seq.clone(), "len", vec![]);
    let old_len_term = enc.encode_pure_impl(&old_len_expr, None).unwrap();
    let new_len_term = enc.encode_pure_impl(&new_len_expr, None).unwrap();
    let four = enc.solver.int_const(4);
    assert_eq_term(&mut enc, old_len_term, four);
    let four_again = enc.solver.int_const(4);
    assert_eq_term(&mut enc, new_len_term, four_again);

    let old_at_0 = enc
        .encode_pure_impl(
            &method_call(old_seq, "index_logic", vec![PureExpr::Int(0)]),
            None,
        )
        .unwrap();
    let new_at_0 = enc
        .encode_pure_impl(
            &method_call(new_seq, "index_logic", vec![PureExpr::Int(0)]),
            None,
        )
        .unwrap();
    let old_new_eq = enc.solver.eq(old_at_0, new_at_0);
    let old_new_neq = enc.solver.not(old_new_eq);
    enc.solver.assert_term(old_new_neq);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "range resolve_elsewhere should protect indices outside 1..=2, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_negative_polarity_emits_no_positive_consequence() {
    let mut enc = AYEncoder::new();

    let old_seq = seq_var("old_seq");
    let new_seq = seq_var("new_seq");
    let predicate = enc
        .encode_resolve_elsewhere(&PureExpr::Int(2), &[old_seq.clone(), new_seq.clone()], None)
        .unwrap();
    let not_predicate = enc.solver.not(predicate);
    enc.solver.assert_term(not_predicate);

    let old_len = enc
        .encode_pure_impl(&method_call(old_seq.clone(), "len", vec![]), None)
        .unwrap();
    assert_int_eq(&mut enc, old_len, 5);
    let old_at_zero = enc
        .encode_pure_impl(
            &method_call(old_seq, "index_logic", vec![PureExpr::Int(0)]),
            None,
        )
        .unwrap();
    let new_at_zero = enc
        .encode_pure_impl(
            &method_call(new_seq, "index_logic", vec![PureExpr::Int(0)]),
            None,
        )
        .unwrap();
    let differs = enc.solver.neq(old_at_zero, new_at_zero);
    enc.solver.assert_term(differs);

    assert_eq!(
        enc.assert_resolve_elsewhere_ground_instances(),
        0,
        "a negatively-used monitor must emit no positive frame consequence"
    );
    assert!(
        enc.solver
            .assertions()
            .iter()
            .all(|term| !term_contains_app(&enc, *term, "seq_len")),
        "negative QF use must not install a raw/global seq_len bridge"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_does_not_bridge_partial_unrelated_receiver() {
    let mut enc = AYEncoder::new();

    let old_seq = seq_var("old_seq");
    let new_seq = seq_var("new_seq");
    let unrelated = seq_var("unrelated_seq");
    let predicate = enc
        .encode_resolve_elsewhere(&PureExpr::Int(2), &[old_seq.clone(), new_seq.clone()], None)
        .unwrap();
    enc.solver.assert_term(predicate);

    let old_len = enc
        .encode_pure_impl(&method_call(old_seq, "len", vec![]), None)
        .unwrap();
    assert_int_eq(&mut enc, old_len, 5);
    let unrelated_len = enc
        .encode_pure_impl(&method_call(unrelated.clone(), "len", vec![]), None)
        .unwrap();
    // Sharing only the length component does not authenticate Seq identity.
    assert_eq_term(&mut enc, unrelated_len, old_len);

    let unrelated_at_zero = enc
        .encode_pure_impl(
            &method_call(unrelated, "index_logic", vec![PureExpr::Int(0)]),
            None,
        )
        .unwrap();
    let new_at_zero = enc
        .encode_pure_impl(
            &method_call(new_seq, "index_logic", vec![PureExpr::Int(0)]),
            None,
        )
        .unwrap();
    let differs = enc.solver.neq(unrelated_at_zero, new_at_zero);
    enc.solver.assert_term(differs);

    assert_eq!(
        enc.assert_resolve_elsewhere_ground_instances(),
        1,
        "only the exact new receiver should instantiate the frame; the unrelated receiver must not"
    );

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "a different receiver sharing only old.len must remain independent; got {result:?}"
    );
    assert!(
        enc.solver
            .assertions()
            .iter()
            .all(|term| !term_contains_app(&enc, *term, "seq_len")),
        "QF resolve_elsewhere must not install a raw/global seq_len bridge"
    );
}

// ── integration: method dispatch routing ───────────────────────────

#[test]
#[timeout(30000)]
fn test_in_bounds_routed_through_method_dispatch() {
    // Verify that PureExpr::MethodCall { method: "in_bounds" } routes
    // through the new dispatch arm
    let mut enc = AYEncoder::new();

    let expr = method_call(PureExpr::Int(3), "in_bounds", vec![seq_var("seq")]);

    let result = enc.encode_pure_impl(&expr, None);
    assert!(
        result.is_ok(),
        "in_bounds should route through method dispatch: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_in_bounds_bridges_mut_vec_view_to_base_len_fact() {
    let mut enc = AYEncoder::new();

    let v = mut_vec_var("v");
    let v_term = enc.encode_pure_impl(&v, None).unwrap();
    let v_sort = enc.solver.get_sort(v_term);
    enc.get_or_declare_logic_func(
        &logic_fn_smt_name("len"),
        &[v_sort],
        ay_dpll::api::Sort::Int,
    );

    let i = var_with_sort("i", ExprSort::Int);
    let v_len = method_call(v.clone(), "len", vec![]);
    let v_view = view(deref(v));
    let in_bounds = method_call(i.clone(), "in_bounds", vec![v_view]);

    for fact in [
        ge(i.clone(), PureExpr::Int(0)),
        lt(i, v_len),
        not(in_bounds),
    ] {
        let term = enc
            .encode_pure_impl(&fact, None)
            .expect("all_zero-style in_bounds fact should encode");
        enc.solver.assert_term(term);
    }

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "i >= 0 && i < v.len() should discharge i.in_bounds((*v)@), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_has_value_routed_through_method_dispatch() {
    let mut enc = AYEncoder::new();

    let expr = method_call(
        PureExpr::Int(1),
        "has_value",
        vec![seq_var("seq"), var("out")],
    );

    let result = enc.encode_pure_impl(&expr, None);
    assert!(
        result.is_ok(),
        "has_value should route through method dispatch: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_routed_through_method_dispatch() {
    let mut enc = AYEncoder::new();

    let expr = method_call(
        PureExpr::Int(2),
        "resolve_elsewhere",
        vec![seq_var("old_seq"), seq_var("new_seq")],
    );

    let result = enc.encode_pure_impl(&expr, None);
    assert!(
        result.is_ok(),
        "resolve_elsewhere should route through method dispatch: {result:?}"
    );
}

// ── wrong arity errors ─────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_in_bounds_wrong_arity_returns_error() {
    let mut enc = AYEncoder::new();
    let result = enc.encode_in_bounds(&PureExpr::Int(0), &[], None);
    assert!(result.is_err(), "in_bounds with 0 args should error");
}

#[test]
#[timeout(30000)]
fn test_has_value_wrong_arity_returns_error() {
    let mut enc = AYEncoder::new();
    let result = enc.encode_has_value(&PureExpr::Int(0), &[seq_var("seq")], None);
    assert!(result.is_err(), "has_value with 1 arg should error");
}

#[test]
#[timeout(30000)]
fn test_resolve_elsewhere_wrong_arity_returns_error() {
    let mut enc = AYEncoder::new();
    let result = enc.encode_resolve_elsewhere(&PureExpr::Int(0), &[seq_var("seq")], None);
    assert!(result.is_err(), "resolve_elsewhere with 1 arg should error");
}

// ── end-to-end verification pattern ────────────────────────────────

#[test]
#[timeout(30000)]
fn test_in_bounds_implies_has_value_connection() {
    // Simulate the Vec::index contract pattern:
    //   requires: ix.in_bounds(self@)
    //   ensures: ix.has_value(self@, result)
    //
    // Assert in_bounds(ix, seq) AND NOT has_value(ix, seq, seq[ix]).
    // This should be UNSAT because has_value(ix, seq, out) <=> seq[ix] == out,
    // so seq[ix] == seq[ix] is tautological when in_bounds holds.
    let mut enc = AYEncoder::new();

    let ix_expr = var("ix");
    let seq_expr = seq_var("seq");

    // Encode in_bounds(ix, seq) — note: ix is a variable, not a literal.
    // We need it to be Int-sorted. Variables default to Int sort.
    let ib_term = enc
        .encode_in_bounds(&ix_expr, &[seq_expr.clone()], None)
        .expect("in_bounds encoding");

    // Assert in_bounds is true (the requires)
    enc.solver.assert_term(ib_term);

    // Encode seq[ix]
    let seq_term = enc.encode_pure_impl(&seq_expr, None).unwrap();
    let ix_term = enc.encode_pure_impl(&ix_expr, None).unwrap();
    let seq_at_ix = enc.seq_index_term(seq_term, ix_term).unwrap();

    // Encode has_value(ix, seq, seq[ix])
    let hv_term = enc
        .encode_has_value(
            &ix_expr,
            &[seq_expr, PureExpr::Var("__result".into(), None)],
            None,
        )
        .expect("has_value encoding");

    // Bind __result to seq[ix]
    let result_term = enc
        .encode_pure_impl(&PureExpr::Var("__result".into(), None), None)
        .unwrap();
    let result_eq = enc.solver.eq(result_term, seq_at_ix);
    enc.solver.assert_term(result_eq);

    // Assert NOT has_value — should make it UNSAT
    let not_hv = enc.solver.not(hv_term);
    enc.solver.assert_term(not_hv);

    let result = enc.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "in_bounds(ix, seq) AND result == seq[ix] AND NOT has_value(ix, seq, result) should be UNSAT, got {result:?}"
    );
}
