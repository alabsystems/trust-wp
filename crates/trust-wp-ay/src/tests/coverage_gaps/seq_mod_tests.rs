// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding infrastructure in `encoder/seq/mod.rs`.
//!
//! Covers genuinely untested or weakly tested `pub(crate)` functions:
//! - `seq_len_term` (3-path branching: fast-path SeqValue, post-coercion, UF fallback)
//! - `assert_seq_shape_constraints` (UF projector equality assertions, 0 test refs)
//!
//! Part of #2514 (Tier 2 coverage gap: encoder/seq/mod.rs, 460 LOC,
//! `seq_len_term` has 2 indirect refs, `assert_seq_shape_constraints` has 0 refs).

use ay_dpll::api::Sort;
use ntest::timeout;

use super::super::{super::*, helpers::*};

// ── Helper: get Seq sort from seq theory ────────────────────────

fn seq_sort(encoder: &mut AYEncoder) -> Sort {
    let sf = encoder.seq_funcs();
    sf.seq_len.domain()[0].clone()
}

fn arr_sort(encoder: &mut AYEncoder) -> Sort {
    let sf = encoder.seq_funcs();
    sf.seq_array.range().clone()
}

// ── seq_len_term ────────────────────────────────────────────────

/// seq_len_term on an unknown Seq term uses UF fallback and returns Int.
#[test]
#[timeout(30000)]
fn seq_len_unknown_term_uf_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let seq_term = encoder.solver.fresh_var("s", ss);

    let result = encoder.seq_len_term(seq_term);
    assert!(
        result.is_ok(),
        "seq_len_term on unknown term should succeed"
    );
    let len_term = result.unwrap();
    let sort = encoder.solver.get_sort(len_term);
    assert_eq!(
        sort,
        Sort::Int,
        "seq_len_term should return Int-sorted term"
    );
}

/// seq_len_term on a concrete SeqValue (via encode_pure seq_empty) uses the fast path.
#[test]
#[timeout(30000)]
fn seq_len_empty_via_encode_pure() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode seq_empty via the public encode_pure path
    let empty_expr = logic_fn_call("seq_empty", vec![]);
    let empty_term = encoder.encode_pure(&empty_expr).expect("encode seq_empty");

    let result = encoder.seq_len_term(empty_term);
    assert!(result.is_ok(), "seq_len_term on empty should succeed");

    let len_term = result.unwrap();
    let zero = encoder.solver.int_const(0);
    let eq = encoder.solver.eq(len_term, zero);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "len(seq_empty) should be 0"
    );
}

/// seq_len_term on seq![42] (single element) returns 1.
#[test]
#[timeout(30000)]
fn seq_len_singleton() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = logic_fn_call("seq", vec![int(42)]);
    let seq_term = encoder.encode_pure(&expr).expect("encode seq![42]");

    let result = encoder.seq_len_term(seq_term);
    assert!(result.is_ok(), "seq_len_term on singleton should succeed");

    let len_term = result.unwrap();
    let one = encoder.solver.int_const(1);
    let eq = encoder.solver.eq(len_term, one);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "len(seq![42]) should be 1"
    );
}

/// Two seq_len_term calls on the same term return the same result.
#[test]
#[timeout(30000)]
fn seq_len_same_term_consistent() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let seq_term = encoder.solver.fresh_var("s", ss);

    let len1 = encoder.seq_len_term(seq_term).expect("first call");
    let len2 = encoder.seq_len_term(seq_term).expect("second call");

    // Both should be equal (same UF application on same argument)
    let eq = encoder.solver.eq(len1, len2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "seq_len(s) should be consistent across calls"
    );
}

/// seq_len_term on different unknown terms can have different values.
#[test]
#[timeout(30000)]
fn seq_len_different_terms_independent() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let s1 = encoder.solver.fresh_var("s1", ss.clone());
    let s2 = encoder.solver.fresh_var("s2", ss);

    let len1 = encoder.seq_len_term(s1).expect("len s1");
    let len2 = encoder.seq_len_term(s2).expect("len s2");

    // Assert len(s1) = 3, len(s2) = 7 — should be satisfiable
    let three = encoder.solver.int_const(3);
    let seven = encoder.solver.int_const(7);
    let eq1 = encoder.solver.eq(len1, three);
    let eq2 = encoder.solver.eq(len2, seven);
    encoder.assert_term(eq1);
    encoder.assert_term(eq2);

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "different Seq terms should have independent lengths"
    );
}

// ── assert_seq_shape_constraints ────────────────────────────────

/// Shape constraints on a fresh Seq term assert projector equalities.
#[test]
#[timeout(30000)]
fn shape_constraints_fresh_seq_term() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let as_ = arr_sort(&mut encoder);

    let seq_term = encoder.solver.fresh_var("s", ss);
    let arr_term = encoder.solver.fresh_var("a", as_);
    let len_term = encoder.solver.int_const(5);
    let off_term = encoder.solver.int_const(0);

    let result =
        encoder.assert_seq_shape_constraints(seq_term, arr_term, len_term, off_term, "test");
    assert!(
        result.is_ok(),
        "shape constraints on fresh Seq term should succeed"
    );

    // The constraints assert: seq_len(s) == 5
    // Verify via seq_len_term
    let len_from_fn = encoder.seq_len_term(seq_term).expect("seq_len_term");
    let five = encoder.solver.int_const(5);
    let eq = encoder.solver.eq(len_from_fn, five);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "seq_len(s) != 5 should be Unsat after shape constraint"
    );
}

/// Shape constraints are idempotent (calling twice doesn't panic).
#[test]
#[timeout(30000)]
fn shape_constraints_idempotent() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let as_ = arr_sort(&mut encoder);

    let seq_term = encoder.solver.fresh_var("s2", ss);
    let arr_term = encoder.solver.fresh_var("a2", as_);
    let len_term = encoder.solver.int_const(3);
    let off_term = encoder.solver.int_const(0);

    let r1 = encoder.assert_seq_shape_constraints(seq_term, arr_term, len_term, off_term, "idem1");
    let r2 = encoder.assert_seq_shape_constraints(seq_term, arr_term, len_term, off_term, "idem2");
    assert!(
        r1.is_ok() && r2.is_ok(),
        "repeated shape constraints should succeed"
    );
}

/// Shape constraints with different context strings don't conflict.
#[test]
#[timeout(30000)]
fn shape_constraints_different_contexts() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let as_ = arr_sort(&mut encoder);

    let s1 = encoder.solver.fresh_var("s_ctx1", ss.clone());
    let a1 = encoder.solver.fresh_var("a_ctx1", as_.clone());
    let s2 = encoder.solver.fresh_var("s_ctx2", ss);
    let a2 = encoder.solver.fresh_var("a_ctx2", as_);

    let three = encoder.solver.int_const(3);
    let seven = encoder.solver.int_const(7);
    let zero = encoder.solver.int_const(0);

    let r1 = encoder.assert_seq_shape_constraints(s1, a1, three, zero, "ctx_a");
    let r2 = encoder.assert_seq_shape_constraints(s2, a2, seven, zero, "ctx_b");
    assert!(
        r1.is_ok() && r2.is_ok(),
        "different contexts should not conflict"
    );
}

/// Shape constraints: projector equalities are consistent with seq_len_term.
#[test]
#[timeout(30000)]
fn shape_constraints_consistent_with_len_term() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let as_ = arr_sort(&mut encoder);

    let seq_term = encoder.solver.fresh_var("s_cons", ss);
    let arr_term = encoder.solver.fresh_var("a_cons", as_);
    let ten = encoder.solver.int_const(10);
    let zero = encoder.solver.int_const(0);

    // Assert shape constraint: seq_len(s_cons) == 10
    encoder
        .assert_seq_shape_constraints(seq_term, arr_term, ten, zero, "consistency")
        .expect("shape constraints");

    // Now seq_len_term should also return 10
    let len_from_fn = encoder.seq_len_term(seq_term).expect("seq_len_term");
    let eq = encoder.solver.eq(len_from_fn, ten);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "seq_len_term(s) should equal shape-constrained length"
    );
}

/// Shape constraints on two distinct seqs maintain independence.
#[test]
#[timeout(30000)]
fn shape_constraints_independent_seqs() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort(&mut encoder);
    let as_ = arr_sort(&mut encoder);

    let s1 = encoder.solver.fresh_var("s_ind1", ss.clone());
    let a1 = encoder.solver.fresh_var("a_ind1", as_.clone());
    let s2 = encoder.solver.fresh_var("s_ind2", ss);
    let a2 = encoder.solver.fresh_var("a_ind2", as_);

    let five = encoder.solver.int_const(5);
    let nine = encoder.solver.int_const(9);
    let zero = encoder.solver.int_const(0);

    encoder
        .assert_seq_shape_constraints(s1, a1, five, zero, "ind1")
        .expect("ind1");
    encoder
        .assert_seq_shape_constraints(s2, a2, nine, zero, "ind2")
        .expect("ind2");

    // s1 has len 5, s2 has len 9 — assert s2 len == 5, expect Unsat
    let len_s2 = encoder.seq_len_term(s2).expect("len s2");
    let eq_s2_five = encoder.solver.eq(len_s2, five);
    encoder.assert_term(eq_s2_five);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "s2 constrained to len 9, asserting len==5 should be Unsat"
    );
}
