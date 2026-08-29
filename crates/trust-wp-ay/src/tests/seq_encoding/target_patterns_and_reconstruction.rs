// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

// =============================================================================
// Direct semantic tests for method-call fast paths (#2514)
//
// Each test exercises a specific encoding path through encode_pure() and
// proves the resulting axiom via refutation (assert NOT(conclusion), expect
// UNSAT). These complement the existing structural/routing tests by
// verifying the produced SMT formula is semantically correct.
// =============================================================================

/// Prove: `push_front(s, x).len() == s.len() + 1`
///
/// push_front has a concrete Array+Length encoding (operations.rs:473).
/// This mirrors the push_back_len test but exercises the push_front path,
/// which adjusts the offset in the opposite direction.
#[test]
#[timeout(30000)]
fn test_seq_axiom_push_front_len() {
    let mut encoder = AYEncoder::new();

    let s = view(var("s"));
    let x = var("x");

    let push_front = method_call(s.clone(), "push_front", vec![x]);
    let push_front_len = method_call(push_front, "len", vec![]);
    let s_len = method_call(s, "len", vec![]);
    let s_len_plus_1 = add(s_len, int(1));

    let axiom = eq(push_front_len, s_len_plus_1);
    let term = encoder
        .encode_pure(&axiom)
        .expect("push_front len formula should encode");
    let neg = encoder.solver.not(term);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "push_front(s, x).len() == s.len() + 1 should be UNSAT (axiom holds), got {result:?}"
    );
}

/// Prove: `push_front(s, x).index_logic(0) == x` for concrete index 0.
///
/// push_front stores the element at (offset - 1) and the new offset is
/// (offset - 1), so index 0 reads at (new_offset + 0) == (offset - 1)
/// which is exactly where the element was stored.
#[test]
#[timeout(30000)]
fn test_seq_axiom_push_front_element_at_zero() {
    let mut encoder = AYEncoder::new();

    let s = view(var("s"));
    let x = var("x");

    let push_front = method_call(s, "push_front", vec![x.clone()]);
    let index_zero = method_call(push_front, "index_logic", vec![int(0)]);

    let axiom = eq(index_zero, x);
    let term = encoder
        .encode_pure(&axiom)
        .expect("push_front index(0) formula should encode");
    let neg = encoder.solver.not(term);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "push_front(s, x)[0] == x should be UNSAT (axiom holds), got {result:?}"
    );
}

/// Prove: `NOT is_empty(push_back(s, x))` — a non-empty sequence after push.
///
/// Exercises the is_empty dispatch (collection_dispatch.rs:175) through
/// the method-call path. is_empty encodes as `seq_len(r) == 0`, and
/// push_back increments length by 1, so the result cannot be 0.
#[test]
#[timeout(30000)]
fn test_seq_is_empty_after_push_back_is_false() {
    let mut encoder = AYEncoder::new();

    let s = view(var("s"));
    let x = var("x");

    let pushed = method_call(s, "push_back", vec![x]);
    let is_empty = method_call(pushed, "is_empty", vec![]);

    let term = encoder
        .encode_pure(&is_empty)
        .expect("is_empty(push_back(s, x)) should encode");

    // Assert is_empty is true — this should be UNSAT because len >= 1
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "is_empty(push_back(s, x)) should be UNSAT (push adds one element), got {result:?}"
    );
}

/// Prove: `contains(push_back(s, x), x) == true` via axiom 10.
///
/// Exercises the contains dispatch (collection_dispatch.rs:217) through
/// the method-call path. Axiom 10 states:
///   `contains(push_back(s, v), x) = (x == v || contains(s, x))`
/// When x == v (same element), this reduces to `true`.
///
/// This test requires quantifiers because axiom 10 is universally
/// quantified with trigger `contains(push_back(s, v), x)`.
#[test]
#[timeout(30000)]
fn test_seq_contains_push_back_same_element() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let s = view(var("s"));
    let x = var("x");

    let pushed = method_call(s, "push_back", vec![x.clone()]);
    let contains = method_call(pushed, "contains", vec![x]);

    let term = encoder
        .encode_pure(&contains)
        .expect("contains(push_back(s, x), x) should encode");

    // Negate: NOT contains(push_back(s, x), x) — should be UNSAT
    let neg = encoder.solver.not(term);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT contains(push_back(s, x), x) should be UNSAT (axiom 10), got {result:?}"
    );
}

/// Prove: `tail(push_back(seq_empty, x)).len() == 0`
///
/// tail/pop_front drops the first element (subsequence from 1 to len).
/// For a 1-element sequence (push_back on empty), the tail is empty.
/// Exercises the tail fast path (operations.rs:295).
#[test]
#[timeout(30000)]
fn test_seq_tail_of_singleton_has_zero_length() {
    let mut encoder = AYEncoder::new();

    let empty = logic_fn_call("seq_empty", vec![]);
    let singleton = method_call(empty, "push_back", vec![int(42)]);
    let tail = method_call(singleton, "tail", vec![]);
    let tail_len = method_call(tail, "len", vec![]);

    let axiom = eq(tail_len, int(0));
    let term = encoder
        .encode_pure(&axiom)
        .expect("tail(singleton).len() == 0 should encode");
    let neg = encoder.solver.not(term);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "tail(push_back(empty, 42)).len() != 0 should be UNSAT, got {result:?}"
    );
}

/// cc/seq.rs `g` function postcondition: `s[..] == s` desugar to
/// `s.subsequence(0, s.len()) == s`. With a symbolic Seq `s` (not built
/// from concrete operations), the encoder must be able to decompose
/// equality and prove this identity. Part of #2463.
#[test]
#[timeout(30000)]
fn test_cc_seq_g_subsequence_full_range_eq_self() {
    let mut encoder = AYEncoder::new();

    // s: Seq<Int> (symbolic)
    // requires: s.len() >= 1
    let s_len = method_call(var("s"), "len", vec![]);
    let requires = ge(s_len.clone(), int(1));

    // ensures: s.subsequence(0, s.len()) == s  (i.e., s[..] == s)
    let subseq = method_call(var("s"), "subsequence", vec![int(0), s_len]);
    let ensures = eq(subseq, var("s"));

    // Register sort hints (all expressions that mention s)
    encoder.register_sort_hints(&[requires.clone(), ensures.clone()]);

    // Assert precondition
    let req_term = encoder
        .encode_pure(&requires)
        .expect("requires encoding should succeed");
    encoder.assert_term(req_term);

    // Assert negation of postcondition (refutation-based: UNSAT = verified)
    let ens_term = encoder
        .encode_pure(&ensures)
        .expect("ensures encoding should succeed");
    let violation = encoder.solver.not(ens_term);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "s.subsequence(0, s.len()) == s should be provable, got {result:?}"
    );
}

/// cc/seq.rs `g` postcondition: `s[0..1].len() == 1`.
/// With `s.len() >= 1`, subsequence(s, 0, 1) has length 1. Part of #2463.
#[test]
#[timeout(30000)]
fn test_cc_seq_g_subsequence_len_from_symbolic() {
    let mut encoder = AYEncoder::new();

    let s_len = method_call(var("s"), "len", vec![]);
    let requires = ge(s_len, int(1));

    // s.subsequence(0, 1).len() == 1
    let subseq = method_call(var("s"), "subsequence", vec![int(0), int(1)]);
    let subseq_len = method_call(subseq, "len", vec![]);
    let ensures = eq(subseq_len, int(1));

    encoder.register_sort_hints(&[requires.clone(), ensures.clone()]);

    let req_term = encoder
        .encode_pure(&requires)
        .expect("requires encoding should succeed");
    encoder.assert_term(req_term);

    let ens_term = encoder
        .encode_pure(&ensures)
        .expect("ensures encoding should succeed");
    let violation = encoder.solver.not(ens_term);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "s.subsequence(0, 1).len() should be 1 when s.len() >= 1, got {result:?}"
    );
}
