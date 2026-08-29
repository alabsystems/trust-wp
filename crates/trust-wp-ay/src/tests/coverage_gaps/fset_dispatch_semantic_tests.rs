// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic round-trip tests for FSet method-call dispatch (#2514).
//!
//! Bridges the gap between:
//! - **Dispatch tests** (`fset_method_tests.rs`, `fset_method_strengthened_tests.rs`):
//!   verify `encode_pure` routes to correct UFs with UNSAT dual consistency.
//! - **Axiom tests** (`fset_axiom_tests.rs`): verify axioms hold with manually
//!   declared UFs.
//!
//! These tests go through `encode_pure` (dispatch) AND `assert_fset_axioms()`,
//! proving the UFs produced by dispatch are correctly connected by axiom reasoning.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::super::{super::*, helpers::*};

// ── Insert-then-contains: contains(insert(s, x), x) ──

/// Encode `s.insert(5)` via encode_pure, then verify via axiom that
/// `fset_contains(result, 5)` is true.
#[test]
#[timeout(30000)]
fn fset_insert_then_contains_same_elem_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let insert_expr = method_call(var("s"), "insert", vec![int(5)]);
    let insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("s.insert(5) should encode via fset dispatch");

    // Declare fset_contains before axiom assertion — assert_fset_axioms
    // only links UFs already declared.
    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    let five = encoder.solver.int_const(5);
    let contains_result = encoder.solver.apply(&fset_contains, &[insert_term, five]);

    // Negate: NOT contains(insert(s,5), 5) — axiom says this is true
    let not_contains = encoder.solver.not(contains_result);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT fset_contains(fset_insert(s,5), 5) should be UNSAT via axiom, got: {result:?}"
    );
}

// ── Remove-then-not-contains: NOT contains(remove(s, x), x) ──

/// Encode `s.remove(5)` via encode_pure, then verify via axiom that
/// `fset_contains(result, 5)` is false.
#[test]
#[timeout(30000)]
fn fset_remove_then_not_contains_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let remove_expr = method_call(var("s"), "remove", vec![int(5)]);
    let remove_term = encoder
        .encode_pure(&remove_expr)
        .expect("s.remove(5) should encode via fset dispatch");

    // Need insert declared for full axiom set; use a separate expression
    let _insert_term = encoder
        .encode_pure(&method_call(var("s"), "insert", vec![int(0)]))
        .expect("need insert to trigger fset axiom set");

    // Declare fset_contains before axiom assertion
    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    let five = encoder.solver.int_const(5);
    let contains_result = encoder.solver.apply(&fset_contains, &[remove_term, five]);

    // Assert: contains(remove(s,5), 5) — axiom says this is false
    encoder.solver.assert_term(contains_result);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_contains(fset_remove(s,5), 5) should be UNSAT via axiom, got: {result:?}"
    );
}

// ── Insert-frame-contains: x != y ==> contains(insert(s,x),y) == contains(s,y) ──

/// Encode `s.insert(5)` and `s.contains(7)` via dispatch, then verify
/// the frame axiom: inserting 5 does not affect membership of 7.
#[test]
#[timeout(30000)]
fn fset_insert_frame_contains_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let insert_expr = method_call(var("s"), "insert", vec![int(5)]);
    let insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("s.insert(5) should encode");

    let contains_s_7 = method_call(var("s"), "contains", vec![int(7)]);
    let contains_s_7_term = encoder
        .encode_pure(&contains_s_7)
        .expect("s.contains(7) should encode");

    encoder.assert_fset_axioms();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let seven = encoder.solver.int_const(7);
    let contains_insert_7 = encoder.solver.apply(&fset_contains, &[insert_term, seven]);

    // Frame: contains(insert(s,5), 7) == contains(s, 7) since 5 != 7
    let frame_eq = encoder.solver.iff(contains_insert_7, contains_s_7_term);
    let not_frame = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(not_frame);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "frame violation should be UNSAT (elem 5 != elem 7), got: {result:?}"
    );
}

// ── Nested dispatch: s.insert(5).contains(5) ──

/// Full nested dispatch: `s.insert(5).contains(5)` as a single PureExpr.
/// The `contains` dispatch must recognize the Int-sorted return of
/// `fset_insert` and route to fset_contains without explicit annotation.
#[test]
#[timeout(30000)]
fn fset_nested_insert_contains_full_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let insert_expr = method_call(var("s"), "insert", vec![int(5)]);
    let contains_on_insert = method_call(insert_expr, "contains", vec![int(5)]);

    let contains_term = encoder
        .encode_pure(&contains_on_insert)
        .expect("s.insert(5).contains(5) should encode");

    encoder.assert_fset_axioms();

    // Negate: NOT insert(s,5).contains(5)
    let not_contains = encoder.solver.not(contains_term);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT s.insert(5).contains(5) should be UNSAT via nested dispatch + axiom, got: {result:?}"
    );
}

// ── Remove-frame-contains: x != y ==> contains(remove(s,x),y) == contains(s,y) ──

/// Encode `s.remove(5)` and `s.contains(7)` via dispatch, then verify
/// the frame axiom: removing 5 does not affect membership of 7.
#[test]
#[timeout(30000)]
fn fset_remove_frame_contains_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let remove_expr = method_call(var("s"), "remove", vec![int(5)]);
    let remove_term = encoder
        .encode_pure(&remove_expr)
        .expect("s.remove(5) should encode");

    let contains_s_7 = method_call(var("s"), "contains", vec![int(7)]);
    let contains_s_7_term = encoder
        .encode_pure(&contains_s_7)
        .expect("s.contains(7) should encode");

    // Need insert for full axiom set
    let _insert = encoder
        .encode_pure(&method_call(var("s"), "insert", vec![int(0)]))
        .expect("need insert for axiom trigger");

    encoder.assert_fset_axioms();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let seven = encoder.solver.int_const(7);
    let contains_remove_7 = encoder.solver.apply(&fset_contains, &[remove_term, seven]);

    // Frame: contains(remove(s,5), 7) == contains(s, 7) since 5 != 7
    let frame_eq = encoder.solver.iff(contains_remove_7, contains_s_7_term);
    let not_frame = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(not_frame);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "remove frame violation should be UNSAT (elem 5 != elem 7), got: {result:?}"
    );
}

// ── Insert-non-empty: !is_empty(insert(s, x)) (#2547) ──

/// Verify that `is_empty(insert(s, x))` is refutable via the new
/// contains→non-empty and insert-non-empty axioms.
///
/// Before #2547, the FSet axioms could model `contains(insert(s,x), x) = true`
/// AND `is_empty(insert(s,x)) = true` simultaneously because there was no
/// bridge from membership to non-emptiness.
#[test]
#[timeout(30000)]
fn fset_insert_produces_non_empty_set_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let insert_expr = method_call(var("s"), "insert", vec![int(5)]);
    let insert_term = encoder
        .encode_pure(&insert_expr)
        .expect("s.insert(5) should encode via fset dispatch");

    // Declare fset_is_empty before axiom assertion
    let fset_is_empty = encoder.get_or_declare_spec_fn("fset_is_empty", &[Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    // Assert: is_empty(insert(s, 5)) — should be refutable
    let is_empty_ins = encoder.solver.apply(&fset_is_empty, &[insert_term]);
    encoder.solver.assert_term(is_empty_ins);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "is_empty(insert(s, 5)) should be UNSAT via insert-non-empty axiom (#2547), got: {result:?}"
    );
}

// ── Nested peek + contains: !is_empty(s) ==> contains(s, peek(s)) ─────

/// Nested dispatch: `s.contains(s.peek())` under the assumption `!s.is_empty()`.
///
/// This is the encode_pure-level companion to the UF-level axiom test in
/// `fset_axiom_tests.rs`: the nested `peek()` call becomes the argument to the
/// `contains()` dispatch, and the resulting term is discharged via the
/// non-empty peek-contains axiom.
#[test]
#[timeout(30000)]
fn fset_nested_peek_contains_nonempty_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_empty_expr = method_call(var("s"), "is_empty", vec![]);
    let is_empty_term = encoder
        .encode_pure(&is_empty_expr)
        .expect("s.is_empty() should encode");

    let peek_expr = method_call(var("s"), "peek", vec![]);
    let contains_peek_expr = method_call(var("s"), "contains", vec![peek_expr]);
    let contains_peek_term = encoder
        .encode_pure(&contains_peek_expr)
        .expect("s.contains(s.peek()) should encode");

    encoder.assert_fset_axioms();

    let not_empty = encoder.solver.not(is_empty_term);
    encoder.solver.assert_term(not_empty);
    let not_contains_peek = encoder.solver.not(contains_peek_term);
    encoder.solver.assert_term(not_contains_peek);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "!s.is_empty() && !s.contains(s.peek()) should be UNSAT via nested dispatch + FSet peek axiom, got: {result:?}"
    );
}

// ── FSet empty constant axioms (#2549) ──

/// Empty FSet contains no elements: `fset_contains(fset_empty, x)` is false.
///
/// Tests the empty-contains axiom added in #2549. Before this axiom,
/// `fset_empty` was a bare constant disconnected from `fset_contains`.
#[test]
#[timeout(30000)]
fn fset_empty_contains_no_elements_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode fset_empty through the logic_fn_call path, which hits the
    // canonical declare_const("fset_empty", Sort::Int) in call_encoding.rs.
    // This ensures the test uses the exact same term as the axiom system.
    let empty_expr = logic_fn_call("fset_empty", vec![]);
    let fset_empty = encoder
        .encode_pure(&empty_expr)
        .expect("fset_empty should encode via call_encoding special case");

    // Declare fset_contains via dispatch
    let contains_expr = method_call(var("s"), "contains", vec![int(42)]);
    let _contains_term = encoder
        .encode_pure(&contains_expr)
        .expect("s.contains(42) should encode via fset dispatch");

    encoder.assert_fset_axioms();

    let fset_contains =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);

    let x = encoder.solver.fresh_var("x", Sort::Int);
    let contains_empty_x = encoder.solver.apply(&fset_contains, &[fset_empty, x]);

    // Assert: fset_contains(fset_empty, x) — should be UNSAT
    encoder.solver.assert_term(contains_empty_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_contains(fset_empty, x) should be UNSAT via empty-contains axiom (#2549), got: {result:?}"
    );
}

/// Empty FSet has length zero and is_empty true.
///
/// Tests both the empty-len and empty-is_empty axioms from #2549.
#[test]
#[timeout(30000)]
fn fset_empty_len_zero_and_is_empty_true_via_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Ensure fset_contains is declared (required for axiom assertion path)
    let contains_expr = method_call(var("s"), "contains", vec![int(1)]);
    let _contains_term = encoder
        .encode_pure(&contains_expr)
        .expect("s.contains(1) should encode");

    // Declare len and is_empty
    let fset_len = encoder.get_or_declare_spec_fn("fset_len", &[Sort::Int], Sort::Int);
    let fset_is_empty = encoder.get_or_declare_spec_fn("fset_is_empty", &[Sort::Int], Sort::Bool);

    encoder.assert_fset_axioms();

    // Encode fset_empty through the logic_fn_call path for canonical term identity
    let empty_expr = logic_fn_call("fset_empty", vec![]);
    let fset_empty = encoder
        .encode_pure(&empty_expr)
        .expect("fset_empty should encode");

    // Assert: fset_len(fset_empty) != 0 OR !fset_is_empty(fset_empty)
    // Both should be refutable independently, but testing together is stronger
    let len_empty = encoder.solver.apply(&fset_len, &[fset_empty]);
    let zero = encoder.solver.int_const(0);
    let len_eq_zero = encoder.solver.eq(len_empty, zero);
    let len_neq_zero = encoder.solver.not(len_eq_zero);

    let is_empty_empty = encoder.solver.apply(&fset_is_empty, &[fset_empty]);
    let not_is_empty = encoder.solver.not(is_empty_empty);

    // Either len != 0 or !is_empty — both should be false for empty set
    let either = encoder.solver.or(len_neq_zero, not_is_empty);
    encoder.solver.assert_term(either);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_len(empty)!=0 OR !fset_is_empty(empty) should be UNSAT via empty axioms (#2549), got: {result:?}"
    );
}
