// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

// =============================================================================
// Singleton and Concat Tests (#379)
// =============================================================================

/// Test that seq![v] (single-element) encodes successfully via seq_singleton.
///
/// The `seq!` macro with one argument compiles to `LogicFnCall { name: "seq", args: [v] }`.
/// This should be intercepted in logic_fn.rs and routed to `encode_seq_singleton`.
#[test]
#[timeout(30000)]
fn test_encode_seq_singleton_basic() {
    let mut encoder = AYEncoder::new();

    // seq![42] — a singleton sequence containing 42
    let expr = logic_fn_call("seq", vec![int(42)]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "seq![42] should encode via seq_singleton: {result:?}"
    );
}

/// Axiom 13: len(singleton(v)) = 1.
///
/// Encodes: `seq![x].len() == 1` and checks UNSAT on its negation.
#[test]
#[timeout(30000)]
fn test_seq_axiom_singleton_len() {
    let mut encoder = AYEncoder::new();

    let x = var("x");

    // seq![x]
    let singleton = logic_fn_call("seq", vec![x]);

    // seq![x].len()
    let singleton_len = method_call(singleton, "len", vec![]);

    // seq![x].len() == 1
    let axiom_check = eq(singleton_len, int(1));

    let formula_term = encoder
        .encode_pure(&axiom_check)
        .expect("Singleton len formula should encode");

    // Assert NOT(axiom) and check UNSAT — proves axiom holds universally
    let neg_formula = encoder.solver.not(formula_term);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq axiom 13 (len(singleton(v)) = 1) should verify (expected UNSAT, got {result:?})"
    );
}

/// Axiom 14: index(singleton(v), 0) = v.
///
/// Encodes: `seq![x].index_logic(0) == x` and checks UNSAT on its negation.
#[test]
#[timeout(30000)]
fn test_seq_axiom_singleton_index() {
    let mut encoder = AYEncoder::new();

    let x = var("x");

    // seq![x]
    let singleton = logic_fn_call("seq", vec![x.clone()]);

    // seq![x].index_logic(0)
    let singleton_idx = method_call(singleton, "index_logic", vec![int(0)]);

    // seq![x].index_logic(0) == x
    let axiom_check = eq(singleton_idx, x);

    let formula_term = encoder
        .encode_pure(&axiom_check)
        .expect("Singleton index formula should encode");

    let neg_formula = encoder.solver.not(formula_term);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq axiom 14 (index(singleton(v), 0) = v) should verify (expected UNSAT, got {result:?})"
    );
}

/// Associated constructor syntax `Seq::singleton(v)` must route to the same
/// axiom-backed singleton encoding as `seq![v]`.
#[test]
#[timeout(30000)]
fn test_encode_seq_static_singleton_method_len() {
    let mut encoder = AYEncoder::new();

    let singleton = method_call(var("Seq"), "singleton", vec![int(7)]);
    let singleton_len = method_call(singleton, "len", vec![]);
    let eq_len = eq(singleton_len, int(1));

    let eq_term = encoder
        .encode_pure(&eq_len)
        .expect("Seq::singleton(v).len() should encode");
    let neg_eq = encoder.solver.not(eq_term);
    encoder.assert_term(neg_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq::singleton(v).len() == 1 should be provable, got {result:?}"
    );
}

/// Some parser paths preserve associated constructor syntax as a logic-function
/// call rather than a MethodCall. That spelling must also route to seq_singleton.
#[test]
#[timeout(30000)]
fn test_encode_seq_static_singleton_logic_fn_len() {
    let mut encoder = AYEncoder::new();

    let singleton = logic_fn_call("Seq::singleton", vec![int(7)]);
    let singleton_len = method_call(singleton, "len", vec![]);
    let eq_len = eq(singleton_len, int(1));

    let eq_term = encoder
        .encode_pure(&eq_len)
        .expect("Seq::singleton(v).len() logic-fn spelling should encode");
    let neg_eq = encoder.solver.not(eq_term);
    encoder.assert_term(neg_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq::singleton(v).len() logic-fn spelling should be provable, got {result:?}"
    );
}

/// Test that v@.concat(w@) encodes successfully via Seq encoding path.
#[test]
#[timeout(30000)]
fn test_encode_seq_concat_basic() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));
    let w_view_expr = view(var("w"));

    // v@.concat(w@)
    let expr = method_call(v_view_expr, "concat", vec![w_view_expr]);

    // Pre-scan for sort hints so both views get Seq sort
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "v@.concat(w@) should encode via Seq path: {result:?}"
    );
}

/// A bare variable used as the right operand of concat still needs a Seq sort
/// before argument encoding. This covers shapes like `ab.concat(bc)` where `bc`
/// is not wrapped in `View(...)`.
#[test]
#[timeout(30000)]
fn test_encode_seq_concat_bare_arg_gets_seq_hint_before_encoding() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(view(var("ab")), "concat", vec![var("bc")]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "v@.concat(bare_var) should pre-hint the bare arg as Seq: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_concat_annotated_bare_receiver_and_arg() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(
        var_with_sort("ab", ExprSort::Seq),
        "concat",
        vec![var_with_sort("bc", ExprSort::Seq)],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Seq-annotated ab.concat(bc) should encode through Seq path: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_seq_concat_prescan_tags_bare_arg_as_seq() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("ab"), "concat", vec![var("bc")]);
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let bc_term = encoder
        .encode_pure(&var("bc"))
        .expect("bare concat arg should encode after prescan");
    let sort = encoder.solver.get_sort(bc_term);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "concat prescan should declare bare arg as Seq, got {sort:?}"
    );
}

/// Concat of two concrete Seq literals now synthesizes a concrete SeqValue.
///
/// `encode_seq_operation_impl` registers Array+Length+Offset backing when the
/// left operand has a known concrete length, so downstream indexing can avoid
/// the UF-only fallback path.
#[test]
#[timeout(30000)]
fn test_encode_seq_concat_literal_registers_seq_value_with_known_len() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(
        logic_fn_call("seq", vec![int(10)]),
        "concat",
        vec![logic_fn_call("seq", vec![int(20), int(30)])],
    );

    let result = encoder
        .encode_pure(&expr)
        .expect("literal concat should encode");
    let known_len = encoder
        .seq_state_for_test()
        .get_seq_value(&result)
        .and_then(|sv| sv.known_len);

    assert_eq!(
        known_len,
        Some(3),
        "literal concat should synthesize a SeqValue with known_len=3"
    );

    let len_term = encoder.seq_len_term(result).expect("concat len");
    let three = encoder.solver.int_const(3);
    let eq = encoder.solver.eq(len_term, three);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "len(seq![10].concat(seq![20, 30])) should be 3"
    );
}

/// The synthesized SeqValue must preserve element order across the concat
/// boundary so `index_logic(1)` reads the first element of the right operand.
#[test]
#[timeout(30000)]
fn test_encode_seq_concat_literal_boundary_index_uses_synthesized_seq_value() {
    let mut encoder = AYEncoder::new();

    let concat_expr = method_call(
        logic_fn_call("seq", vec![int(10)]),
        "concat",
        vec![logic_fn_call("seq", vec![int(20), int(30)])],
    );
    let index_expr = method_call(concat_expr, "index_logic", vec![int(1)]);

    let index_term = encoder
        .encode_pure(&index_expr)
        .expect("literal concat index should encode");
    let twenty = encoder.solver.int_const(20);
    let eq = encoder.solver.eq(index_term, twenty);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "seq![10].concat(seq![20, 30])[1] should equal 20"
    );
}

/// Concat only synthesizes a SeqValue when the left operand has known concrete
/// length. A symbolic left operand should keep the result opaque.
#[test]
#[timeout(30000)]
fn test_encode_seq_concat_unknown_left_keeps_result_without_seq_value() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(
        view(var("v")),
        "concat",
        vec![logic_fn_call("seq", vec![int(1)])],
    );

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    let result = encoder
        .encode_pure(&expr)
        .expect("symbolic-left concat should encode");

    assert!(
        !encoder.seq_state_for_test().has_seq_value(&result),
        "concat should stay opaque when the left operand has no known_len"
    );
}

/// Axiom 15: len(concat(s1, s2)) = len(s1) + len(s2).
///
/// Encodes: `v@.concat(w@).len() == v@.len() + w@.len()` and checks UNSAT.
#[test]
#[timeout(30000)]
fn test_seq_axiom_concat_len() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));
    let w_view_expr = view(var("w"));

    // v@.concat(w@)
    let concat_expr = method_call(v_view_expr.clone(), "concat", vec![w_view_expr.clone()]);

    // v@.concat(w@).len()
    let concat_len = method_call(concat_expr, "len", vec![]);

    // v@.len()
    let v_len = method_call(v_view_expr, "len", vec![]);

    // w@.len()
    let w_len = method_call(w_view_expr, "len", vec![]);

    // v@.len() + w@.len()
    let sum_len = add(v_len, w_len);

    // v@.concat(w@).len() == v@.len() + w@.len()
    let axiom_check = eq(concat_len, sum_len);

    // Pre-scan for sort hints
    encoder.register_sort_hints(std::slice::from_ref(&axiom_check));

    let formula_term = encoder
        .encode_pure(&axiom_check)
        .expect("Concat len formula should encode");

    let neg_formula = encoder.solver.not(formula_term);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq axiom 15 (len(concat(s1, s2)) = len(s1) + len(s2)) should verify (expected UNSAT, got {result:?})"
    );
}

/// Axiom 16: left indexing through concat.
///
/// Encodes: `v@.len() > 0 => v@.concat(w@).index_logic(0) == v@.index_logic(0)`
/// and checks UNSAT on its negation.
#[test]
#[timeout(30000)]
fn test_seq_axiom_concat_left_index() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));
    let w_view_expr = view(var("w"));

    // v@.concat(w@)
    let concat_expr = method_call(v_view_expr.clone(), "concat", vec![w_view_expr]);

    // v@.concat(w@).index_logic(0)
    let concat_idx_0 = method_call(concat_expr, "index_logic", vec![int(0)]);

    // v@.index_logic(0)
    let v_idx_0 = method_call(v_view_expr.clone(), "index_logic", vec![int(0)]);

    // v@.len() > 0 (precondition: v@ is non-empty so index 0 is in left range)
    let v_len = method_call(v_view_expr, "len", vec![]);
    let precond = gt(v_len, int(0));

    // v@.concat(w@).index_logic(0) == v@.index_logic(0)
    let idx_eq = eq(concat_idx_0, v_idx_0);

    // precond => idx_eq
    let axiom_check = implies(precond, idx_eq);

    encoder.register_sort_hints(std::slice::from_ref(&axiom_check));

    let formula_term = encoder
        .encode_pure(&axiom_check)
        .expect("Concat left index formula should encode");

    let neg_formula = encoder.solver.not(formula_term);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq axiom 16 (concat left index) should be UNSAT, got {result:?}"
    );
}

/// `to_owned_seq` is a logical identity at the SMT level: the encoder should
/// return the already-encoded receiver term rather than allocating a new UF.
#[test]
#[timeout(30000)]
fn test_encode_seq_to_owned_seq_returns_receiver_term() {
    let mut encoder = AYEncoder::new();

    let receiver = view(var("v"));
    let expr = method_call(receiver.clone(), "to_owned_seq", vec![]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    let receiver_term = encoder
        .encode_pure(&receiver)
        .expect("receiver should encode");
    let result_term = encoder
        .encode_pure(&expr)
        .expect("to_owned_seq should encode");

    assert_eq!(
        result_term, receiver_term,
        "to_owned_seq should return the receiver term unchanged"
    );
}

/// Test concat with wrong argument count produces error.
#[test]
#[timeout(30000)]
fn test_encode_seq_concat_wrong_args() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));

    // v@.concat(a, b) — wrong: 2 args instead of 1
    let expr = method_call(v_view_expr, "concat", vec![int(1), int(2)]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "concat with 2 args should produce an error: {result:?}"
    );
}
