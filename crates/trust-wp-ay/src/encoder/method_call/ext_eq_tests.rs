// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `ext_eq.rs` Tseitin-style extensional equality encoding.
//!
//! Covers:
//! - Seq vs non-Seq dispatch routing
//! - Forward Tseitin axioms (length equality, pointwise element equality)
//! - Reverse ground axiom (term equality => ext_eq)
//! - Congruence bridge across multiple ext_eq encodings
//! - Concat length axiom injection
//! - Concat identity for seq_empty operands
//! - Non-Seq Bool UF fallback

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{ExprSort, PureExpr};

use crate::{
    encoder::AYEncoder,
    tests::helpers::{eq, int, logic_fn_call, method_call, var, var_with_sort, view},
};

// ── Helper: build ext_eq method call ────────────────────────────────

fn ext_eq_call(receiver: PureExpr, other: PureExpr) -> PureExpr {
    method_call(receiver, "ext_eq", vec![other])
}

fn seq_var(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::Seq)
}

fn concat_call(receiver: PureExpr, other: PureExpr) -> PureExpr {
    method_call(receiver, "concat", vec![other])
}

fn seq_empty_logic_fn() -> PureExpr {
    PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    }
}

fn seq_empty_method() -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("Seq".to_string(), None)),
        method: "empty".to_string(),
        args: vec![],
    }
}

// ── Non-Seq fallback path ───────────────────────────────────────────

#[test]
#[timeout(30000)]
fn ext_eq_non_seq_produces_bool_uf() {
    let mut encoder = AYEncoder::new();
    let expr = ext_eq_call(var("x"), var("y"));
    let term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq on bare vars");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(sort, Sort::Bool, "non-Seq ext_eq should return Bool");
}

#[test]
#[timeout(30000)]
fn ext_eq_non_seq_no_seq_theory_initialized() {
    let mut encoder = AYEncoder::new();
    let expr = ext_eq_call(var("x"), var("y"));
    let _term = encoder.encode_pure(&expr).expect("encode ext_eq");
    assert!(
        encoder.seq_state.funcs_clone().is_none(),
        "non-Seq ext_eq should not initialize Seq theory"
    );
}

#[test]
#[timeout(30000)]
fn ext_eq_non_seq_fallback_reuses_uf_decl() {
    let mut encoder = AYEncoder::new();
    let expr1 = ext_eq_call(var("a"), var("b"));
    let expr2 = ext_eq_call(var("c"), var("d"));
    let _t1 = encoder.encode_pure(&expr1).expect("first ext_eq");
    let count_after_first = encoder.decls.logic_func_count();
    let _t2 = encoder.encode_pure(&expr2).expect("second ext_eq");
    // Same UF signature (Int, Int) -> Bool should reuse the declaration
    assert_eq!(
        encoder.decls.logic_func_count(),
        count_after_first,
        "repeated non-Seq ext_eq with same sort signature should reuse UF decl"
    );
}

// ── Seq path: basic dispatch ────────────────────────────────────────

#[test]
#[timeout(30000)]
fn ext_eq_seq_annotated_produces_bool_term() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = ext_eq_call(seq_var("a"), seq_var("b"));
    encoder.register_sort_hints(&[expr.clone()]);
    let term = encoder.encode_pure(&expr).expect("encode Seq ext_eq");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "Seq ext_eq should return Bool (Tseitin var)"
    );
}

#[test]
#[timeout(30000)]
fn ext_eq_seq_initializes_seq_theory() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = ext_eq_call(seq_var("a"), seq_var("b"));
    encoder.register_sort_hints(&[expr.clone()]);
    let _term = encoder.encode_pure(&expr).expect("encode Seq ext_eq");
    assert!(
        encoder.seq_state.funcs_clone().is_some(),
        "Seq ext_eq should initialize Seq theory"
    );
}

#[test]
#[timeout(30000)]
fn ext_eq_seq_populates_registry() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = ext_eq_call(seq_var("a"), seq_var("b"));
    encoder.register_sort_hints(&[expr.clone()]);
    let _term = encoder.encode_pure(&expr).expect("encode Seq ext_eq");
    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        1,
        "encoding one ext_eq should add one registry entry"
    );
}

// ── Seq path: forward length axiom ──────────────────────────────────

/// ext_eq(a, b) => len(a) == len(b)
/// So: ext_eq(a, b) AND len(a) != len(b) should be UNSAT.
#[test]
#[timeout(30000)]
fn ext_eq_seq_forward_length_axiom_is_sound() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let b = seq_var("b");
    let expr = ext_eq_call(a.clone(), b.clone());
    encoder.register_sort_hints(&[expr.clone()]);

    let ext_eq_term = encoder.encode_pure(&expr).expect("encode ext_eq");
    encoder.assert_term(ext_eq_term);

    // Assert len(a) != len(b) using Seq length terms directly
    let a_term = encoder.encode_pure(&a).expect("encode a");
    let b_term = encoder.encode_pure(&b).expect("encode b");
    let len_a = encoder.seq_len_term(a_term).expect("len(a)");
    let len_b = encoder.seq_len_term(b_term).expect("len(b)");
    let len_neq = encoder.solver.neq(len_a, len_b);
    encoder.assert_term(len_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq AND len(a) != len(b) should be UNSAT via forward length axiom, got {result:?}"
    );
}

// ── Seq path: reverse term equality axiom ───────────────────────────

/// terms_equal => ext_eq. So: a == b AND NOT ext_eq(a, b) should be UNSAT.
#[test]
#[timeout(30000)]
fn ext_eq_seq_reverse_term_equality_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let b = seq_var("b");
    let expr = ext_eq_call(a.clone(), b.clone());
    encoder.register_sort_hints(&[expr.clone()]);

    let ext_eq_term = encoder.encode_pure(&expr).expect("encode ext_eq");

    // Assert a == b (as SMT terms)
    let a_term = encoder.encode_pure(&a).expect("encode a");
    let b_term = encoder.encode_pure(&b).expect("encode b");
    let terms_eq = encoder.solver.eq(a_term, b_term);
    encoder.assert_term(terms_eq);

    // Assert NOT ext_eq
    let not_ext_eq = encoder.solver.not(ext_eq_term);
    encoder.assert_term(not_ext_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "a == b AND NOT ext_eq(a, b) should be UNSAT via reverse axiom, got {result:?}"
    );
}

// ── Seq path: congruence bridge ─────────────────────────────────────

/// Two ext_eq calls sharing the same receiver. If ext_eq(orig, old) holds
/// and old == new, then ext_eq(orig, new) must hold via congruence bridge.
#[test]
#[timeout(30000)]
fn ext_eq_congruence_bridge_closes_preservation() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let orig = seq_var("orig");
    let old = seq_var("old");
    let new = seq_var("new");

    let ext_eq_old = ext_eq_call(orig.clone(), old.clone());
    let ext_eq_new = ext_eq_call(orig.clone(), new.clone());
    encoder.register_sort_hints(&[ext_eq_old.clone(), ext_eq_new.clone()]);

    // Encode and assert ext_eq(orig, old)
    let old_term = encoder.encode_pure(&ext_eq_old).expect("encode ext_eq_old");
    encoder.assert_term(old_term);

    // Assert old == new through the same finite Seq equality boundary used by
    // production VCs. Raw native-Seq equality is deliberately not trusted to
    // authenticate Array+Length+Offset components.
    let old_val = encoder.encode_pure(&old).expect("encode old");
    let new_val = encoder.encode_pure(&new).expect("encode new");
    encoder.assert_eq(old_val, new_val);

    // Encode ext_eq(orig, new) — should create congruence bridge
    let new_term = encoder.encode_pure(&ext_eq_new).expect("encode ext_eq_new");
    assert!(
        encoder.encoding_cache.ext_eq_registry_len() >= 2,
        "two ext_eq calls should create two registry entries"
    );

    // Negate ext_eq(orig, new) — should be UNSAT via bridge
    let not_new = encoder.solver.not(new_term);
    encoder.assert_term(not_new);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq(orig, old) AND old == new AND NOT ext_eq(orig, new) should be UNSAT via congruence bridge, got {result:?}"
    );
}

/// Bridge only fires when the receiver matches. Two ext_eq calls with
/// different receivers should NOT produce a bridge.
#[test]
#[timeout(30000)]
fn ext_eq_no_bridge_for_different_receivers() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let b = seq_var("b");
    let c = seq_var("c");
    let d = seq_var("d");

    let ext_eq_ab = ext_eq_call(a.clone(), b.clone());
    let ext_eq_cd = ext_eq_call(c.clone(), d.clone());
    encoder.register_sort_hints(&[ext_eq_ab.clone(), ext_eq_cd.clone()]);

    // Encode both ext_eq calls
    let ab_term = encoder
        .encode_pure(&ext_eq_ab)
        .expect("encode ext_eq(a, b)");
    let bridge_count_after_ab = encoder.encoding_cache.ext_eq_bridge_count();
    let cd_term = encoder
        .encode_pure(&ext_eq_cd)
        .expect("encode ext_eq(c, d)");
    let bridge_count_after_cd = encoder.encoding_cache.ext_eq_bridge_count();

    assert_eq!(
        bridge_count_after_ab, bridge_count_after_cd,
        "encoding ext_eq(c, d) must not add a congruence bridge for prior ext_eq(a, b)"
    );
    assert_ne!(
        ab_term, cd_term,
        "different receiver ext_eq calls should produce distinct Tseitin terms"
    );
}

// ── Seq path: concat length axiom ───────────────────────────────────

/// ext_eq(a, b.concat(c)) => len(a) == len(b) + len(c)
#[test]
#[timeout(30000)]
fn ext_eq_concat_operand_asserts_length_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let b = seq_var("b");
    let c = seq_var("c");
    let concat_bc = concat_call(b.clone(), c.clone());
    let expr = ext_eq_call(a.clone(), concat_bc);
    encoder.register_sort_hints(&[expr.clone(), b.clone(), c.clone()]);

    let ext_eq_term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq with concat");
    encoder.assert_term(ext_eq_term);

    // Get len terms for a, b, c
    let a_val = encoder.encode_pure(&a).expect("encode a");
    let b_val = encoder.encode_pure(&b).expect("encode b");
    let c_val = encoder.encode_pure(&c).expect("encode c");
    let len_a = encoder.seq_len_term(a_val).expect("len(a)");
    let len_b = encoder.seq_len_term(b_val).expect("len(b)");
    let len_c = encoder.seq_len_term(c_val).expect("len(c)");

    // Assert len(a) != len(b) + len(c)
    let sum_bc = encoder.solver.add(len_b, len_c);
    let neq = encoder.solver.neq(len_a, sum_bc);
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq with concat operand AND len(a) != len(b)+len(c) should be UNSAT, got {result:?}"
    );
}

/// Non-opaque singleton-prefix concat still carries normal ext_eq length
/// semantics. Only symbolic iterator shapes like `seq![v].concat(next@)` get
/// the scoped solver workaround.
#[test]
#[timeout(30000)]
fn ext_eq_int_singleton_concat_keeps_length_semantics() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let next = seq_var("next");
    let singleton_one = logic_fn_call("seq", vec![int(1)]);
    let concat = concat_call(singleton_one, next.clone());
    let expr = ext_eq_call(a.clone(), concat);
    encoder.register_sort_hints(&[expr.clone(), next.clone()]);

    let ext_eq_term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq with int singleton concat");
    encoder.assert_term(ext_eq_term);

    let a_term = encoder.encode_pure(&a).expect("encode a");
    let next_term = encoder.encode_pure(&next).expect("encode next");
    let len_a = encoder.seq_len_term(a_term).expect("len(a)");
    let len_next = encoder.seq_len_term(next_term).expect("len(next)");
    let one = encoder.solver.int_const(1);
    let expected_len = encoder.solver.add(one, len_next);
    let neq = encoder.solver.neq(len_a, expected_len);
    encoder.assert_term(neq);
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq(a, seq![1].concat(next)) must imply len(a) == 1 + len(next), got {result:?}"
    );
}

/// The iterator decomposition base context
///   len(vec) == 3
///   index(vec, 0) == v
///   ext_eq(view(vec), concat(seq![v], view(next)))
/// is consistent. If this becomes UNSAT, refutation-based verification can
/// incorrectly prove `false` by vacuity.
#[test]
#[timeout(30000)]
fn ext_eq_singleton_concat_base_context_is_not_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let vec_view = view(var("vec"));
    let next_view = view(var("next"));
    let v = var("v");
    let singleton_v = logic_fn_call("seq", vec![v.clone()]);
    let concat = concat_call(singleton_v, next_view);
    let ext_eq_expr = ext_eq_call(vec_view.clone(), concat);
    let assumptions = vec![
        eq(method_call(vec_view.clone(), "len", vec![]), int(3)),
        eq(method_call(vec_view, "index", vec![int(0)]), v),
        ext_eq_expr,
    ];
    encoder.register_sort_hints(&assumptions);

    for assumption in &assumptions {
        let term = encoder
            .encode_pure(assumption)
            .expect("base context assumption should encode");
        encoder.assert_term(term);
    }
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "singleton-prefix ext_eq base context must be SAT or Unknown, got {result:?}"
    );
}

/// The singleton-prefix produces relation alone must not constrain the
/// produced element to the array default value.
#[test]
#[timeout(30000)]
fn ext_eq_singleton_concat_does_not_force_element_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let v = var("v");
    let singleton_v = logic_fn_call("seq", vec![v.clone()]);
    let concat = concat_call(singleton_v, view(var("next")));
    let ext_eq_expr = ext_eq_call(view(var("vec")), concat);
    encoder.register_sort_hints(std::slice::from_ref(&ext_eq_expr));

    let ext_eq_term = encoder
        .encode_pure(&ext_eq_expr)
        .expect("singleton-prefix ext_eq should encode");
    encoder.assert_term(ext_eq_term);
    let v_term = encoder.encode_pure(&v).expect("v should encode");
    let zero = encoder.solver.int_const(0);
    let v_ne_zero = encoder.solver.neq(v_term, zero);
    encoder.assert_term(v_ne_zero);
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "singleton-prefix ext_eq must not force v == 0, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn seq_singleton_does_not_force_element_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let v = var("v");
    let singleton_v = logic_fn_call("seq", vec![v.clone()]);
    let _singleton_term = encoder
        .encode_pure(&singleton_v)
        .expect("singleton should encode");
    let v_term = encoder.encode_pure(&v).expect("v should encode");
    let zero = encoder.solver.int_const(0);
    let v_ne_zero = encoder.solver.neq(v_term, zero);
    encoder.assert_term(v_ne_zero);
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "seq![v] must not force v == 0, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn seq_singleton_concat_does_not_force_element_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let v = var("v");
    let singleton_v = logic_fn_call("seq", vec![v.clone()]);
    let concat = concat_call(singleton_v, view(var("next")));
    encoder.register_sort_hints(std::slice::from_ref(&concat));
    let _concat_term = encoder
        .encode_pure(&concat)
        .expect("singleton-prefix concat should encode");
    let v_term = encoder.encode_pure(&v).expect("v should encode");
    let zero = encoder.solver.int_const(0);
    let v_ne_zero = encoder.solver.neq(v_term, zero);
    encoder.assert_term(v_ne_zero);
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "seq![v].concat(next@) must not force v == 0, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn seq_unknown_len_and_index_value_is_satisfiable() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let vec_view = view(var("vec"));
    let assumptions = vec![
        eq(method_call(vec_view.clone(), "len", vec![]), int(3)),
        eq(method_call(vec_view, "index", vec![int(0)]), int(42)),
    ];
    encoder.register_sort_hints(&assumptions);
    for assumption in &assumptions {
        let term = encoder
            .encode_pure(assumption)
            .expect("base seq assumption should encode");
        encoder.assert_term(term);
    }
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "unknown Seq len/index base must be SAT or Unknown, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn seq_unknown_len_index_and_singleton_concat_is_satisfiable() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let vec_view = view(var("vec"));
    let singleton_v = logic_fn_call("seq", vec![var("v")]);
    let concat = concat_call(singleton_v, view(var("next")));
    let assumptions = vec![
        eq(method_call(vec_view.clone(), "len", vec![]), int(3)),
        eq(method_call(vec_view, "index", vec![int(0)]), int(42)),
    ];
    encoder.register_sort_hints(&[
        assumptions[0].clone(),
        assumptions[1].clone(),
        concat.clone(),
    ]);
    for assumption in &assumptions {
        let term = encoder
            .encode_pure(assumption)
            .expect("base seq assumption should encode");
        encoder.assert_term(term);
    }
    let _concat_term = encoder
        .encode_pure(&concat)
        .expect("singleton-prefix concat should encode");
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "unknown Seq len/index plus singleton concat must be SAT or Unknown, got {result:?}"
    );
}

// ── Seq path: concat identity for seq_empty ─────────────────────────

/// ext_eq encoding with seq_empty().concat(s) asserts concat(empty, s) = s.
#[test]
#[timeout(30000)]
fn ext_eq_concat_left_identity_with_seq_empty_logic_fn() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let s = seq_var("s");
    let empty_concat_s = concat_call(seq_empty_logic_fn(), s.clone());
    let expr = ext_eq_call(a.clone(), empty_concat_s);
    encoder.register_sort_hints(&[expr.clone(), s.clone()]);

    let ext_eq_term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq with empty concat");
    encoder.assert_term(ext_eq_term);

    // The identity axiom says concat(empty, s) = s. With ext_eq asserting
    // len(a) = len(concat(empty, s)), and concat(empty, s) = s,
    // we get len(a) = len(s). Assert len(a) != len(s) => UNSAT.
    let a_val = encoder.encode_pure(&a).expect("encode a");
    let s_val = encoder.encode_pure(&s).expect("encode s");
    let len_a = encoder.seq_len_term(a_val).expect("len(a)");
    let len_s = encoder.seq_len_term(s_val).expect("len(s)");
    let neq = encoder.solver.neq(len_a, len_s);
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq with seq_empty().concat(s) should propagate concat identity, got {result:?}"
    );
}

/// Direct identity fast path: `ext_eq(s, seq_empty().concat(s))` is a ground truth.
#[test]
#[timeout(30000)]
fn ext_eq_concat_left_identity_trivially_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let s = seq_var("s_identity");
    let expr = ext_eq_call(s.clone(), concat_call(seq_empty_logic_fn(), s));
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let ext_eq_term = encoder.encode_pure(&expr).expect("encode ext_eq identity");
    let negated = encoder.solver.not(ext_eq_term);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT ext_eq(s, seq_empty().concat(s)) should be UNSAT, got {result:?}"
    );
}

/// Same identity but using the MethodCall form: Seq::empty().concat(s).
#[test]
#[timeout(30000)]
fn ext_eq_concat_left_identity_with_seq_empty_method() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let s = seq_var("s2");
    let empty_concat_s = concat_call(seq_empty_method(), s.clone());
    let expr = ext_eq_call(a.clone(), empty_concat_s);
    encoder.register_sort_hints(&[expr.clone(), s.clone()]);

    let ext_eq_term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq with empty method concat");
    encoder.assert_term(ext_eq_term);

    let a_val = encoder.encode_pure(&a).expect("encode a");
    let s_val = encoder.encode_pure(&s).expect("encode s2");
    let len_a = encoder.seq_len_term(a_val).expect("len(a)");
    let len_s = encoder.seq_len_term(s_val).expect("len(s2)");
    let neq = encoder.solver.neq(len_a, len_s);
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq::empty().concat(s) identity should propagate, got {result:?}"
    );
}

// ── Seq path: right identity for seq_empty concat ───────────────────

/// ext_eq(a, s.concat(seq_empty())) asserts concat(s, empty) = s.
#[test]
#[timeout(30000)]
fn ext_eq_concat_right_identity_with_seq_empty() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = seq_var("a");
    let s = seq_var("s3");
    let s_concat_empty = concat_call(s.clone(), seq_empty_logic_fn());
    let expr = ext_eq_call(a.clone(), s_concat_empty);
    encoder.register_sort_hints(&[expr.clone(), s.clone()]);

    let ext_eq_term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq with right-empty concat");
    encoder.assert_term(ext_eq_term);

    let a_val = encoder.encode_pure(&a).expect("encode a");
    let s_val = encoder.encode_pure(&s).expect("encode s3");
    let len_a = encoder.seq_len_term(a_val).expect("len(a)");
    let len_s = encoder.seq_len_term(s_val).expect("len(s3)");
    let neq = encoder.solver.neq(len_a, len_s);
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "s.concat(seq_empty()) identity should propagate, got {result:?}"
    );
}

// ── Seq path: ext_eq with view-wrapped receivers ────────────────────

/// ext_eq on View-wrapped Seq receivers should still route to Seq path.
#[test]
#[timeout(30000)]
fn ext_eq_view_wrapped_seq_receivers_route_to_seq_path() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = view(seq_var("a"));
    let b = view(seq_var("b"));
    let expr = ext_eq_call(a, b);
    encoder.register_sort_hints(&[expr.clone()]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode view-wrapped ext_eq");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "view-wrapped Seq ext_eq should return Bool"
    );
    assert!(
        encoder.seq_state.funcs_clone().is_some(),
        "view-wrapped Seq ext_eq should initialize Seq theory"
    );
}

// ── Seq path: sort hint propagation ─────────────────────────────────

/// ext_eq receiver sort hints should be propagated into the encoder.
#[test]
#[timeout(30000)]
fn ext_eq_seq_records_sort_hints_for_receivers() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // Use view(var("p")) — resolve_view_var_name should extract "p"
    let p = view(var("p"));
    let q = view(var("q"));
    let expr = ext_eq_call(p, q);

    // Record Seq hints manually so is_seq_receiver succeeds
    encoder.record_sort_hint("p".to_string(), ExprSort::Seq);
    encoder.record_sort_hint("q".to_string(), ExprSort::Seq);

    let _term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq with view vars");
    // The ext_eq encoder should have re-confirmed Seq hints for both receivers
    assert!(
        encoder.encoding_cache.ext_eq_registry_len() == 1,
        "ext_eq should populate registry"
    );
}

// ── Mixed Seq/non-Seq: one Seq operand triggers Seq path ────────────

#[test]
#[timeout(30000)]
fn ext_eq_one_seq_operand_triggers_seq_path() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // Only receiver is Seq-annotated, other is bare
    let expr = ext_eq_call(seq_var("a"), var("b"));
    encoder.register_sort_hints(&[expr.clone()]);
    let _term = encoder.encode_pure(&expr).expect("encode mixed ext_eq");
    assert!(
        encoder.seq_state.funcs_clone().is_some(),
        "one Seq operand should trigger Seq path"
    );
    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        1,
        "should populate registry on Seq path"
    );
}

// ── Seq path: multiple ext_eq calls accumulate in registry ──────────

#[test]
#[timeout(30000)]
fn ext_eq_multiple_calls_accumulate_registry_entries() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let exprs = vec![
        ext_eq_call(seq_var("a"), seq_var("b")),
        ext_eq_call(seq_var("c"), seq_var("d")),
        ext_eq_call(seq_var("a"), seq_var("e")),
    ];
    for expr in &exprs {
        encoder.register_sort_hints(&[expr.clone()]);
    }
    for expr in &exprs {
        let _term = encoder.encode_pure(expr).expect("encode ext_eq");
    }
    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        3,
        "three ext_eq calls should create three registry entries"
    );
}

// ── Soundness: ext_eq is not trivially true ─────────────────────────

/// ext_eq should not be trivially true — it must be possible for
/// NOT ext_eq(a, b) to be satisfiable when a != b.
#[test]
#[timeout(30000)]
fn ext_eq_seq_not_trivially_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = ext_eq_call(seq_var("a"), seq_var("b"));
    encoder.register_sort_hints(&[expr.clone()]);
    let ext_eq_term = encoder.encode_pure(&expr).expect("encode ext_eq");

    // Assert NOT ext_eq(a, b) — should be SAT (ext_eq is not tautological)
    let not_ext_eq = encoder.solver.not(ext_eq_term);
    encoder.assert_term(not_ext_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat | SolveResult::Unknown),
        "NOT ext_eq(a, b) should be SAT (ext_eq is not trivially true), got {result:?}"
    );
}

/// ext_eq should not be trivially false either — it must be possible for
/// ext_eq(a, b) to be satisfiable.
#[test]
#[timeout(30000)]
fn ext_eq_seq_not_trivially_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = ext_eq_call(seq_var("a"), seq_var("b"));
    encoder.register_sort_hints(&[expr.clone()]);
    let ext_eq_term = encoder.encode_pure(&expr).expect("encode ext_eq");

    encoder.assert_term(ext_eq_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat | SolveResult::Unknown),
        "ext_eq(a, b) should be SAT (sequences can be equal), got {result:?}"
    );
}

// ── Performance: ext_eq_registry growth ─────────────────────────────

/// The ext_eq_registry is a `Vec<(Term, Term, Term)>` capped at
/// `TRUST_WP_EXT_EQ_REGISTRY_CAP` (50). Each new ext_eq encoding scans all
/// previous entries with the same receiver (ext_eq.rs:267-272),
/// making the total registration work O(R²) where R is the registry size.
///
/// The preservation bridge in `seq_instances.rs:305-358` also iterates
/// over all (i, j) pairs in the registry — O(R²) per receiver bucket.
/// The inner push_back/push_front membership checks use pre-indexed
/// HashMap/HashSet lookups, so the remaining bridge cost is O(R²×P)
/// where P is the number of push_back entries for a matched prefix.
/// The bridge is capped at `TRUST_WP_EXT_EQ_BRIDGE_BUDGET` (40) (#2708).
///
/// This test registers 50 ext_eq encodings (sharing a receiver) and
/// verifies the bridge construction completes within the timeout. At
/// 50 entries the nested loop does 50×49/2 = 1225 pairs, well within
/// bounds. The test documents the quadratic bound and guards against
/// accidental removal of the early-exit `r_i != r_j` filter.
#[test]
#[timeout(30000)]
fn perf_ext_eq_registry_50_entries_completes_in_time() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register sort hints for a shared receiver.
    let receiver = seq_var("shared_recv");
    let first_other = seq_var("other_0");
    let first_expr = ext_eq_call(receiver.clone(), first_other);
    encoder.register_sort_hints(&[first_expr.clone()]);

    // Encode 50 ext_eq calls all sharing the same receiver.
    // Each registration scans all previous entries → O(R²) total.
    for i in 0..50 {
        let other = seq_var(&format!("other_{i}"));
        let expr = ext_eq_call(receiver.clone(), other);
        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "ext_eq #{i} should encode successfully: {:?}",
            result.err()
        );
    }

    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        50,
        "50 ext_eq calls should produce 50 registry entries"
    );

    // Trigger the ground instance assertion which contains the
    // O(R²) nested loop over the registry.
    let count = encoder.assert_standard_ground_instances();
    // count may be 0 if no push_back/push_front entries exist — that's fine.
    // The test proves the loop terminates within the timeout.
    assert!(
        count < 100_000,
        "ground instance count should be bounded, got {count}"
    );
}

/// Verify that `ext_eq_registry` respects `TRUST_WP_EXT_EQ_REGISTRY_CAP` (50).
/// Entries beyond the cap are silently dropped (fail-closed: may return
/// Unknown, never strengthens the VC). (#2535)
#[test]
#[timeout(30000)]
fn ext_eq_registry_respects_cap() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let receiver = seq_var("cap_recv");
    let first_other = seq_var("cap_other_0");
    let first_expr = ext_eq_call(receiver.clone(), first_other);
    encoder.register_sort_hints(&[first_expr.clone()]);

    // Encode 60 ext_eq calls (10 beyond the 50-entry cap).
    for i in 0..60 {
        let other = seq_var(&format!("cap_other_{i}"));
        let expr = ext_eq_call(receiver.clone(), other);
        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "ext_eq #{i} should encode even beyond cap: {:?}",
            result.err()
        );
    }

    // Registry must stay at the cap, not grow to 60.
    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        50,
        "ext_eq_registry should be capped at 50, not grow unbounded"
    );
}

/// Verify that congruence bridge assertions are capped at
/// `TRUST_WP_MAX_CONGRUENCE_BRIDGES` (100). Without the cap, 50 ext_eq entries
/// sharing a receiver would produce 50*49/2 = 1225 bridges (O(n^2)).
/// With the cap, total bridges are bounded at 100. (#2708)
#[test]
#[timeout(30000)]
fn ext_eq_congruence_bridge_respects_cap() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let receiver = seq_var("bridge_cap_recv");
    let first_other = seq_var("bridge_cap_other_0");
    let first_expr = ext_eq_call(receiver.clone(), first_other);
    encoder.register_sort_hints(&[first_expr.clone()]);

    // Encode 50 ext_eq calls all sharing the same receiver.
    // Without the cap, this would produce 0+1+2+...+49 = 1225 bridges.
    // With TRUST_WP_MAX_CONGRUENCE_BRIDGES=100, total bridges should stop at 100.
    for i in 0..50 {
        let other = seq_var(&format!("bridge_cap_other_{i}"));
        let expr = ext_eq_call(receiver.clone(), other);
        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "ext_eq #{i} should encode successfully: {:?}",
            result.err()
        );
    }

    // The bridge count should be capped at 100, not the full 1225.
    let bridge_count = encoder.encoding_cache.ext_eq_bridge_count();
    assert_eq!(
        bridge_count, 100,
        "congruence bridge count should be capped at TRUST_WP_MAX_CONGRUENCE_BRIDGES=100, got {bridge_count}"
    );
}

/// Verify that small numbers of ext_eq calls (below the cap) still
/// produce the expected number of bridges. With 5 calls sharing a
/// receiver, we expect 0+1+2+3+4 = 10 bridges (all below cap=100).
#[test]
#[timeout(30000)]
fn ext_eq_congruence_bridge_fires_fully_below_cap() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let receiver = seq_var("small_bridge_recv");
    let first_other = seq_var("small_bridge_other_0");
    let first_expr = ext_eq_call(receiver.clone(), first_other);
    encoder.register_sort_hints(&[first_expr.clone()]);

    // 5 calls: 0+1+2+3+4 = 10 bridges expected
    for i in 0..5 {
        let other = seq_var(&format!("small_bridge_other_{i}"));
        let expr = ext_eq_call(receiver.clone(), other);
        encoder
            .encode_pure(&expr)
            .expect("encode ext_eq for small bridge test");
    }

    let bridge_count = encoder.encoding_cache.ext_eq_bridge_count();
    assert_eq!(
        bridge_count, 10,
        "5 ext_eq calls should produce 0+1+2+3+4=10 bridges, got {bridge_count}"
    );
}

// ── FMap ext_eq: falls back to Bool UF (not Seq path) ────────────────

/// FMap-annotated receivers should NOT trigger the Seq Tseitin path.
/// ext_eq on FMaps falls through to the Bool UF fallback because only
/// Seq defines the pointwise equality encoding. (#2662)
#[test]
#[timeout(30000)]
fn ext_eq_fmap_receivers_use_bool_uf_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let m1 = var_with_sort("m1", ExprSort::FMap);
    let m2 = var_with_sort("m2", ExprSort::FMap);
    let expr = ext_eq_call(m1, m2);
    encoder.register_sort_hints(&[expr.clone()]);

    let term = encoder.encode_pure(&expr).expect("encode FMap ext_eq");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "FMap ext_eq should return Bool via UF fallback"
    );
    // FMap ext_eq should NOT populate the Seq ext_eq registry
    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        0,
        "FMap ext_eq should not populate Seq ext_eq registry"
    );
}

// ── Nested View: ext_eq on View(View(Seq)) ──────────────────────────

/// Nested View wrappers around Seq receivers should still route to the
/// Seq Tseitin path. The sort hint resolution peels through View layers.
#[test]
#[timeout(30000)]
fn ext_eq_nested_view_seq_receivers_route_to_seq_path() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // View(View(Seq-annotated var))
    let a = view(view(seq_var("nv_a")));
    let b = view(view(seq_var("nv_b")));
    let expr = ext_eq_call(a, b);
    encoder.register_sort_hints(&[expr.clone()]);

    let term = encoder
        .encode_pure(&expr)
        .expect("encode nested-view ext_eq");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "nested-view Seq ext_eq should return Bool"
    );
    assert!(
        encoder.seq_state.funcs_clone().is_some(),
        "nested-view Seq ext_eq should initialize Seq theory"
    );
    assert!(
        !encoder.encoding_cache.ext_eq_registry().is_empty(),
        "nested-view Seq ext_eq should populate registry"
    );
}

// ── Fallback for unknown/untyped receivers ──────────────────────────

/// ext_eq on receivers with no sort annotation and no Seq hints should
/// use the Bool UF fallback, not crash. This matches the non-Seq fallback
/// path at ext_eq.rs:291-298.
#[test]
#[timeout(30000)]
fn ext_eq_unknown_type_receivers_use_bool_uf_fallback() {
    let mut encoder = AYEncoder::new();
    let expr = ext_eq_call(var("unknown_a"), var("unknown_b"));
    let term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq on unknown-type vars");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "unknown-type ext_eq should return Bool via UF fallback"
    );
    // No Seq theory should be initialized
    assert!(
        encoder.seq_state.funcs_clone().is_none(),
        "unknown-type ext_eq should NOT initialize Seq theory"
    );
    // No registry entries
    assert_eq!(
        encoder.encoding_cache.ext_eq_registry_len(),
        0,
        "unknown-type ext_eq should NOT populate Seq registry"
    );
}

/// ext_eq Bool UF fallback should be satisfiable in both directions:
/// the UF is uninterpreted, so both true and false are possible.
#[test]
#[timeout(30000)]
fn ext_eq_bool_uf_fallback_is_not_trivially_constrained() {
    let mut encoder = AYEncoder::new();
    let expr = ext_eq_call(var("p"), var("q"));
    let term = encoder
        .encode_pure(&expr)
        .expect("encode ext_eq UF fallback");

    // ext_eq(p, q) = true should be SAT
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat | SolveResult::Unknown),
        "ext_eq UF(p, q) should be SAT, got {result:?}"
    );
}
