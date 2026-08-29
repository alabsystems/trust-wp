// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_subsequence_on_seq() {
    // v@.subsequence(from, to) should encode via Seq encoding path,
    // NOT through the generic UF fallback. Verified by absence of
    // method_subsequence_* in logic_funcs.
    let mut encoder = AYEncoder::new();

    let expr = method_call(view(var("v")), "subsequence", vec![int(1), int(3)]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("subsequence should encode via Seq path");
    let has_uf_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_subsequence_"));
    assert!(
        !has_uf_fallback,
        "subsequence should use Seq built-in, not UF fallback; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_ext_eq_on_seq_receiver() {
    // ext_eq(v@, w@) should infer Seq from view-shaped operands and route
    // to the Seq encoding path (no UF fallback). (#962)
    let mut encoder = AYEncoder::new();

    let ext_eq = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let ext_eq_term = encoder.encode_pure(&ext_eq).expect("ext_eq should encode");

    let ext_eq_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_ext_eq_"));
    let len_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_len_"));
    assert!(
        !ext_eq_fallback,
        "ext_eq(v@, w@) should use Seq encoding path, not method_ext_eq_* fallback"
    );
    assert!(
        !len_fallback,
        "len should use Seq encoding path, not method_len_* fallback"
    );

    // Semantic check (#955): ext_eq implies len(v@) == len(w@).
    // Assert ext_eq_term AND len(v@) != len(w@) — should be UNSAT.
    encoder.assert_term(ext_eq_term);

    let len_v = encoder
        .encode_pure(&method_call(view(var("v")), "len", vec![]))
        .expect("len(v@) should encode");
    let len_w = encoder
        .encode_pure(&method_call(view(var("w")), "len", vec![]))
        .expect("len(w@) should encode");
    let len_eq = encoder.solver.eq(len_v, len_w);
    let len_neq = encoder.solver.not(len_eq);
    encoder.assert_term(len_neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ext_eq(v@, w@) AND len(v@) != len(w@) should be UNSAT — \
             ext_eq must imply length equality"
    );
}

/// Negative semantic check (#955): ext_eq on view-shaped variables with
/// different lengths is UNSAT.
#[test]
#[timeout(30000)]
fn test_ext_eq_view_vars_different_lengths_unsat() {
    let mut encoder = AYEncoder::new();

    // Assert ext_eq(v@, w@).
    let ext_eq = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq(v@, w@) should encode");
    encoder.assert_term(ext_eq_term);

    // Force len(v@) == 1 and len(w@) == 2 — contradicts ext_eq.
    let len_v = encoder
        .encode_pure(&method_call(view(var("v")), "len", vec![]))
        .expect("len(v@) should encode");
    let len_w = encoder
        .encode_pure(&method_call(view(var("w")), "len", vec![]))
        .expect("len(w@) should encode");
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let v_is_1 = encoder.solver.eq(len_v, one);
    let w_is_2 = encoder.solver.eq(len_w, two);
    encoder.assert_term(v_is_1);
    encoder.assert_term(w_is_2);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ext_eq(v@, w@) with len(v@)=1 and len(w@)=2 should be UNSAT"
    );
}

/// Regression coverage for the symbolic ext_eq path (#2404, #2172).
///
/// `ext_eq(v@, w@)` on two free views does not use Array-backed SeqValues;
/// it relies on the seq_index_logic triggers plus the index-0 ground seeding
/// in `encode_ext_eq`. Constraining `v@.index_logic(0)` while forcing
/// `w@.index_logic(0)` to differ should therefore be UNSAT once `len(v@) > 0`.
///
/// Without the symbolic-path seed terms, this regression can silently weaken
/// to SAT even though the Array-backed iterator tests still pass.
#[test]
#[timeout(30000)]
fn test_ext_eq_view_vars_propagate_index_zero_equality() {
    let mut encoder = AYEncoder::new();

    let ext_eq = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq(v@, w@) should encode");
    encoder.assert_term(ext_eq_term);

    let len_v = encoder
        .encode_pure(&method_call(view(var("v")), "len", vec![]))
        .expect("len(v@) should encode");
    let one = encoder.solver.int_const(1);
    let len_v_is_one = encoder.solver.eq(len_v, one);
    encoder.assert_term(len_v_is_one);

    let idx_v = encoder
        .encode_pure(&method_call(view(var("v")), "index_logic", vec![int(0)]))
        .expect("v@.index_logic(0) should encode");
    let idx_w = encoder
        .encode_pure(&method_call(view(var("w")), "index_logic", vec![int(0)]))
        .expect("w@.index_logic(0) should encode");
    let forty_two = encoder.solver.int_const(42);
    let idx_v_is_42 = encoder.solver.eq(idx_v, forty_two);
    let idx_w_is_not_42 = encoder.solver.neq(idx_w, forty_two);
    encoder.assert_term(idx_v_is_42);
    encoder.assert_term(idx_w_is_not_42);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ext_eq(v@, w@) with len(v@)=1, v@.index_logic(0)=42, and \
             w@.index_logic(0)!=42 should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_ext_eq_with_nested_view_arg_uses_seq_path() {
    // ext_eq(v@, if c then w@ else z@) should infer Seq for nested views
    // in the argument and encode without UF fallback.
    let mut encoder = AYEncoder::new();

    let nested = ite(bool_expr(true), view(var("w")), view(var("z")));
    let ext_eq = method_call(view(var("v")), "ext_eq", vec![nested]);
    let _ext_eq_term = encoder.encode_pure(&ext_eq).expect("ext_eq should encode");

    let ext_eq_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_ext_eq_"));
    assert!(
        !ext_eq_fallback,
        "ext_eq with nested view arg should use Seq encoding path, not UF fallback"
    );
}

#[test]
#[timeout(30000)]
fn test_ext_eq_on_seq_receiver_rejects_different_lengths() {
    // Unambiguously Seq-producing receivers should use the Seq ext_eq path
    // (no method_ext_eq UF fallback).
    let mut encoder = AYEncoder::new();

    // singleton(len=1) vs push_back(singleton, _)(len=2)
    let singleton = logic_fn_call("seq", vec![var("a")]);
    let two_elems = method_call(
        logic_fn_call("seq", vec![var("b")]),
        "push_back",
        vec![var("c")],
    );
    let ext_eq = method_call(singleton, "ext_eq", vec![two_elems]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq on Seq receivers should encode");
    encoder.assert_term(ext_eq_term);

    let ext_eq_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_ext_eq_"));
    assert!(
        !ext_eq_fallback,
        "ext_eq should use Seq encoding path, not method_ext_eq_* fallback"
    );
}

/// Semantic SAT test: ext_eq(seq(a), seq(b).push_back(c)) asserts that a
/// length-1 sequence equals a length-2 sequence. The ext_eq Seq encoding
/// includes len(lhs) == len(rhs), which contradicts axioms 1 and 13.
/// This MUST be UNSAT. (#962)
#[test]
#[timeout(30000)]
fn test_ext_eq_different_lengths_is_unsat() {
    let mut encoder = AYEncoder::new();

    // singleton(a) has len=1 (axiom 13)
    let singleton = logic_fn_call("seq", vec![var("a")]);
    // seq(b).push_back(c) has len=2 (axiom 1 + axiom 13)
    let two_elems = method_call(
        logic_fn_call("seq", vec![var("b")]),
        "push_back",
        vec![var("c")],
    );
    let ext_eq = method_call(singleton, "ext_eq", vec![two_elems]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq on Seq receivers should encode");
    encoder.assert_term(ext_eq_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq(seq(a), seq(b).push_back(c)) should be UNSAT due to \
             length contradiction (1 != 2); got {result:?}"
    );
}

/// Regression for #2246 / #2172: ext_eq on identical sequences.
///
/// After the `seq_index_logic` switch plus index-0 ground seeding,
/// asserting `ext_eq(seq(a), seq(a))` is satisfiable again. This guards
/// against reintroducing the false-UNSAT behavior fixed by the
/// ext_eq representation bridge.
#[test]
#[timeout(30000)]
fn test_ext_eq_identical_seqs_positive_is_sat_with_ground_seeding() {
    let mut encoder = AYEncoder::new();

    // seq(a).ext_eq(seq(a)) — same singleton, same element
    let singleton1 = logic_fn_call("seq", vec![var("a")]);
    let singleton2 = logic_fn_call("seq", vec![var("a")]);
    let ext_eq = method_call(singleton1, "ext_eq", vec![singleton2]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq on same Seq should encode");
    encoder.assert_term(ext_eq_term);

    let result = encoder.check_sat();
    // The ext_eq encoding now uses seq_index_logic UF (not raw
    // select) in the pointwise axiom (#2246), which resolves the
    // previous ay model-construction deficiency. The formula is
    // satisfiable (seq(a).ext_eq(seq(a)) is true by identity).
    assert!(
        matches!(result, SolveResult::Sat),
        "seq(a).ext_eq(seq(a)) should be satisfiable: got {result:?}"
    );
}

/// Semantic test for Tseitin Axiom 2 (pointwise element equality). (#955)
///
/// ext_eq(seq(a), seq(b)) with a != b should ideally be UNSAT:
/// - Both singletons have len=1 (old axiom 13).
/// - ext_eq => forall i. 0<=i<len => index(lhs,i)==index(rhs,i).
/// - At i=0: old axiom 14 gives index(seq(a),0)=a and index(seq(b),0)=b, so a==b.
/// - a != b contradicts a == b. UNSAT.
///
/// With the 21 quantified axioms removed (#1317), `seq(a)` is an uninterpreted
/// function call without singleton axioms 13-14. ay now derives the
/// contradiction from the pointwise encoding alone (previously returned Sat).
/// Fixed in ay pin bump. See #1725.
#[test]
#[timeout(30000)]
fn test_ext_eq_same_length_different_elements_incomplete_without_singleton_axioms() {
    let mut encoder = AYEncoder::new();

    let seq_a = logic_fn_call("seq", vec![var("a")]);
    let seq_b = logic_fn_call("seq", vec![var("b")]);
    let ext_eq = method_call(seq_a, "ext_eq", vec![seq_b]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq(seq(a), seq(b)) should encode");
    encoder.assert_term(ext_eq_term);

    // Assert a != b — contradicts pointwise equality at index 0.
    let a = *encoder.vars_for_test().get("a").unwrap();
    let b = *encoder.vars_for_test().get("b").unwrap();
    let a_neq_b = encoder.solver.neq(a, b);
    encoder.assert_term(a_neq_b);

    let result = encoder.check_sat();
    // ay now derives the contradiction from pointwise ext_eq encoding
    // without singleton axioms 13-14 (removed in #1317). Previously returned
    // Sat; fixed in ay pin bump. See #1725.
    assert_eq!(
        result,
        SolveResult::unsat(),
        "ext_eq(seq(a), seq(b)) with a != b should be Unsat. Got: {result:?}"
    );
}

/// Reverse Tseitin forces ext_eq true for identical seq terms. (#2116)
///
/// Previously (#2246), the one-directional Tseitin made `!ext_eq(seq(a), seq(a))`
/// satisfiable because `ext_eq_var=false` vacuously satisfied forward axioms.
/// The ground reverse Tseitin `(r_term = o_term) => ext_eq_var` (#2116) fixes
/// this: identical operands produce the same SMT term, so `r_term = o_term`
/// is trivially true, forcing `ext_eq_var = true` and making `NOT ext_eq_var`
/// UNSAT. The full quantified reverse direction remains suppressed (ay#6481).
#[test]
#[timeout(30000)]
fn test_ext_eq_negated_on_identical_seqs_is_unsat_with_reverse_tseitin() {
    let mut encoder = AYEncoder::new();

    let seq1 = logic_fn_call("seq", vec![var("a")]);
    let seq2 = logic_fn_call("seq", vec![var("a")]);
    let ext_eq = method_call(seq1, "ext_eq", vec![seq2]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq(seq(a), seq(a)) should encode");

    // Assert NOT ext_eq — with the ground reverse Tseitin (#2116),
    // identical operands force ext_eq_var = true, making NOT ext_eq UNSAT.
    let not_ext_eq = encoder.solver.not(ext_eq_term);
    encoder.assert_term(not_ext_eq);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "NOT ext_eq(seq(a), seq(a)) should be Unsat with reverse Tseitin: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_ext_eq_non_seq_fallback() {
    // x.ext_eq(y) on non-Seq receivers falls back to Bool UF.
    // UF name: method_ext_eq_2_i_i (2 params: receiver=Int, other=Int; returns Bool).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "ext_eq", vec![var("y")]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("ext_eq on non-Seq should encode as Bool UF");
    assert!(
        encoder.decls().has_logic_func("method_ext_eq_2_i_i"),
        "ext_eq non-Seq should declare method_ext_eq_2_i_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}
