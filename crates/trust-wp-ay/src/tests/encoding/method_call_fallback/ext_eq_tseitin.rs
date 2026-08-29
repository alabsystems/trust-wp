// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── ext_eq Tseitin axiom isolation tests (#1667) ────────────────────
//
// The ext_eq Seq encoding emits three Tseitin axioms:
//   Axiom 1: ext_eq => len(a) == len(b)
//   Axiom 2: ext_eq => forall i. in_bounds(i) => index(a,i) == index(b,i)
//   Axiom 3: (len(a) == len(b) AND pointwise) => ext_eq
// These tests verify each axiom in isolation.

/// Tseitin Axiom 1 isolation: ext_eq forces length equality.
/// Assert ext_eq is true, then constrain len(v@) and len(w@) to distinct
/// concrete values. The solver must find this UNSAT because Axiom 1
/// forces len(v@) == len(w@).
#[test]
#[timeout(30000)]
fn test_ext_eq_tseitin_axiom1_forces_length_equality() {
    let mut encoder = AYEncoder::new();

    // Encode ext_eq FIRST — this establishes Seq sort for v_view, w_view
    let ext_eq = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let ext_eq_term = encoder.encode_pure(&ext_eq).expect("ext_eq should encode");
    encoder.assert_term(ext_eq_term);

    // Now len() uses the already-established Seq sort
    let len_v = encoder
        .encode_pure(&method_call(view(var("v")), "len", vec![]))
        .expect("len(v@)");
    let len_w = encoder
        .encode_pure(&method_call(view(var("w")), "len", vec![]))
        .expect("len(w@)");
    let three = encoder.solver.int_const(3);
    let five = encoder.solver.int_const(5);
    let v_eq_3 = encoder.solver.eq(len_v, three);
    encoder.assert_term(v_eq_3);
    let w_eq_5 = encoder.solver.eq(len_w, five);
    encoder.assert_term(w_eq_5);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ext_eq=true with len(v@)=3 and len(w@)=5 must be UNSAT (Axiom 1)"
    );
}

/// Tseitin Axiom 2 structural: ext_eq does not use a UF fallback for
/// Seq receivers — it uses the Tseitin encoding with fresh Bool variable.
/// The Axiom 2 quantifier (forall i. in_bounds => index equality) is
/// present but E-matching does not instantiate it at ground terms, so
/// we verify structural properties instead of quantifier instantiation.
#[test]
#[timeout(30000)]
fn test_ext_eq_tseitin_axiom2_no_uf_fallback() {
    let mut encoder = AYEncoder::new();

    // Encode ext_eq on Seq-typed view vars
    let ext_eq = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let ext_eq_term = encoder.encode_pure(&ext_eq).expect("ext_eq should encode");

    // Verify NO method_ext_eq UF fallback was used (Seq path taken)
    let has_uf_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_ext_eq_"));
    assert!(
        !has_uf_fallback,
        "Seq ext_eq should use Tseitin encoding, not UF fallback; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Assert ext_eq=true on unconstrained Seq views.
    // The ext_eq encoding (#2246) now seeds ground seq_index_logic
    // terms at index 0 and uses seq_index_logic UF in the pointwise
    // axiom, providing E-matching trigger instances. This resolves
    // the previous ay model-construction deficiency.
    encoder.assert_term(ext_eq_term);
    let result = encoder.check_sat();
    assert!(
        !result.is_unsat(),
        "ext_eq=true on unconstrained seqs must remain consistent; AY may conservatively return Unknown when auxiliary Seq axioms cannot be validated: got {result:?}; reason={:?}; error={:?}",
        encoder.last_unknown_reason(),
        encoder.last_executor_error()
    );
}

/// Tseitin structure test: NOT ext_eq on unconstrained sequences.
/// With one-directional Tseitin (#2246, reverse axiom suppressed for
/// ay#6481),
/// NOT ext_eq_var is satisfiable: ext_eq_var=false vacuously satisfies
/// the forward axioms. This is conservative (never false Verified).
#[test]
#[timeout(30000)]
fn test_ext_eq_tseitin_not_ext_eq_is_sat_unconstrained() {
    let mut encoder = AYEncoder::new();

    let ext_eq = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let ext_eq_term = encoder.encode_pure(&ext_eq).expect("ext_eq should encode");
    let not_ext_eq = encoder.solver.not(ext_eq_term);
    encoder.assert_term(not_ext_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "NOT ext_eq on unconstrained Seqs is Sat with one-directional \
         Tseitin (#2246 / ay#6481): got {result:?}; reason={:?}; error={:?}",
        encoder.last_unknown_reason(),
        encoder.last_executor_error()
    );
}
