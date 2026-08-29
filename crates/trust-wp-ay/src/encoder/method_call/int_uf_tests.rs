// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for Int-returning method UF sort-drift recovery.

use ay_dpll::api::{Sort, TermKind};
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use super::super::AYEncoder;
use crate::tests::helpers::{final_expr, var};

#[test]
#[timeout(30000)]
fn pow2_ground_only_mode_omits_recursive_quantifiers() {
    let expr = PureExpr::MethodCall {
        receiver: std::sync::Arc::new(var("i")),
        method: "pow2".to_string(),
        args: vec![],
    };

    let mut quantified = AYEncoder::new_with_quantifiers();
    quantified
        .encode_pure(&expr)
        .expect("symbolic pow2 should encode in quantified mode");
    assert_eq!(
        quantified
            .solver
            .assertions()
            .into_iter()
            .filter(|term| matches!(quantified.solver.term_kind(*term), TermKind::Forall))
            .count(),
        3,
        "the ordinary lane should retain lower-bound, doubling, and nonnegative foralls"
    );

    let mut ground_only = AYEncoder::new_with_quantifiers();
    ground_only.set_logic_fn_defining_axioms_ground_only(true);
    ground_only
        .encode_pure(&expr)
        .expect("symbolic pow2 should encode in finite ground-only mode");
    assert_eq!(
        ground_only
            .solver
            .assertions()
            .into_iter()
            .filter(|term| matches!(ground_only.solver.term_kind(*term), TermKind::Forall))
            .count(),
        0,
        "ground-only proof lanes must not inherit recursive pow2 foralls"
    );
    assert!(
        ground_only.solver.assertions().len() >= 7,
        "base facts plus exact per-receiver ground instances must remain available"
    );
}

#[test]
#[timeout(30000)]
fn deep_model_retries_with_actual_int_sort_for_generic_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("k", Sort::Int)
        .expect("declare generic receiver carrier as Int");

    let receiver = PureExpr::Var(
        "k".to_string(),
        Some(ExprSort::TypeParam(intern_sort_name("K"))),
    );
    let expr = PureExpr::MethodCall {
        receiver: std::sync::Arc::new(receiver),
        method: "deep_model".to_string(),
        args: vec![],
    };

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "deep_model should retry with the actual encoded Int carrier sort: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn encode_int_method_uf_bridges_ground_calls_inside_quantifiers() {
    let mut encoder = AYEncoder::new();
    encoder.quantifier_state.inc_quantifier_depth();

    let receiver = final_expr(var("v"));
    let receiver_term = encoder
        .encode_pure(&receiver)
        .expect("receiver should encode");
    let param_sort = encoder.method_param_sort(&receiver, receiver_term, None);
    let smt_name = format!(
        "method_capacity_1_{}",
        AYEncoder::method_sort_tag(&param_sort)
    );
    let func_decl = encoder.get_or_declare_method_func(&smt_name, &[param_sort], Sort::Int);
    let raw_app = encoder.solver.apply(&func_decl, &[receiver_term]);

    let encoded = encoder
        .encode_int_method_uf(&receiver, "capacity", &[], None)
        .expect("ground capacity call should encode inside quantifier scope");

    assert_eq!(
        encoder.seq_state_for_test().get_uf_int_aux(&raw_app),
        Some(encoded),
        "ground capacity calls inside quantifier scopes should cache the aux carrier"
    );
    assert_ne!(
        encoded, raw_app,
        "capacity should remain opaque instead of returning the raw UF"
    );
}

#[test]
#[timeout(30000)]
fn encode_int_method_uf_keeps_bound_capacity_opaque_inside_quantifiers() {
    let mut encoder = AYEncoder::new();
    encoder.quantifier_state.inc_quantifier_depth();
    encoder.bind_quantifier_var("i".to_string());

    let receiver = var("i");
    let receiver_term = encoder
        .encode_pure(&receiver)
        .expect("receiver should encode");
    let param_sort = encoder.method_param_sort(&receiver, receiver_term, None);
    let smt_name = format!(
        "method_capacity_1_{}",
        AYEncoder::method_sort_tag(&param_sort)
    );
    let func_decl = encoder.get_or_declare_method_func(&smt_name, &[param_sort], Sort::Int);
    let raw_app = encoder.solver.apply(&func_decl, &[receiver_term]);

    let encoded = encoder
        .encode_int_method_uf(&receiver, "capacity", &[], None)
        .expect("bound capacity call should still encode");

    assert_ne!(
        encoded, raw_app,
        "capacity inside a quantifier should use the opaque aux carrier instead of the raw UF"
    );
    assert!(
        encoder
            .seq_state_for_test()
            .get_uf_int_aux(&raw_app)
            .is_some(),
        "capacity inside a quantifier should still cache the aux carrier"
    );

    let five = encoder.solver.int_const(5);
    let eq_five = encoder.solver.eq(encoded, five);
    encoder.solver.assert_term(eq_five);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Sat),
        "opaque bound capacity carrier should stay satisfiable"
    );
}

// ── CE-census 2026-08-20 pin: std iterator-carrier len non-negativity ──

/// `len` on an FMapIter-sorted receiver falls back to the composite Int
/// method UF; the result still denotes an FMap cardinality, so the LEN
/// law's `result >= 0` clause (trust-wp-std/src/logic/fmap.rs `FMap::LEN`)
/// must attach. Unfixed: `len(iter) < 0` is satisfiable and
/// loop_variant_nonneg gets a fabricated counterexample
/// (ghost/fmap_iter merge_fmaps).
#[test]
#[timeout(30000)]
fn std_iterator_len_uf_carries_cardinality_nonnegativity() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("iter", Sort::Uninterpreted("FMapIter".to_string()))
        .expect("declare FMapIter carrier");
    let encoded = encoder
        .encode_int_method_uf(&var("iter"), "len", &[], None)
        .expect("len UF should encode");
    let zero = encoder.solver.int_const(0);
    let negative = encoder.solver.lt(encoded, zero);
    encoder.solver.assert_term(negative);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_)),
        "FMapIter len must carry the FMap LEN law's non-negativity clause"
    );
}

/// CONTROL (cardinal rule): a user-named receiver sort must NOT receive a
/// fabricated non-negativity law — user `len` methods may mean anything.
#[test]
#[timeout(30000)]
fn user_receiver_len_uf_gets_no_fabricated_nonnegativity() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("thing", Sort::Uninterpreted("MyCollection".to_string()))
        .expect("declare user carrier");
    let encoded = encoder
        .encode_int_method_uf(&var("thing"), "len", &[], None)
        .expect("len UF should encode");
    let zero = encoder.solver.int_const(0);
    let negative = encoder.solver.lt(encoded, zero);
    encoder.solver.assert_term(negative);
    assert!(
        !matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_)),
        "no non-negativity law may be fabricated for user-defined len methods"
    );
}
