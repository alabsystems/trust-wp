// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

/// ay-dpll Array extensionality: asserting two stores with different values
/// at the same index are equal should return Unsat. Fixed in ay rev 40ed0b
/// (was returning Sat in 702bf7, which was UNSOUND).
#[test]
#[timeout(30000)]
fn test_store_store_equality_lacks_extensionality() {
    let mut encoder = AYEncoder::new();
    let zero = encoder.solver.int_const(0);
    let one = encoder.solver.int_const(1);
    let base_arr = encoder.solver.const_array(Sort::Int, zero);

    // store(base, 0, 0)
    let arr0 = encoder.solver.store(base_arr, zero, zero);
    // store(base, 0, 1)
    let arr1 = encoder.solver.store(base_arr, zero, one);

    // Assert arr0 == arr1. These arrays provably differ at index 0
    // (select(arr0,0)==0, select(arr1,0)==1), so the correct answer is Unsat.
    // ay rev 702bf7 regression was returning Sat (spurious model).
    // ay rev 40ed0b fixed the Array extensionality soundness issue.
    let eq_term = encoder.solver.eq(arr0, arr1);
    encoder.assert_term(eq_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "store(base,0,0)==store(base,0,1) should be Unsat \
         (arrays differ at index 0). Got {result:?}"
    );
}

/// seq_contains with a Tuple2-sorted element should not crash (#994).
///
/// When `prod.contains(__trust_wp_tuple2(k1, v))` is encoded, the tuple
/// constructor produces a Tuple2-sorted term. The `coerce_seq_element_to_int`
/// bridge injects an `__seq_elem_Tuple2: Tuple2 -> Int` UF so that
/// `seq_contains` receives Int-sorted arguments.
#[test]
#[timeout(30000)]
fn test_seq_contains_with_tuple2_element_does_not_crash() {
    let mut encoder = AYEncoder::new();

    let v_view = view(var("v"));

    // Pre-scan with v@.len() to hint v_view as Seq
    let len_hint = method_call(v_view.clone(), "len", vec![]);

    // Build __trust_wp_tuple2(k, val)
    let tuple_fn_name = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);
    let tuple_elem = PureExpr::LogicFnCall {
        name: tuple_fn_name,
        args: vec![PureExpr::Var("k".into(), None), PureExpr::Int(42)],
    };

    // v@.contains(__trust_wp_tuple2(k, 42))
    let contains_tuple = method_call(v_view, "contains", vec![tuple_elem]);

    encoder.register_sort_hints(&[len_hint, contains_tuple.clone()]);

    let result = encoder.encode_pure(&contains_tuple);
    assert!(
        result.is_ok(),
        "v@.contains(tuple2(k, 42)) should succeed via element coercion: {result:?}"
    );
}

/// Seq element bridges must preserve non-Int element identity through
/// `index_logic` equality checks. (#2316)
///
/// `Seq<Mapping>` literals are stored via the existing element-to-Int bridge.
/// When the indexed element is later compared against a Mapping-sorted term,
/// the equality layer must recover the original Mapping term instead of
/// replacing the Int token with a fresh unconstrained Mapping constant.
#[test]
#[timeout(30000)]
fn test_seq_index_mapping_element_roundtrips_through_eq_bridge_2316() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let mapping_sort = ExprSort::Datatype(intern_sort_name("Mapping"));
    let mapping_var = var_with_sort("pred0", mapping_sort);
    let seq_expr = method_call(
        logic_fn_call("Seq::empty", vec![]),
        "push_back",
        vec![mapping_var.clone()],
    );
    let eq_expr = eq(
        method_call(seq_expr, "index_logic", vec![int(0)]),
        mapping_var,
    );

    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("Seq<Mapping> index equality should encode");

    encoder.solver.push();
    let neg = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neg);
    let result = encoder.check_sat();
    encoder.solver.pop();

    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "negated Seq<Mapping> index equality should be UNSAT, got {result:?}"
    );
}

// =============================================================================
// AC2: encode_seq_empty produces valid empty Seq with len == 0 (#1380)
// =============================================================================

/// Verify that encoding `Seq::empty()` via the public API produces a term
/// whose length is provably 0 under the axiom set.
#[test]
#[timeout(30000)]
fn test_encode_seq_empty_has_zero_length() {
    let mut encoder = AYEncoder::new();

    // Encode Seq::empty() through the public encode_pure API.
    let empty_expr = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let empty = encoder
        .encode_pure(&empty_expr)
        .expect("seq_empty should encode");

    // The term should be Seq-sorted.
    let sort = encoder.solver.get_sort(empty);
    assert_eq!(
        sort,
        ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int),
        "seq_empty should be Seq-sorted"
    );

    // Encode len(empty) via a method call and prove it equals 0.
    let len_expr = method_call(empty_expr.clone(), "len", vec![]);
    let len = encoder
        .encode_pure(&len_expr)
        .expect("len(seq_empty) should encode");
    let zero = encoder.solver.int_const(0);
    let len_ne_zero = encoder.solver.distinct(&[len, zero]);
    encoder.solver.push();
    encoder.solver.assert_term(len_ne_zero);
    let result = encoder.check_sat();
    encoder.solver.pop();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "len(seq_empty) != 0 should be UNSAT (proving len == 0), got {result:?}"
    );
}

/// Verify that encoding `Seq::empty()` twice yields the same SMT term
/// (the underlying constant is declared once and reused).
#[test]
#[timeout(30000)]
fn test_encode_seq_empty_is_idempotent() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let empty1 = encoder.encode_pure(&expr).expect("first encode");
    let empty2 = encoder.encode_pure(&expr).expect("second encode");
    assert_eq!(
        empty1, empty2,
        "encode_seq_empty should return the same constant on repeated calls"
    );
}
