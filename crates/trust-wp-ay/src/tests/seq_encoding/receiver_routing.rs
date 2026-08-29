// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;
use crate::expr_seq::expr_has_seq_method_needing_quantifiers;

// Ambiguous Method Dispatch Tests (#756)
// =============================================================================
// `len`, `index`, `get` are shared by Seq, FSet, FMap, Mapping.
// The encoder uses is_seq_receiver() dispatch to route correctly.

/// Non-Seq receiver calling `.len()` should fall through to UF encoding,
/// not crash or misroute to Seq encoding. Regression test for #756.
#[test]
#[timeout(30000)]
fn test_non_seq_receiver_len_falls_through_to_uf() {
    let mut encoder = AYEncoder::new();
    let receiver = var("fmap_val");

    // Use a bare Var (not View) that has no Seq hint — simulates FMap/Mapping receiver
    let expr = method_call(receiver.clone(), "len", vec![]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "bare var receiver calling len should not be tagged Seq"
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "non-Seq receiver calling len should succeed via UF fallback: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "non-Seq len() fallback should not initialize Seq functions"
    );
}

/// Non-Seq receiver calling `.index(i)` should fall through to UF encoding.
/// Regression test for #756.
#[test]
#[timeout(30000)]
fn test_non_seq_receiver_index_falls_through_to_uf() {
    let mut encoder = AYEncoder::new();
    let receiver = var("fmap_val");

    let expr = method_call(receiver.clone(), "index", vec![int(0)]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "bare var receiver calling index should not be tagged Seq"
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "non-Seq receiver calling index should succeed via UF fallback: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "non-Seq index() fallback should not initialize Seq functions"
    );
}

/// Non-Seq receiver calling `.get(i)` should fall through to UF encoding.
/// Regression test for #756.
#[test]
#[timeout(30000)]
fn test_non_seq_receiver_get_falls_through_to_uf() {
    let mut encoder = AYEncoder::new();
    let receiver = var("fmap_val");

    let expr = method_call(receiver.clone(), "get", vec![int(0)]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "bare var receiver calling get should not be tagged Seq"
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "non-Seq receiver calling get should succeed via UF fallback: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "non-Seq get() fallback should not initialize Seq functions"
    );
}

/// Seq receiver calling `.len()` still routes to Seq encoding (not broken by #756 dispatch).
#[test]
#[timeout(30000)]
fn test_seq_receiver_len_still_routes_to_seq_encoding() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));
    let expr = method_call(v_view_expr, "len", vec![]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Seq receiver calling len should still work: {result:?}"
    );
}

/// Seq receiver calling `.get(i)` still routes to Seq encoding after #756 dispatch.
#[test]
#[timeout(30000)]
fn test_seq_receiver_get_still_routes_to_seq_encoding() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));
    let expr = method_call(v_view_expr, "get", vec![int(0)]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Seq receiver calling get should still work: {result:?}"
    );
}

/// Cross-expression: prescan detects Seq via `v@.len()` and propagates to `v`.
/// Bare Var `fmap_val.len()` without _view evidence stays non-Seq.
/// Regression test for #756. Updated for corroboration-based promotion (#994).
#[test]
#[timeout(30000)]
fn test_cross_expression_seq_and_non_seq_len_coexist() {
    let mut encoder = AYEncoder::new();

    // Seq receiver: v@.len() — tags v_view as Seq, propagates to v
    let seq_expr = method_call(view(var("v")), "len", vec![]);

    // Non-Seq receiver: fmap_val.len() — no _view evidence, stays non-Seq
    let non_seq_receiver = var("fmap_val");
    let non_seq_expr = method_call(non_seq_receiver.clone(), "len", vec![]);

    // Prescan both expressions
    encoder.register_sort_hints(&[seq_expr.clone(), non_seq_expr.clone()]);
    assert!(
        !encoder.is_seq_receiver(&non_seq_receiver, None),
        "bare var without _view evidence should not be tagged Seq"
    );

    // Both should encode successfully
    let r1 = encoder.encode_pure(&seq_expr);
    r1.unwrap_or_else(|err| panic!("Seq receiver len should succeed: {err:?}"));

    let r2 = encoder.encode_pure(&non_seq_expr);
    r2.unwrap_or_else(|err| panic!("non-Seq receiver len should succeed: {err:?}"));
}

/// FMap.len() receiver (bare var) should remain non-Seq even after prescan.
#[test]
#[timeout(30000)]
fn test_fmap_len_prescan_keeps_var_receiver_non_seq() {
    let mut encoder = AYEncoder::new();
    let receiver = var("fmap");
    let expr = method_call(receiver.clone(), "len", vec![]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "FMap-style var receiver must not be auto-tagged Seq by len() prescan"
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap.len() should encode via UF fallback after prescan: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "FMap.len() fallback should not initialize Seq functions"
    );
}

/// FMap.index(k) receiver (bare var) should remain non-Seq even after prescan.
#[test]
#[timeout(30000)]
fn test_fmap_index_prescan_keeps_var_receiver_non_seq() {
    let mut encoder = AYEncoder::new();
    let receiver = var("fmap");
    let expr = method_call(receiver.clone(), "index", vec![int(0)]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "FMap-style var receiver must not be auto-tagged Seq by index() prescan"
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap.index() should encode via UF fallback after prescan: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "FMap.index() fallback should not initialize Seq functions"
    );
}

/// Mapping.get(k) receiver (bare var) should remain non-Seq even after prescan.
#[test]
#[timeout(30000)]
fn test_mapping_get_prescan_keeps_var_receiver_non_seq() {
    let mut encoder = AYEncoder::new();
    let receiver = var("mapping");
    let expr = method_call(receiver.clone(), "get", vec![int(0)]);

    encoder.register_sort_hints(std::slice::from_ref(&expr));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "Mapping-style var receiver must not be auto-tagged Seq by get() prescan"
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Mapping.get() should encode via UF fallback after prescan: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "Mapping.get() fallback should not initialize Seq functions"
    );
}

/// Tail/pop operations use sequence semantics and must trigger the richer Seq
/// route instead of staying on the axiom-free integer path.
#[test]
#[timeout(30000)]
fn test_tail_and_pop_methods_trigger_richer_seq_route_detection() {
    for method in ["tail", "pop_front", "pop_back"] {
        let expr = method_call(view(var("s")), method, vec![]);
        assert!(
            expr_has_seq_method_needing_quantifiers(&expr),
            "{method} should trigger richer Seq route detection"
        );
    }
}
