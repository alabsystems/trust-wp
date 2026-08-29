// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Seq operations argument-count error path coverage
// =============================================================================

/// Test that Seq index/index_logic rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 62: "index expects 1 argument"
/// Zero test coverage before this.
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_index_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();

    // Register v@ as Seq-sorted
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    // v@.index(a, b) — 2 args instead of 1
    let expr = method_call(view(var("v")), "index", vec![int(0), int(1)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "index with 2 args should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("index") && err_msg.contains("1 argument"),
        "error should mention 'index' and '1 argument', got: {err_msg}"
    );
}

/// Test that Seq push_back rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 72: "push_back expects 1 argument"
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_push_back_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "push_back", vec![int(0), int(1)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "push_back with 2 args should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("push_back") && err_msg.contains("1 argument"),
        "error should mention 'push_back' and '1 argument', got: {err_msg}"
    );
}

/// Test that Seq get rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 120: "get expects 1 argument"
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_get_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "get", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "get with 0 args should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("get") && err_msg.contains("1 argument"),
        "error should mention 'get' and '1 argument', got: {err_msg}"
    );
}

/// Test that Seq contains with wrong arg count is caught by method dispatch.
///
/// The `method_call/mod.rs` dispatcher only routes `contains` when args.len() == 1,
/// so a wrong arg count falls through to the "unknown method" handler before
/// reaching `seq/operations.rs`. This validates the dispatch-level guard.
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_contains_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "contains", vec![int(1), int(2)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "contains with 2 args should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("contains"),
        "error should mention 'contains', got: {err_msg}"
    );
}

/// Test that Seq subsequence with wrong arg count is caught by method dispatch.
///
/// The `method_call/mod.rs` dispatcher only routes `subsequence` when args.len() == 2,
/// so a wrong arg count falls through to the "unknown method" handler before
/// reaching `seq/operations.rs`. This validates the dispatch-level guard.
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_subsequence_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "subsequence", vec![int(0)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "subsequence with 1 arg should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("subsequence"),
        "error should mention 'subsequence', got: {err_msg}"
    );
}

/// Test that Seq tail rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 187: "tail expects 0 arguments"
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_tail_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "tail", vec![int(0)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "tail with 1 arg should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("tail") && err_msg.contains("0 arguments"),
        "error should mention 'tail' and '0 arguments', got: {err_msg}"
    );
}

/// Test that Seq concat rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 221: "concat expects 1 argument"
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_concat_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "concat", vec![int(0), int(1)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "concat with 2 args should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("concat") && err_msg.contains("1 argument"),
        "error should mention 'concat' and '1 argument', got: {err_msg}"
    );
}

/// Test that Seq set with wrong arg count is caught by method dispatch.
///
/// The `method_call/mod.rs` dispatcher only routes `set` to seq when args.len() == 2.
/// With 1 arg, it falls through to the int method UF handler at line 370.
/// This test validates the dispatch-level guard prevents reaching seq/operations.rs.
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_set_wrong_arg_count_dispatches_to_uf() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    // With 1 arg, `set` falls to the int method UF handler (line 370),
    // which creates an uninterpreted function `method_set_2_<sort_sig>`.
    let expr = method_call(view(var("v")), "set", vec![int(0)]);
    let result = encoder.encode_pure(&expr);

    // 1) Encoding succeeds via UF handler (seq path would error with "2 arguments")
    assert!(
        result.is_ok(),
        "set with 1 arg should be handled by int method UF, not seq: {:?}",
        result.err()
    );

    // 2) Verify a `method_set_*` UF was declared (distinguishes UF path from seq path).
    // The seq path does NOT declare method_set_* — it uses seq_store internally.
    // get_or_declare_method_func stores UF decls in decls.logic_funcs.
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("method_set_")),
        "UF fallback should declare method_set_* function, found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// Test that Seq pop_back rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 304: "pop_back expects 0 arguments"
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_pop_back_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "pop_back", vec![int(0)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "pop_back with 1 arg should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("pop_back") && err_msg.contains("0 arguments"),
        "error should mention 'pop_back' and '0 arguments', got: {err_msg}"
    );
}

/// Test that Seq push_front rejects wrong argument count.
///
/// Coverage target: `seq/operations.rs` line 342: "push_front expects 1 argument"
///
/// Part of #901.
#[test]
#[timeout(30000)]
fn test_seq_push_front_wrong_arg_count_returns_error() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let expr = method_call(view(var("v")), "push_front", vec![int(0), int(1)]);
    let result = encoder.encode_pure(&expr);
    assert!(result.is_err(), "push_front with 2 args should fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("push_front") && err_msg.contains("1 argument"),
        "error should mention 'push_front' and '1 argument', got: {err_msg}"
    );
}
