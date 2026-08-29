// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

// =============================================================================
// Seq Error Handling Tests
// =============================================================================

#[test]
#[timeout(30000)]
fn test_encode_seq_index_logic_wrong_args() {
    // Test that index_logic with wrong number of args fails
    let mut encoder = AYEncoder::new();

    // v@.index_logic() - missing argument
    let expr = method_call(view(var("v")), "index_logic", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "index_logic with no args should fail, got Ok({:?})",
        result.as_ref().ok()
    );
    match result.unwrap_err() {
        EncodingError::Unsupported { message: msg, .. } => {
            assert!(
                msg.contains("expects 1 argument"),
                "Error should mention argument count"
            );
        }
        err @ (EncodingError::SolverError { .. }
        | EncodingError::SortInference { .. }
        | EncodingError::SortConflict { .. }) => {
            panic!("Expected Unsupported error, got {err:?}")
        }
    }
}

#[test]
#[timeout(30000)]
fn test_encode_unknown_method_returns_error() {
    // Unknown methods now return EncodingError instead of silently
    // creating an Int-returning UF (#1820).
    let mut encoder = AYEncoder::new();

    // x.unknown_method()
    let expr = method_call(var("x"), "unknown_method", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "Unknown method should produce EncodingError: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_old_unknown_method_returns_error() {
    // Unknown methods via old() (prefixed path) now return EncodingError (#1820).
    let mut encoder = AYEncoder::new();

    // old(x).unknown_method() - unknown method through prefixed path
    let expr = method_call(old(var("x")), "unknown_method", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "Unknown method via old() should produce EncodingError: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_push_back_wrong_args() {
    // Test that push_back with wrong number of args fails
    let mut encoder = AYEncoder::new();

    // v@.push_back() - missing argument
    let expr = method_call(view(var("v")), "push_back", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "push_back with no args should fail, got Ok({:?})",
        result.as_ref().ok()
    );
    match result.unwrap_err() {
        EncodingError::Unsupported { message: msg, .. } => {
            assert!(
                msg.contains("expects 1 argument"),
                "Error should mention argument count"
            );
        }
        err @ (EncodingError::SolverError { .. }
        | EncodingError::SortInference { .. }
        | EncodingError::SortConflict { .. }) => {
            panic!("Expected Unsupported error, got {err:?}")
        }
    }
}

#[test]
#[timeout(30000)]
fn test_encode_old_seq_index_logic_wrong_args() {
    // Test that old(v@).index_logic() with wrong args fails
    let mut encoder = AYEncoder::new();

    // old(v@).index_logic() - missing argument (with prefix)
    let expr = method_call(old(view(var("v"))), "index_logic", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "old(v@).index_logic() with no args should fail: {result:?}"
    );
    match result.unwrap_err() {
        EncodingError::Unsupported { message: msg, .. } => {
            assert!(
                msg.contains("expects 1 argument"),
                "Error should mention argument count"
            );
        }
        err @ (EncodingError::SolverError { .. }
        | EncodingError::SortInference { .. }
        | EncodingError::SortConflict { .. }) => {
            panic!("Expected Unsupported error, got {err:?}")
        }
    }
}

#[test]
#[timeout(30000)]
fn test_encode_old_seq_push_back_wrong_args() {
    // Test that old(v@).push_back() with wrong args fails
    let mut encoder = AYEncoder::new();

    // old(v@).push_back() - missing argument (with prefix)
    let expr = method_call(old(view(var("v"))), "push_back", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "old(v@).push_back() with no args should fail: {result:?}"
    );
    match result.unwrap_err() {
        EncodingError::Unsupported { message: msg, .. } => {
            assert!(
                msg.contains("expects 1 argument"),
                "Error should mention argument count"
            );
        }
        err @ (EncodingError::SolverError { .. }
        | EncodingError::SortInference { .. }
        | EncodingError::SortConflict { .. }) => {
            panic!("Expected Unsupported error, got {err:?}")
        }
    }
}
