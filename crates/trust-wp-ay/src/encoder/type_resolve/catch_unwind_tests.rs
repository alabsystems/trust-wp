// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for solver panic isolation (catch_unwind wrappers).

use ay_core::panic_payload_to_string;
use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::*;
use crate::AYEncoder;

#[test]
#[timeout(30000)]
fn check_sat_returns_result_through_catch_unwind() {
    let mut encoder = AYEncoder::new();
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "empty solver should be SAT"
    );
}

#[test]
#[timeout(30000)]
fn check_sat_unsat_through_catch_unwind() {
    let mut encoder = AYEncoder::new();
    let t = encoder.solver.bool_const(true);
    let f = encoder.solver.bool_const(false);
    encoder.solver.assert_term(t);
    encoder.solver.assert_term(f);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "contradictory assertions (true AND false) should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn panic_payload_str_literal() {
    let result = std::panic::catch_unwind(|| panic!("test message"));
    let msg = panic_payload_to_string(result.unwrap_err().as_ref());
    assert_eq!(
        msg, "test message",
        "str literal panic should be extracted verbatim"
    );
}

#[test]
#[timeout(30000)]
fn panic_payload_string_owned() {
    let result = std::panic::catch_unwind(|| panic!("{}", "formatted message"));
    let msg = panic_payload_to_string(result.unwrap_err().as_ref());
    assert_eq!(
        msg, "formatted message",
        "owned String panic should be extracted verbatim"
    );
}

#[test]
#[timeout(30000)]
fn panic_payload_non_string() {
    let result = std::panic::catch_unwind(|| {
        std::panic::resume_unwind(Box::new(42_i32));
    });
    let msg = panic_payload_to_string(result.unwrap_err().as_ref());
    assert_eq!(
        msg, "unknown panic",
        "non-string panic should produce fallback message"
    );
}

#[test]
#[timeout(30000)]
fn catch_solver_panic_with_reason_returns_err_on_ay_panic() {
    let result = catch_solver_panic_with_reason("unit_test", || -> u32 {
        panic!("sort mismatch: expected Bool, got Int")
    });
    assert!(result.is_err(), "should return Err on ay panic");
    let err = result.unwrap_err();
    assert_eq!(
        err.reason(),
        "sort mismatch: expected Bool, got Int",
        "Err should contain the panic reason string"
    );
}

#[test]
#[timeout(30000)]
fn catch_solver_panic_with_reason_captures_bug_panic() {
    let result = catch_solver_panic_with_reason("unit_test", || -> u32 {
        panic!("BUG: mk_eq called with mismatched sorts")
    });
    assert!(result.is_err(), "should return Err on ay BUG panic");
    let err = result.unwrap_err();
    assert_eq!(
        err.reason(),
        "BUG: mk_eq called with mismatched sorts",
        "should capture panic reason string"
    );
}

#[test]
#[timeout(30000)]
fn catch_solver_panic_with_reason_propagates_non_ay_panics() {
    let result = std::panic::catch_unwind(|| {
        let _ = catch_solver_panic_with_reason("unit_test", || -> u32 {
            panic!("debug: tracing something")
        });
    });
    let msg = panic_payload_to_string(result.unwrap_err().as_ref());
    assert_eq!(
        msg, "debug: tracing something",
        "non-ay panics should propagate unchanged through the encoder boundary"
    );
}

#[test]
#[timeout(30000)]
fn catch_solver_panic_with_reason_ok_on_success() {
    let result = catch_solver_panic_with_reason("unit_test", || 99_u32);
    assert_eq!(
        result.expect("should return Ok on success"),
        99,
        "should return Ok(result) on success"
    );
}

/// After an assertion panics, `solver_panic_reason()` must contain the
/// panic message and `check_sat()` must return `Unknown`.
/// End-to-end test for the #1009 panic-surfacing fix.
#[test]
#[timeout(30000)]
fn solver_panic_reason_surfaces_after_assertion_panic() {
    let mut encoder = AYEncoder::new();

    assert!(
        encoder.solver_panic_reason().is_none(),
        "fresh encoder should have no panic reason"
    );

    encoder
        .assertion_pipeline
        .record_solver_panic_with(|| "ay internal assertion failure".to_string());

    assert!(
        encoder.solver_panic_reason().is_some(),
        "panic reason should be set after storing failure"
    );
    assert_eq!(
        encoder.solver_panic_reason(),
        Some("ay internal assertion failure"),
        "panic reason should match the stored message"
    );

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "check_sat should return Unknown after recorded panic"
    );
}

/// Verify that the first panic reason is preserved (not overwritten).
#[test]
#[timeout(30000)]
fn solver_panic_reason_preserves_first_panic() {
    let mut encoder = AYEncoder::new();
    encoder
        .assertion_pipeline
        .record_solver_panic_with(|| "first panic".to_string());
    encoder
        .assertion_pipeline
        .record_solver_panic_with(|| "second panic".to_string());
    assert_eq!(
        encoder.solver_panic_reason(),
        Some("first panic"),
        "first panic reason should not be overwritten by subsequent panics"
    );
}

#[test]
#[timeout(30000)]
fn get_model_sat_through_catch_unwind() {
    let mut encoder = AYEncoder::new();
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "empty solver should be SAT before get_model"
    );
    let _model = encoder.get_model();
}

#[test]
#[timeout(30000)]
fn get_model_unsat_through_catch_unwind() {
    let mut encoder = AYEncoder::new();
    let f = encoder.solver.bool_const(false);
    encoder.solver.assert_term(f);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "solver with false assertion should be UNSAT"
    );
    assert!(
        encoder.get_model().is_none(),
        "get_model should return None for UNSAT result"
    );
}

/// Regression test for #1806: `assert_solver_term` must catch ay panics
/// (e.g., sort-mismatch when asserting an Int term as a constraint) and
/// surface them as `Unknown` via `solver_panic_reason`, instead of crashing.
#[test]
#[timeout(30000)]
fn assert_solver_term_catches_sort_mismatch_panic() {
    let mut encoder = AYEncoder::new();

    // Int term is not Bool — ay's assert_term will panic with SortMismatch.
    let int_term = encoder.solver.int_const(42);
    let ok = encoder.assert_solver_term("regression_test_sort_mismatch", int_term);

    assert!(!ok, "assert_solver_term should return false when ay panics");
    assert!(
        encoder.solver_panic_reason().is_some(),
        "solver_panic_reason should be set after sort-mismatch panic"
    );
    assert!(
        encoder
            .solver_panic_reason()
            .expect("panic reason should be Some after sort-mismatch")
            .contains("sort mismatch"),
        "panic reason should mention sort mismatch, got: {:?}",
        encoder.solver_panic_reason()
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "check_sat must return Unknown after assert_solver_term catches a panic (#1806)"
    );
}
