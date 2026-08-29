// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness tests for borrow finality (#2181) in the prophecy writeback pipeline.
//!
//! These tests verify the `BorrowFinality::Final` optimization:
//! `parent_final == child_final` is asserted when the parent borrow is final
//! at the reborrow site. This is sound because finality guarantees the parent
//! is never used after the reborrow, so the child's final value IS the parent's
//! final value.
//!
//! Tests:
//! 1. Final borrow correctly propagates prophecy (positive)
//! 2. Fresh borrow works without extra assertion (positive)
//! 3. Final borrow rejects wrong postcondition (negative)
//!
//! Part of #2181, requested by W2 for Prover verification.

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::formula::BorrowFinality;

use crate::{
    tests::helpers::{deref, eq, final_expr, int, var},
    verify::{mut_borrow::verify_mut_borrow_function_with_modes, MutBorrowRequest},
    VerificationResult,
};

/// Final-borrow optimization: `parent_final == child_final` for final borrows.
///
/// Models a reborrow chain z = &mut *y where y is final at the reborrow site.
/// Postcondition: ^y == 5. Child z resolves to 5.
/// With finality, parent_final == child_final gives y_final == z_final == 5.
///
/// Part of #2181
#[test]
#[timeout(30000)]
fn test_finality_final_borrow_propagates_prophecy() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), int(5));

    let ensures = vec![eq(final_expr(var("y")), int(5))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let mut finality = HashMap::new();
    finality.insert("y_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "finality: ^y == 5 should verify with Final borrow propagation (#2181): got {result:?}"
    );
}

/// Fresh borrow: no additional parent_final == child_final assertion.
/// Same as non-finality case but explicitly passing `BorrowFinality::Fresh`.
///
/// Part of #2181
#[test]
#[timeout(30000)]
fn test_finality_fresh_borrow_no_extra_assertion() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), int(5));

    let ensures = vec![eq(final_expr(var("y")), int(5))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let mut finality = HashMap::new();
    finality.insert("y_rb5".to_string(), BorrowFinality::Fresh);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "fresh borrow: ^y == 5 should still verify via standard writeback (#2181): got {result:?}"
    );
}

/// Negative test: Final borrow produces a concrete counterexample for an
/// incorrect postcondition.
///
/// Models z = &mut *y where z_final = 5, but we claim ^y == 99.
/// The finality assertion adds parent_final == child_final (= 5), so ^y == 99
/// fails since y_final == 5 != 99.
///
/// Part of #2181
#[test]
#[timeout(30000)]
fn test_finality_final_borrow_rejects_wrong_postcondition() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), int(5));

    // Wrong postcondition: ^y == 99 (z_final is 5, not 99)
    let ensures = vec![eq(final_expr(var("y")), int(99))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let mut finality = HashMap::new();
    finality.insert("y_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "finality: ^y == 99 should fail when child is 5 (#2181): got {result:?}"
    );
}
