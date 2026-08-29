// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutation-continued and resolve interaction tests (#2124 Phase 5, 5b).

use std::collections::{HashMap, HashSet};

use ntest::timeout;

use crate::{
    tests::helpers::{add, deref, eq, final_expr, int, ne, var},
    verify::{mut_borrow::verify_mut_borrow_function_with_modes, types::MutBorrowRequest},
    UnknownReason, VerificationResult,
};

// ── mutation_continued_params (#2124 Phase 5) ──────────────────────

/// Identity assertion is suppressed for mutation-continued params.
#[test]
#[timeout(30000)]
fn mutation_continued_skips_identity_assertion() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let ensures = vec![ne(final_expr(var("v")), deref(var("v")))];

    // Without mutation_continued: identity asserts v_final == v_current.
    let result_normal =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result_normal, VerificationResult::Failed(_)),
        "without mutation_continued, ^v != *v should be falsifiable: got {result_normal:?}"
    );

    // With mutation_continued: identity assertion is skipped.
    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());
    let result_continued = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result_continued, VerificationResult::Failed(_)),
        "unconstrained v_final should leave ^v != *v falsifiable: got {result_continued:?}"
    );
}

/// Call assumption + mutation_continued enables postcondition proof.
#[test]
#[timeout(30000)]
fn mutation_continued_with_call_assumption_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let call_assumption = eq(final_expr(var("v")), add(deref(var("v")), int(1)));
    let requires = vec![call_assumption];
    let ensures = vec![eq(final_expr(var("v")), add(deref(var("v")), int(1)))];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "call assumption should prove postcondition: got {result:?}"
    );
}

/// Without mutation_continued, identity + call_assumption contradiction.
#[test]
#[timeout(30000)]
fn without_mutation_continued_creates_contradiction() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let call_assumption = eq(final_expr(var("v")), add(deref(var("v")), int(1)));
    let requires = vec![call_assumption];
    let ensures = vec![eq(int(0), int(1))];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    // Contradiction makes 0 == 1 vacuously true (unsound without guard).
    // Vacuity guard (#2414) now demotes this to Unknown.
    match result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg)) => {
            assert!(
                msg.contains("vacuous"),
                "vacuity guard should report a vacuous proof: {msg}"
            );
        }
        other => panic!("vacuity guard should detect contradictory base: got {other:?}"),
    }
}

// ── Phase 5b: resolve + mutation_continued interaction (#2124) ───

/// Resolve assertion is skipped for mutation-continued params.
///
/// Models: `fn f(v: &mut i32) { *v += 1; }`
/// - call_assumption: `^v == *v + 1`
/// - resolve: v has precise resolve point
/// - mutation_continued: v is in the set
///
/// Without Phase 5b, resolve would assert `v_final == v_current` which
/// contradicts the call assumption `v_final == v_current + 1`. With Phase 5b,
/// resolve skips mutation-continued params and the postcondition is provable.
#[test]
#[timeout(30000)]
fn resolve_skips_mutation_continued_param() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // call_assumption: ^v == *v + 1 (merged into requires)
    let call_assumption = eq(final_expr(var("v")), add(deref(var("v")), int(1)));
    let requires = vec![call_assumption];
    // postcondition: ^v == *v + 1
    let ensures = vec![eq(final_expr(var("v")), add(deref(var("v")), int(1)))];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    // With mutation_continued + resolve: resolve skips v, call_assumption proves postcondition.
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp))
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve should skip mutation-continued param, letting call_assumption prove postcondition: got {result:?}"
    );
}

/// Without mutation_continued, resolve + call_assumption creates contradiction.
///
/// Demonstrates that resolve `v_final == v_current` + call assumption
/// `v_final == v_current + 1` is contradictory (makes anything provable).
#[test]
#[timeout(30000)]
fn resolve_without_mutation_continued_creates_contradiction() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // call_assumption: ^v == *v + 1
    let call_assumption = eq(final_expr(var("v")), add(deref(var("v")), int(1)));
    let requires = vec![call_assumption];
    // absurd postcondition: 0 == 1 — only provable under contradiction
    let ensures = vec![eq(int(0), int(1))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .resolve_assumptions(Some(vec!["v".to_string()])),
    )
    .expect("encoding should succeed");

    // Resolve asserts v_final == v_current, call says v_final == v_current + 1
    // => v_current == v_current + 1 => 0 == 1 => contradiction.
    // Vacuity guard (#2414) now demotes this to Unknown.
    match result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg)) => {
            assert!(
                msg.contains("vacuous"),
                "vacuity guard should report a vacuous proof: {msg}"
            );
        }
        other => {
            panic!("vacuity guard should detect contradictory resolve + call: got {other:?}");
        }
    }
}

/// Mixed params: mutation-continued and non-mutation-continued resolve correctly.
///
/// Models: `fn f(v: &mut i32, w: &mut i32) { *v += 1; }`
/// - v is mutation-continued (received mutation call)
/// - w is NOT mutation-continued (identity: ^w == *w)
/// - Both have resolve points
///
/// Resolve should skip v (letting call_assumption constrain it) but
/// assert `w_final == w_current` (identity, since w wasn't mutated).
#[test]
#[timeout(30000)]
fn mixed_resolve_mutation_continued_and_normal() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));
    final_values.insert("w".to_string(), deref(var("w")));

    // call_assumption: ^v == *v + 1
    let call_assumption = eq(final_expr(var("v")), add(deref(var("v")), int(1)));
    let requires = vec![call_assumption];
    // postcondition: ^v == *v + 1 AND ^w == *w (both should verify)
    let ensures = vec![
        eq(final_expr(var("v")), add(deref(var("v")), int(1))),
        eq(final_expr(var("w")), deref(var("w"))),
    ];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());
    // w is NOT in mutation_continued

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp))
            .resolve_assumptions(Some(vec!["v".to_string(), "w".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mixed resolve: v via call_assumption, w via resolve identity: got {result:?}"
    );
}

// ── resolve_assumptions with no matching final_values (#1945) ────

/// When resolve_assumptions contains a name that has no corresponding entry
/// in final_values, the emit function silently skips the assertion (the
/// `if let` guard at resolve.rs:47 fails). This is conservative (no false
/// proofs) but could mask driver bugs.
///
/// This test documents the behavior: a param in resolve_assumptions but NOT
/// in final_values produces no constraint — the postcondition falls through
/// to the default behavior (unconstrained v_final).
#[test]
#[timeout(30000)]
fn resolve_with_phantom_param_is_conservative() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));
    // "w" is NOT in final_values — it's a phantom in resolve_assumptions

    // postcondition: ^v == *v (identity, should verify via resolve for v)
    let ensures = vec![eq(final_expr(var("v")), deref(var("v")))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).resolve_assumptions(Some(vec![
            "v".to_string(),
            "w".to_string(), // phantom: no final_values entry
        ])),
    )
    .expect("encoding should succeed");

    // v resolves normally (v_final == v_current). w is silently skipped.
    // The postcondition only references v, so it should verify.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "phantom param in resolve_assumptions should be silently skipped: got {result:?}"
    );
}

// ── bug/682 followup: delayed-writeback + mutation_continued (#5) ────

/// Regression test for the `foo` function-contract path in
/// `reference/creusot/tests/should_succeed/bug/682.rs`.
///
/// The driver-side bug (sibling of #2663): the two-phase-borrow analysis
/// emits a delayed-writeback assumption `*a == ^a_rb6` for the implicit
/// `&mut *a` reborrow at the `add_some(a)` call site. That assumption is
/// merged into the function's preconditions BEFORE the ay layer ever sees
/// it, so the `emit_prophecy_writebacks` gate added for #5 cannot suppress
/// it — by then the equation is already a precondition.
///
/// At the ay level, the equation collapses to
/// `a_current == a_rb6_final`. Combined with the `add_some` call_assumption
/// `^a > *a` (encoded as `a_final > a_current`), the standard prophecy
/// final propagation `a_final == a_rb6_final`, and the `#[requires(*a == 3)]`
/// precondition, the base premises form
///
/// ```text
///   a_current == 3
///   a_final > a_current
///   a_current == a_rb6_final
///   a_final == a_rb6_final
/// ```
///
/// which is UNSAT and trips the vacuity guard. The driver-side fix filters
/// the `*parent == ^child` delayed-writeback assumption when `parent` is in
/// `mutation_continued_params`, leaving the `^parent == ^child` final-side
/// propagation in place. This test models the *post-filter* preconditions:
/// the function-contract verification must close without going vacuous.
#[test]
#[timeout(30000)]
fn bug_682_function_contract_non_vacuous_after_delayed_writeback_filter() {
    // mutation-continued: add_some(a) cannot be symbolically advanced
    let mut mcp = HashSet::new();
    mcp.insert("a".to_string());

    // call_assumption from add_some's `^a > *a` (gt, not eq).
    let call_assumption = crate::tests::helpers::gt(final_expr(var("a")), deref(var("a")));
    // The `^a == ^a_rb6` final-side propagation that survives the filter.
    let final_side_writeback = eq(final_expr(var("a")), final_expr(var("a_rb6")));
    let requires = vec![
        eq(deref(var("a")), int(3)),
        call_assumption,
        final_side_writeback,
    ];
    let ensures = vec![crate::tests::helpers::gt(
        final_expr(var("a")),
        deref(var("a")),
    )];

    let final_values = HashMap::new();
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
            if msg.contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "bug/682 function-contract base premises must be consistent after delayed-writeback filter: got {result:?}"
    );
}
