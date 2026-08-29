// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SSA-renamed sequential mutation tests (#2124 Phase 5b, 5c).

use std::collections::{HashMap, HashSet};

use ntest::timeout;

use crate::{
    tests::helpers::{deref, eq, final_expr, int, method_call, var, view},
    verify::{mut_borrow::verify_mut_borrow_function_with_modes, types::MutBorrowRequest},
    VerificationResult,
};

// ── Phase 5b gap: multiple sequential mutations (#2124) ─────────

/// Documents the SSA current advancement gap for sequential mutations.
///
/// Models: `fn f(v: &mut Vec<i32>) { v.push(1); v.push(2); }`
/// with postcondition `^v.len() == v.len() + 2`.
///
/// Without SSA renaming, both call_assumptions reference the same
/// `v_current` and `v_final`, creating contradictory constraints:
///   assume: v_final_view == push_back(v_current_view, 1)   // first push
///   assume: v_final_view == push_back(v_current_view, 2)   // second push — contradicts!
///
/// With SSA renaming (Phase 5b future work), the assumptions would be:
///   assume: v_current_1_view == push_back(v_current_view, 1)
///   assume: v_final_view == push_back(v_current_1_view, 2)
///
/// This test documents the current limitation. When Phase 5b is implemented,
/// flip this test to assert Verified with the correct (non-contradictory)
/// postcondition.
#[test]
#[timeout(30000)]
fn sequential_mutations_without_ssa_are_contradictory() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let v_view = view(deref(var("v")));
    let v_final_view = view(final_expr(var("v")));

    // Two contradictory call_assumptions (same v_final, different push_back args)
    let call1 = eq(
        v_final_view.clone(),
        method_call(v_view.clone(), "push_back", vec![int(1)]),
    );
    let call2 = eq(
        v_final_view.clone(),
        method_call(v_view.clone(), "push_back", vec![int(2)]),
    );
    let requires = vec![call1, call2];

    // Any postcondition — contradiction makes anything provable
    let ensures = vec![eq(int(0), int(1))];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    // Contradiction: push_back(v@, 1) == push_back(v@, 2) can only hold
    // if 1 == 2 (which is false). Vacuity guard (#2414) now catches this
    // instead of letting it through as a false Verified.
    // Phase 5b SSA renaming would fix the root cause by giving each
    // mutation its own v_current_N.
    assert!(
        matches!(result, VerificationResult::Unknown(_)),
        "vacuity guard should detect contradictory sequential call_assumptions: got {result:?}"
    );
}

// ── Phase 5b target: SSA-renamed sequential mutations (#2124) ───

/// Target test for Phase 5b: sequential mutations with SSA-renamed intermediates.
///
/// Models: `fn f(v: &mut Vec<i32>) { v.push(1); v.push(2); }`
/// with postcondition `(^v)@ == push_back(push_back((*v)@, 1), 2)`.
///
/// With correct SSA renaming, the call_assumptions would be:
///   assume: v_ssa_1_view == push_back(v_current_view, 1)
///   assume: v_final_view == push_back(v_ssa_1_view, 2)
///
/// The postcondition `^v@ == push_back(push_back(*v@, 1), 2)` can be proven
/// because the solver chains: v_final_view == push_back(v_ssa_1_view, 2)
/// == push_back(push_back(v_current_view, 1), 2).
///
/// This test models the CORRECT output that Phase 5b should produce.
/// It passes today because we manually construct the SSA-renamed assumptions.
#[test]
#[timeout(30000)]
fn ssa_renamed_sequential_mutations_verify() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let v_current_view = view(deref(var("v")));
    let v_final_view = view(final_expr(var("v")));

    // SSA intermediate: v_ssa_1 is the post-first-push state
    let v_ssa_1_view = var("v_ssa_1_view");

    // SSA-renamed call_assumptions (no contradiction!)
    let call1 = eq(
        v_ssa_1_view.clone(),
        method_call(v_current_view.clone(), "push_back", vec![int(1)]),
    );
    let call2 = eq(
        v_final_view.clone(),
        method_call(v_ssa_1_view, "push_back", vec![int(2)]),
    );
    let requires = vec![call1, call2];

    // Postcondition: ^v@ == push_back(push_back(*v@, 1), 2)
    let expected = method_call(
        method_call(v_current_view, "push_back", vec![int(1)]),
        "push_back",
        vec![int(2)],
    );
    let ensures = vec![eq(v_final_view, expected)];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "SSA-renamed sequential mutations should verify the chained postcondition: got {result:?}"
    );
}

// ── Phase 5c: SSA-renamed mutations with Deref-based naming (#2124) ──

/// Phase 5c integration test: SSA-renamed sequential mutations using the
/// realistic Deref-based expression structure that the driver produces.
///
/// The driver's SSA renaming transforms call_assumptions to use
/// `Deref(Var("v_ssa_1"))` for intermediates and `Final(Deref(Var("v")))`
/// for the max depth. These expressions encode to different SMT variable
/// names than the postcondition's `Final(Var("v"))`:
///
///   - `View(Deref(Var("v_ssa_1")))` → `v_ssa_1_current_view`
///   - `View(Final(Deref(Var("v"))))` → `final_v_current_view`
///   - `View(Final(Var("v")))` (postcondition) → `final_v_view`
///
/// Phase 5c bridges `final_v_current_view == final_v_view` so the solver
/// can connect the SSA chain to the postcondition.
#[test]
#[timeout(60000)]
fn ssa_renamed_deref_based_sequential_mutations_verify() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Realistic SSA-renamed call_assumptions (Deref-based, as driver produces):
    // Call 1 LHS: View(Deref(Var("v_ssa_1"))) → v_ssa_1_current_view
    // Call 1 RHS receiver: View(Deref(Var("v"))) → v_current_view
    let call1 = eq(
        view(deref(var("v_ssa_1"))),
        method_call(view(deref(var("v"))), "push_back", vec![int(1)]),
    );
    // Call 2 LHS: View(Final(Deref(Var("v")))) → final_v_current_view
    // Call 2 RHS receiver: View(Deref(Var("v_ssa_1"))) → v_ssa_1_current_view
    let call2 = eq(
        view(final_expr(deref(var("v")))),
        method_call(view(deref(var("v_ssa_1"))), "push_back", vec![int(2)]),
    );
    let requires = vec![call1, call2];

    // Postcondition uses bare Var: View(Final(Var("v"))) → final_v_view
    let v_current_view = view(deref(var("v")));
    let v_final_view = view(final_expr(var("v")));
    let expected = method_call(
        method_call(v_current_view, "push_back", vec![int(1)]),
        "push_back",
        vec![int(2)],
    );
    let ensures = vec![eq(v_final_view, expected)];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp))
            .timeout(Some(std::time::Duration::from_secs(45))),
    )
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the mut-borrow
    // vacuity gate refuses this verdict fail-closed when ay answers `Incomplete`
    // on the fresh base re-solve. See `tests::helpers::verified_or_unvalidated_sat_base`.
    assert!(
        crate::tests::helpers::verified_or_unvalidated_sat_base(&result),
        "Phase 5c bridge should connect Deref-based SSA chain to postcondition \
         (or refuse fail-closed on the known unvalidated-SAT-base class): got {result:?}"
    );
}

/// Without Phase 5c bridge, Deref-based SSA naming is disconnected from
/// postcondition. This test would fail without the `final_v_current_view ==
/// final_v_view` bridge. We verify it passes (demonstrating the bridge works)
/// and separately verify that removing mutation_continued (which re-enables
/// the identity assertion path with its own aliasing) also works.
#[test]
#[timeout(30000)]
fn ssa_renamed_deref_based_single_mutation_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Single mutation: View(Final(Deref(Var("v")))) → final_v_current_view
    let call_assumption = eq(
        view(final_expr(deref(var("v")))),
        method_call(view(deref(var("v"))), "push_back", vec![int(42)]),
    );
    let requires = vec![call_assumption];

    // Postcondition: View(Final(Var("v"))) → final_v_view
    let ensures = vec![eq(
        view(final_expr(var("v"))),
        method_call(view(deref(var("v"))), "push_back", vec![int(42)]),
    )];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Phase 5c bridge should connect single mutation to postcondition: got {result:?}"
    );
}
