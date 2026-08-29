// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost data structure (FSet, FMap, Seq) regression tests at the ay encoding
//! level. These tests exercise the ghost mutation chain patterns used by
//! `ghost/ghost_set.rs`, `ghost/ghost_map.rs`, and `ghost/ghost_vec.rs` in
//! the Creusot compat suite. (#2671)
//!
//! Each test constructs the ghost_context and preconditions that the driver
//! would produce for a proof_assert inside a ghost block, then verifies
//! that the ay encoder can handle the resulting verification request.
//!
//! The `flatten_ghost_implications` Phase 0 (ground forall instantiation)
//! enables the FSet tests to verify by instantiating universal quantifiers
//! with ground Int constants from the context. Without Phase 0, these tests
//! return Unknown(Incomplete). (#2671, #2696)

use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::*;
use crate::tests::helpers::{
    add, eq, final_expr, forall, ge, implies, int, method_call, ne, not, sub, var, var_with_sort,
    view,
};

/// Helper: create an FSet variable annotated with Int sort.
///
/// FSet values use `Sort::Int` in the UF encoding. Without this annotation,
/// the `try_synthesize_len_zero_seq_value` path incorrectly pulls FSet
/// variables into Seq sort when it sees `var.len() == 0`. (#2671)
fn fset_var(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::Int)
}

/// Helper: create an FSet carrier whose `Final(..)` projection must be kept
/// distinct from the entry value.
fn fset_mut_state_var(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::MutRef(Box::new(ExprSort::Int)))
}

/// Helper: create a Seq carrier whose `Final(..)` projection must be kept
/// distinct from the entry value.
fn seq_mut_state_var(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::MutRef(Box::new(ExprSort::Seq)))
}

/// Helper: construct `expr.method()` (no args)
fn mcall0(receiver: PureExpr, method: &str) -> PureExpr {
    method_call(receiver, method, vec![])
}

// ── FSet ghost: single insert on empty set ──────────────────────────────

/// Simulates: `let mut set = FSet::new(); ghost! { set.insert_ghost(1); proof_assert!(set.contains(1i32)); }`
///
/// Ghost context should be sufficient for the solver to prove the assertion.
/// This is the simplest FSet ghost pattern. (#2671)
#[test]
#[timeout(30000)]
fn ghost_fset_insert_contains_simple() {
    // State: call_1 = FSet::new(), then insert_ghost(1) mutates ^call_1.
    let call_1 = fset_mut_state_var("call_1");
    let set = fset_var("set");

    // Ghost context (alias facts)
    let ghost_facts = vec![
        // set == ^call_1 (after one mutation)
        eq(set.clone(), final_expr(call_1.clone())),
    ];

    // Assumed facts from FSet::new() and insert_ghost(1) specs:
    let preconditions = vec![
        // From FSet::new(): call_1.len() == 0
        eq(mcall0(call_1.clone(), "len"), int(0)),
        // From FSet::new(): forall x, !call_1.contains(x)
        forall(
            "x",
            not(method_call(call_1.clone(), "contains", vec![var("x")])),
        ),
        // From insert_ghost(1): ^call_1.contains(1)
        method_call(final_expr(call_1.clone()), "contains", vec![int(1)]),
        // Frame axiom: for all y != 1, ^call_1.contains(y) == call_1.contains(y)
        forall(
            "y",
            implies(
                ne(var("y"), int(1)),
                eq(
                    method_call(final_expr(call_1.clone()), "contains", vec![var("y")]),
                    method_call(call_1.clone(), "contains", vec![var("y")]),
                ),
            ),
        ),
    ];

    // Assertion: set.contains(1i32), i.e. ^call_1.contains(1)
    let ensures = vec![method_call(set, "contains", vec![int(1)])];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet insert_ghost(1) then contains(1) should verify: got {result:?}"
    );
}

/// Simulates: after insert_ghost(1), check !set.contains(2i32).
/// Tests the frame axiom: inserting 1 does not make 2 appear in the set.
#[test]
#[timeout(30000)]
fn ghost_fset_insert_frame_axiom() {
    let call_1 = fset_mut_state_var("call_1");
    let set = fset_var("set");

    let ghost_facts = vec![eq(set.clone(), final_expr(call_1.clone()))];

    let preconditions = vec![
        eq(mcall0(call_1.clone(), "len"), int(0)),
        forall(
            "x",
            not(method_call(call_1.clone(), "contains", vec![var("x")])),
        ),
        method_call(final_expr(call_1.clone()), "contains", vec![int(1)]),
        forall(
            "y",
            implies(
                ne(var("y"), int(1)),
                eq(
                    method_call(final_expr(call_1.clone()), "contains", vec![var("y")]),
                    method_call(call_1.clone(), "contains", vec![var("y")]),
                ),
            ),
        ),
    ];

    // Assertion: !set.contains(2i32), i.e. !^call_1.contains(2)
    let ensures = vec![not(method_call(set, "contains", vec![int(2)]))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet insert(1) frame axiom: !contains(2) should verify: got {result:?}"
    );
}

/// Simulates: after insert_ghost(1), check len() == 1.
/// Tests conditional length update through implication resolution.
#[test]
#[timeout(30000)]
fn ghost_fset_insert_len_after_insert() {
    let call_1 = fset_mut_state_var("call_1");
    let set = fset_var("set");

    let ghost_facts = vec![eq(set.clone(), final_expr(call_1.clone()))];

    // Insert return value: call_7 == !call_1.contains(1)
    let call_7 = var("call_7");
    let preconditions = vec![
        // FSet::new()
        eq(mcall0(call_1.clone(), "len"), int(0)),
        forall(
            "x",
            not(method_call(call_1.clone(), "contains", vec![var("x")])),
        ),
        // insert_ghost(1) postconditions
        method_call(final_expr(call_1.clone()), "contains", vec![int(1)]),
        forall(
            "y",
            implies(
                ne(var("y"), int(1)),
                eq(
                    method_call(final_expr(call_1.clone()), "contains", vec![var("y")]),
                    method_call(call_1.clone(), "contains", vec![var("y")]),
                ),
            ),
        ),
        // result of insert_ghost: true if element was new
        eq(
            call_7.clone(),
            not(method_call(call_1.clone(), "contains", vec![int(1)])),
        ),
        // Conditional length update
        implies(
            call_7.clone(),
            eq(
                mcall0(final_expr(call_1.clone()), "len"),
                add(mcall0(call_1.clone(), "len"), int(1)),
            ),
        ),
        implies(
            not(call_7),
            eq(
                mcall0(final_expr(call_1.clone()), "len"),
                mcall0(call_1.clone(), "len"),
            ),
        ),
    ];

    // Assertion: set.len() == 1
    let ensures = vec![eq(mcall0(set, "len"), int(1))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet insert(1) on empty set should give len==1: got {result:?}"
    );
}

// ── FSet ghost: insert then remove ──────────────────────────────────────

/// Simulates: insert(1), insert(2), remove(2) -> set contains {1}, len == 1.
/// Tests two-step mutation chain with conditional length tracking. (#2671)
#[test]
#[timeout(60000)]
fn ghost_fset_insert_remove_chain() {
    let call_1 = fset_mut_state_var("call_1");
    // State after insert_ghost(1): ^call_1
    // State after insert_ghost(2): ^^call_1
    // State after remove_ghost(2): ^^^call_1
    let set = fset_var("set");

    let ghost_facts = vec![eq(
        set.clone(),
        final_expr(final_expr(final_expr(call_1.clone()))),
    )];

    let call_ins1 = var("call_ins1");
    let call_ins2 = var("call_ins2");
    let call_rm2 = var("call_rm2");

    let preconditions = vec![
        // FSet::new()
        eq(mcall0(call_1.clone(), "len"), int(0)),
        forall(
            "x",
            not(method_call(call_1.clone(), "contains", vec![var("x")])),
        ),
        // insert_ghost(1)
        method_call(final_expr(call_1.clone()), "contains", vec![int(1)]),
        forall(
            "y",
            implies(
                ne(var("y"), int(1)),
                eq(
                    method_call(final_expr(call_1.clone()), "contains", vec![var("y")]),
                    method_call(call_1.clone(), "contains", vec![var("y")]),
                ),
            ),
        ),
        eq(
            call_ins1.clone(),
            not(method_call(call_1.clone(), "contains", vec![int(1)])),
        ),
        implies(
            call_ins1.clone(),
            eq(
                mcall0(final_expr(call_1.clone()), "len"),
                add(mcall0(call_1.clone(), "len"), int(1)),
            ),
        ),
        implies(
            not(call_ins1),
            eq(
                mcall0(final_expr(call_1.clone()), "len"),
                mcall0(call_1.clone(), "len"),
            ),
        ),
        // insert_ghost(2)
        method_call(
            final_expr(final_expr(call_1.clone())),
            "contains",
            vec![int(2)],
        ),
        forall(
            "y",
            implies(
                ne(var("y"), int(2)),
                eq(
                    method_call(
                        final_expr(final_expr(call_1.clone())),
                        "contains",
                        vec![var("y")],
                    ),
                    method_call(final_expr(call_1.clone()), "contains", vec![var("y")]),
                ),
            ),
        ),
        eq(
            call_ins2.clone(),
            not(method_call(
                final_expr(call_1.clone()),
                "contains",
                vec![int(2)],
            )),
        ),
        implies(
            call_ins2.clone(),
            eq(
                mcall0(final_expr(final_expr(call_1.clone())), "len"),
                add(mcall0(final_expr(call_1.clone()), "len"), int(1)),
            ),
        ),
        implies(
            not(call_ins2),
            eq(
                mcall0(final_expr(final_expr(call_1.clone())), "len"),
                mcall0(final_expr(call_1.clone()), "len"),
            ),
        ),
        // remove_ghost(&2)
        not(method_call(
            final_expr(final_expr(final_expr(call_1.clone()))),
            "contains",
            vec![int(2)],
        )),
        forall(
            "y",
            implies(
                ne(var("y"), int(2)),
                eq(
                    method_call(
                        final_expr(final_expr(final_expr(call_1.clone()))),
                        "contains",
                        vec![var("y")],
                    ),
                    method_call(
                        final_expr(final_expr(call_1.clone())),
                        "contains",
                        vec![var("y")],
                    ),
                ),
            ),
        ),
        eq(
            call_rm2.clone(),
            method_call(
                final_expr(final_expr(call_1.clone())),
                "contains",
                vec![int(2)],
            ),
        ),
        implies(
            call_rm2.clone(),
            eq(
                mcall0(final_expr(final_expr(final_expr(call_1.clone()))), "len"),
                sub(
                    mcall0(final_expr(final_expr(call_1.clone())), "len"),
                    int(1),
                ),
            ),
        ),
        implies(
            not(call_rm2),
            eq(
                mcall0(final_expr(final_expr(final_expr(call_1.clone()))), "len"),
                mcall0(final_expr(final_expr(call_1.clone())), "len"),
            ),
        ),
    ];

    // Assertion: set.contains(1) -- should still contain 1 after removing 2
    let ensures_contains1 = vec![method_call(set.clone(), "contains", vec![int(1)])];
    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures_contains1)
            .ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet insert(1),insert(2),remove(2) -> contains(1) should verify: got {result:?}"
    );

    // Assertion: !set.contains(2) -- removed
    let ensures_not_contains2 = vec![not(method_call(set.clone(), "contains", vec![int(2)]))];
    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures_not_contains2)
            .ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet insert(1),insert(2),remove(2) -> !contains(2) should verify: got {result:?}"
    );

    // Assertion: set.len() == 1
    let ensures_len1 = vec![eq(mcall0(set, "len"), int(1))];
    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures_len1).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet insert(1),insert(2),remove(2) -> len==1 should verify: got {result:?}"
    );
}

// ── Seq ghost: push_back on empty seq ───────────────────────────────────

/// Simulates: `let mut v = Seq::new(); ghost! { v.push_back_ghost(21); proof_assert!(v.len() == 1); }`
/// Tests the Seq ghost push_back pattern from ghost_vec.rs. (#2671)
#[test]
#[timeout(30000)]
fn ghost_seq_push_back_len() {
    let seq_sort = ExprSort::Seq;
    let call_1 = seq_mut_state_var("call_1");
    let v = var_with_sort("v", seq_sort);

    let ghost_facts = vec![eq(v.clone(), final_expr(call_1.clone()))];

    let preconditions = vec![
        // Seq::new()
        eq(mcall0(call_1.clone(), "len"), int(0)),
        // push_back_ghost(21): ^call_1 == call_1.push_back(21)
        eq(
            view(final_expr(call_1.clone())),
            method_call(call_1.clone(), "push_back", vec![int(21)]),
        ),
        // push_back len postcondition: ^call_1.len() == call_1.len() + 1
        eq(
            mcall0(final_expr(call_1.clone()), "len"),
            add(mcall0(call_1, "len"), int(1)),
        ),
    ];

    let ensures = vec![eq(mcall0(v, "len"), int(1))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Seq push_back_ghost(21) on empty seq should give len==1: got {result:?}"
    );
}

// ── Ghost Bool result: is_empty_ghost ───────────────────────────────────

/// Simulates: `assert!(v.is_empty_ghost());` on an empty Seq.
/// Tests that Bool-typed ghost results are handled correctly. (#2671)
#[test]
#[timeout(30000)]
fn ghost_seq_is_empty_on_new_seq() {
    let seq_sort = ExprSort::Seq;
    let call_1 = var_with_sort("call_1", seq_sort.clone());
    let v = var_with_sort("v", seq_sort);
    let is_empty_result = var_with_sort("is_empty_result", ExprSort::Bool);

    let ghost_facts = vec![
        eq(v.clone(), call_1.clone()),
        eq(is_empty_result.clone(), mcall0(call_1.clone(), "is_empty")),
    ];

    let preconditions = vec![
        eq(mcall0(call_1.clone(), "len"), int(0)),
        // is_empty spec: result == (self.len() == 0)
        eq(mcall0(call_1, "is_empty"), eq(mcall0(v, "len"), int(0))),
    ];

    // Assertion: is_empty_result (should be true)
    let ensures = vec![is_empty_result];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Seq is_empty_ghost() on empty seq should verify true: got {result:?}"
    );
}

// ── Ghost context non-vacuousness ───────────────────────────────────────

/// Regression: ghost context for a single FSet::insert should NOT produce
/// contradictory premises. The preconditions from FSet::new() + insert_ghost(1)
/// must be satisfiable. (#2671)
#[test]
#[timeout(30000)]
fn ghost_fset_single_insert_not_vacuous() {
    let call_1 = fset_mut_state_var("call_1");
    let set = fset_var("set");

    let ghost_facts = vec![eq(set.clone(), final_expr(call_1.clone()))];

    let call_7 = var("call_7");
    let preconditions = vec![
        eq(mcall0(call_1.clone(), "len"), int(0)),
        forall(
            "x",
            not(method_call(call_1.clone(), "contains", vec![var("x")])),
        ),
        method_call(final_expr(call_1.clone()), "contains", vec![int(1)]),
        forall(
            "y",
            implies(
                ne(var("y"), int(1)),
                eq(
                    method_call(final_expr(call_1.clone()), "contains", vec![var("y")]),
                    method_call(call_1.clone(), "contains", vec![var("y")]),
                ),
            ),
        ),
        eq(
            call_7.clone(),
            not(method_call(call_1.clone(), "contains", vec![int(1)])),
        ),
        implies(
            call_7.clone(),
            eq(
                mcall0(final_expr(call_1.clone()), "len"),
                add(mcall0(call_1.clone(), "len"), int(1)),
            ),
        ),
        implies(
            not(call_7),
            eq(
                mcall0(final_expr(call_1.clone()), "len"),
                mcall0(call_1, "len"),
            ),
        ),
    ];

    // A tautological assertion that should verify non-vacuously.
    // set.len() >= 0 is always true for any FSet.
    let ensures = vec![ge(mcall0(set, "len"), int(0))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    // Should be Verified, not Unknown("vacuous")
    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "FSet insert ghost context should not produce contradictory premises: got {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "FSet len >= 0 should verify non-vacuously: got {result:?}"
    );
}

// ── Minimal ghost aliasing diagnostic ──────────────────────────────────

/// Minimal test: ghost equality set == ^call_1, precondition ^call_1.contains(1),
/// postcondition set.contains(1). No quantifiers. Pure EUF congruence.
/// If this fails, the issue is in how the encoder handles ghost aliasing
/// with UF method calls, not in quantifier handling.
#[test]
#[timeout(10000)]
fn ghost_fset_minimal_alias_contains() {
    let call_1 = fset_var("call_1");
    let set = fset_var("set");

    let ghost_facts = vec![eq(set.clone(), final_expr(call_1.clone()))];

    // Minimal preconditions: just the direct assertion
    let preconditions = vec![method_call(final_expr(call_1), "contains", vec![int(1)])];

    // Postcondition: set.contains(1) should follow from ghost alias
    let ensures = vec![method_call(set, "contains", vec![int(1)])];

    let result = verify_function_with_modes(
        VerificationRequest::new(&preconditions, &ensures).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Minimal ghost alias: set==^call_1, ^call_1.contains(1) |- set.contains(1) should verify: got {result:?}"
    );
}
