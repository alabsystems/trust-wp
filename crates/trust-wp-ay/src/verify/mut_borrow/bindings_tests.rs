// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for per-parameter final-value bindings (`bindings.rs`).
//!
//! These tests exercise the `_current_final` alias wiring, multi-parameter
//! binding independence, view alias chains, sort annotation propagation,
//! and mutation_continued branching in `bind_final_values` / `bind_single_final_value`.
//!
//! The key invariant: `Final(Deref(Var("v")))` resolves to `v_current_final`
//! (via `resolve_nameable_expr`), and `bindings.rs` must wire this alias to:
//! - `final_term` (non-mutation_continued path, #2190/#858)
//! - `final_var` (mutation_continued path, #2124 Phase 5c)
//!
//! Without these bindings, postconditions referencing `^(*v)` (which compiles
//! to `Final(Deref(Var("v")))`) would see an unconstrained variable.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::verify_mut_borrow_function_with_modes;
use crate::{
    encoder::AYEncoder,
    tests::helpers::{
        add, and, deref, eq, final_expr, gt, int, ite, logic_fn_call, method_call, old, sub, var,
        var_with_sort, view,
    },
    verify::types::MutBorrowRequest,
    UnknownReason, VerificationResult,
};

#[track_caller]
fn assert_semantically_equal(
    encoder: &mut AYEncoder,
    left: ay_dpll::api::Term,
    right: ay_dpll::api::Term,
    context: &str,
) {
    let equality = encoder.test_seq_aware_equality_term(left, right);
    let inequality = encoder.solver_mut().not(equality);
    encoder.assert_term(inequality);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "{context}: result={result:?}, reason={:?}",
        encoder.last_unknown_reason()
    );
}

// ── _current_final alias: non-mutation_continued path (#2190, #858) ─────

/// `Final(Deref(Var("v")))` (= `v_current_final`) should equal the computed
/// final expression. This verifies the binding at bindings.rs:58-61.
///
/// Re: #2190, #858
#[test]
#[timeout(30000)]
fn test_current_final_alias_equals_computed_final_value() {
    let mut final_values = HashMap::new();
    // final_values: v -> *v + 1
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // Postcondition: ^(*v) == *v + 1
    // Final(Deref(Var("v"))) resolves to v_current_final, which should
    // equal the final expression (*v + 1) via the binding.
    let ensures = vec![eq(
        final_expr(deref(var("v"))),
        add(deref(var("v")), int(1)),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "^(*v) should equal the computed final expression (*v + 1): got {result:?}"
    );
}

/// Negative companion: `v_current_final` should NOT equal a wrong value.
#[test]
#[timeout(30000)]
fn test_current_final_alias_wrong_value_fails() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // Postcondition: ^(*v) == *v + 2 (wrong! should be *v + 1)
    let ensures = vec![eq(
        final_expr(deref(var("v"))),
        add(deref(var("v")), int(2)),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "^(*v) should NOT equal wrong value (*v + 2): got {result:?}"
    );
}

/// `v_current_final` and `v_final` should both equal `final_term`, so
/// `Final(Deref(Var("v"))) == Final(Var("v"))` must hold.
///
/// This verifies the transitivity between bindings.rs:53 (v_final = final_term)
/// and bindings.rs:61 (v_current_final = final_term).
#[test]
#[timeout(30000)]
fn test_current_final_equals_final_var_transitivity() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // Postcondition: ^(*v) == ^v
    let ensures = vec![eq(final_expr(deref(var("v"))), final_expr(var("v")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "^(*v) should transitively equal ^v: got {result:?}"
    );
}

/// With a complex final expression (conditional), `v_current_final` should
/// still correctly track the encoded value.
#[test]
#[timeout(30000)]
fn test_current_final_with_conditional_final_expr() {
    let mut final_values = HashMap::new();
    // final_values: v -> if *v > 0 then *v - 1 else 0
    let conditional_final = ite(
        gt(deref(var("v")), int(0)),
        sub(deref(var("v")), int(1)),
        int(0),
    );
    final_values.insert("v".to_string(), conditional_final.clone());

    // Postcondition: ^(*v) == if *v > 0 then *v - 1 else 0
    let ensures = vec![eq(final_expr(deref(var("v"))), conditional_final)];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "^(*v) should equal conditional final expression: got {result:?}"
    );
}

// ── _current_final alias: mutation_continued path (#2124 Phase 5c) ──────

/// When `mutation_continued_params` includes a parameter, `v_current_final`
/// links to `v_final` (not to `final_term`). This means ghost_context
/// constraints on `^v` (v_final) propagate to `^(*v)` (v_current_final).
///
/// Re: #2124 Phase 5c
#[test]
#[timeout(30000)]
fn test_mutation_continued_current_final_links_to_final_var() {
    let mut final_values = HashMap::new();
    // Identity body: v_final = *v (will be overridden by call assumption)
    final_values.insert("v".to_string(), deref(var("v")));

    // Ghost context constrains v_final: ^v == *v + 1
    let ghost = vec![eq(final_expr(var("v")), add(deref(var("v")), int(1)))];

    // Postcondition: ^(*v) == *v + 1
    // In mutation_continued mode, v_current_final links to v_final (not final_term),
    // so the ghost constraint on v_final propagates.
    let ensures = vec![eq(
        final_expr(deref(var("v"))),
        add(deref(var("v")), int(1)),
    )];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .ghost_context(Some(&ghost))
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mutation_continued ^(*v) should propagate ghost constraint on ^v: got {result:?}"
    );
}

/// Without mutation_continued, the ghost constraint on ^v does NOT override
/// the identity final_values binding, so ^(*v) == *v (identity), not *v + 1.
#[test]
#[timeout(30000)]
fn test_non_mutation_continued_ignores_ghost_override() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Ghost tries to override: ^v == *v + 1
    let ghost = vec![eq(final_expr(var("v")), add(deref(var("v")), int(1)))];

    // Postcondition: ^(*v) == *v + 1 (should FAIL because binding pins to *v)
    let ensures = vec![eq(
        final_expr(deref(var("v"))),
        add(deref(var("v")), int(1)),
    )];

    // No mutation_continued — the binding pins v_current_final to final_term (*v)
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost)),
    )
    .expect("encoding should succeed");

    // Without mutation_continued, v_current_final == v_current (identity body),
    // and v_final is ALSO bound to v_current (identity). The ghost then adds
    // v_final == v_current + 1, creating a contradiction (v_current == v_current + 1).
    // Vacuity guard detects this.
    match result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg)) => {
            assert!(
                msg.contains("vacuous"),
                "ghost override contradiction should report a vacuous proof: {msg}"
            );
        }
        other => panic!("without mutation_continued, ghost override should be vacuous: {other:?}"),
    }
}

// ── Multi-parameter binding independence ─────────────────────────────────

/// Multiple parameters should bind independently — each final_value
/// constrains only its own parameter.
#[test]
#[timeout(30000)]
fn test_multiple_params_bind_independently() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), add(deref(var("a")), int(1)));
    final_values.insert("b".to_string(), add(deref(var("b")), int(2)));

    // Postcondition: ^a + ^b == *a + *b + 3
    let ensures = vec![eq(
        add(final_expr(var("a")), final_expr(var("b"))),
        add(add(deref(var("a")), deref(var("b"))), int(3)),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "independent parameter bindings should compose correctly: got {result:?}"
    );
}

/// Negative companion: wrong sum should fail.
#[test]
#[timeout(30000)]
fn test_multiple_params_wrong_sum_fails() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), add(deref(var("a")), int(1)));
    final_values.insert("b".to_string(), add(deref(var("b")), int(2)));

    // Wrong: ^a + ^b == *a + *b + 4 (should be 3)
    let ensures = vec![eq(
        add(final_expr(var("a")), final_expr(var("b"))),
        add(add(deref(var("a")), deref(var("b"))), int(4)),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong sum should fail: got {result:?}"
    );
}

/// `_current_final` alias works independently per-parameter.
#[test]
#[timeout(30000)]
fn test_multiple_params_current_final_independent() {
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), add(deref(var("a")), int(10)));
    final_values.insert("b".to_string(), add(deref(var("b")), int(20)));

    // Postcondition using ^(*a) and ^(*b) — the _current_final aliases
    let ensures = vec![eq(
        add(final_expr(deref(var("a"))), final_expr(deref(var("b")))),
        add(add(deref(var("a")), deref(var("b"))), int(30)),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "^(*a) + ^(*b) should equal *a + *b + 30: got {result:?}"
    );
}

// ── Mixed mutation_continued + normal bindings ──────────────────────────

/// One parameter mutation_continued, another normal — both should work.
#[test]
#[timeout(30000)]
fn test_mixed_mutation_continued_and_normal() {
    let mut final_values = HashMap::new();
    // a: mutation_continued (identity body, ghost overrides)
    final_values.insert("a".to_string(), deref(var("a")));
    // b: normal (computed final)
    final_values.insert("b".to_string(), add(deref(var("b")), int(1)));

    let ghost = vec![eq(final_expr(var("a")), add(deref(var("a")), int(5)))];

    // ^a == *a + 5 (from ghost) AND ^b == *b + 1 (from final_values)
    let ensures = vec![and(
        eq(final_expr(var("a")), add(deref(var("a")), int(5))),
        eq(final_expr(var("b")), add(deref(var("b")), int(1))),
    )];

    let mut mcp = HashSet::new();
    mcp.insert("a".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .ghost_context(Some(&ghost))
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mixed mutation_continued and normal params should verify: got {result:?}"
    );
}

// ── View alias wiring ───────────────────────────────────────────────────

/// Indexed writes without a predeclared `final_a_view` must fall back to the
/// encoded `.set(...)` final term when advancing `a_view`.
#[test]
#[timeout(30000)]
fn test_indexed_write_base_view_falls_back_to_final_term_without_final_view() {
    let mut encoder = AYEncoder::new();
    let a_ref = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let indexed_write = method_call(view(deref(a_ref)), "set", vec![int(0), int(42)]);

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), indexed_write.clone());

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("indexed-write binding should succeed");

    let a_view = encoder
        .var_term("a_view")
        .expect("indexed-write binding should declare a_view");
    let final_term = encoder
        .encode_pure(&indexed_write)
        .expect("set(...) final expression should re-encode");

    assert_semantically_equal(
        &mut encoder,
        a_view,
        final_term,
        "a_view must equal the set(...) final term when final_a_view is absent",
    );
}

/// Indexed writes keep `old_a_view` tied to the entry-state current view even
/// while `a_view` advances to the post-write state.
#[test]
#[timeout(30000)]
fn test_indexed_write_old_base_view_stays_on_current_view() {
    let mut encoder = AYEncoder::new();
    let a_ref = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let indexed_write = method_call(view(deref(a_ref)), "set", vec![int(0), int(42)]);

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), indexed_write);

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("indexed-write binding should succeed");

    let old_a_view = encoder
        .var_term("old_a_view")
        .expect("indexed-write binding should declare old_a_view");
    let a_current_view = encoder
        .var_term("a_current_view")
        .expect("indexed-write binding should declare a_current_view");

    assert_semantically_equal(
        &mut encoder,
        old_a_view,
        a_current_view,
        "old_a_view must stay equal to a_current_view across indexed writes",
    );
}

/// If `final_a_view` already exists, indexed-write advancement should reuse it
/// rather than falling back to the raw `.set(...)` term.
#[test]
#[timeout(30000)]
fn test_indexed_write_base_view_reuses_predeclared_final_view() {
    let mut encoder = AYEncoder::new();
    let a_ref = var_with_sort("a", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let predeclared_final_view = encoder
        .encode_pure(&view(final_expr(a_ref.clone())))
        .expect("view(^a) should predeclare final_a_view");
    let indexed_write = method_call(view(deref(a_ref)), "set", vec![int(0), int(42)]);

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), indexed_write);

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("indexed-write binding should succeed");

    let a_view = encoder
        .var_term("a_view")
        .expect("indexed-write binding should declare a_view");

    assert_semantically_equal(
        &mut encoder,
        a_view,
        predeclared_final_view,
        "a_view must reuse the predeclared final_a_view on indexed writes",
    );
}

/// For non-indexed writes, `v_view` (base) should alias `v_current_view`.
/// This verifies bindings.rs:167 — the `base_view_term == current_view_term` path.
#[test]
#[timeout(30000)]
fn test_view_base_aliases_current_view_non_indexed() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // View(Var("v")) maps to v_view, View(Deref(Var("v"))) maps to v_current_view.
    // The binding at line 167 asserts v_view == v_current_view.
    let ensures = vec![eq(view(var("v")), view(deref(var("v"))))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "v_view should alias v_current_view for non-indexed writes: got {result:?}"
    );
}

/// View alias with a precondition on the view — the view identity should
/// preserve precondition constraints.
#[test]
#[timeout(30000)]
fn test_view_alias_preserves_precondition_constraint() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Precondition on view: (*v)@.len() > 0
    let requires = vec![gt(
        method_call(view(deref(var("v"))), "len", vec![]),
        int(0),
    )];

    // Postcondition using base view: v@.len() > 0
    // Should verify because v_view == v_current_view.
    let ensures = vec![gt(method_call(view(var("v")), "len", vec![]), int(0))];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "view alias should preserve the precondition constraint: got {result:?}"
    );
}

// ── Empty final_values edge case ────────────────────────────────────────

/// Empty `final_values` should not panic or error — the loop body in
/// `bind_final_values` simply doesn't execute.
#[test]
#[timeout(30000)]
fn test_empty_final_values_no_panic() {
    let final_values = HashMap::new();
    let ensures = vec![eq(int(1), int(1))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty final_values should verify trivial postcondition: got {result:?}"
    );
}

/// Empty `final_values` with mutation_continued set should not panic.
#[test]
#[timeout(30000)]
fn test_empty_final_values_with_mutation_continued_no_panic() {
    let final_values = HashMap::new();
    let ensures = vec![eq(int(1), int(1))];

    let mut mcp = HashSet::new();
    mcp.insert("nonexistent".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty final_values with mutation_continued should not panic: got {result:?}"
    );
}

// ── Whole-MutRef carrier gating (#2141 Phase 1) ────────────────────────

/// Scalar-only mut-borrow bindings must not synthesize whole-borrow id
/// variables unless setup already established the base variable as a `MutRef`
/// carrier.
#[test]
#[timeout(30000)]
fn test_scalar_binding_does_not_declare_id_without_whole_mutref_carrier() {
    let mut encoder = AYEncoder::new();

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("scalar binding should succeed");

    assert!(
        !encoder.vars_for_test().contains_key("v_id"),
        "scalar-only binding must not declare v_id without a predeclared whole MutRef carrier; vars: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
    assert!(
        encoder.var_sort("v").is_none(),
        "scalar-only binding must not synthesize a whole-borrow base var"
    );
}

/// Once setup/predeclaration has established the base variable as a whole
/// `MutRef` carrier, final-value binding must preserve that carrier sort
/// instead of collapsing the base variable back to a scalar referent sort.
#[test]
#[timeout(30000)]
fn test_predeclared_whole_mutref_carrier_preserves_base_sort() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let whole_var = var_with_sort("v", ExprSort::MutRef(Box::new(ExprSort::Int)));
    encoder
        .get_or_declare_var("v", whole_sort.clone())
        .expect("predeclared whole carrier should encode");

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(whole_var));

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("whole-carrier binding should succeed");

    assert_eq!(
        encoder.var_sort("v"),
        Some(&whole_sort),
        "whole-carrier binding must preserve the predeclared MutRef sort"
    );
    assert_eq!(
        encoder.var_sort("v_current"),
        Some(&ay_dpll::api::Sort::Int),
        "whole-carrier binding must still declare the current component with the inner referent sort"
    );
    assert_eq!(
        encoder.var_sort("v_final"),
        Some(&ay_dpll::api::Sort::Int),
        "whole-carrier binding must still declare the final component with the inner referent sort"
    );
    assert!(
        encoder.vars_for_test().contains_key("v_id"),
        "whole-carrier binding must declare the borrow id sidecar"
    );
}

// ── Sort annotation propagation ─────────────────────────────────────────

/// Sort annotation on final expression should propagate through bindings
/// without producing sort mismatches.
#[test]
#[timeout(30000)]
fn test_sort_annotation_seq_no_mismatch() {
    use trust_wp_core::formula::ExprSort;

    let mut final_values = HashMap::new();
    // Final expression with Seq sort annotation
    final_values.insert(
        "v".to_string(),
        PureExpr::Var("v_current".to_string(), Some(ExprSort::Seq)),
    );

    let ensures = vec![eq(final_expr(var("v")), final_expr(var("v")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values));

    // Should not panic with sort mismatch
    assert!(
        result.is_ok(),
        "Seq-annotated final expression should not cause sort mismatch: {result:?}"
    );
}

/// ExprSort::Bool annotation on final expression should produce Bool-sorted
/// bindings, enabling boolean equality/iff assertions.
#[test]
#[timeout(30000)]
fn test_sort_annotation_bool_propagation() {
    let mut final_values = HashMap::new();
    // Final expression: a boolean-sorted variable
    final_values.insert(
        "flag".to_string(),
        PureExpr::Var("flag_current".to_string(), Some(ExprSort::Bool)),
    );

    let ensures = vec![eq(final_expr(var("flag")), final_expr(var("flag")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values));

    assert!(
        result.is_ok(),
        "Bool-annotated final expression should not cause sort errors: {result:?}"
    );
}

/// Registered user ADTs that collide with a collection-model bare name (for
/// example `List`) must keep their declared datatype sort in mut-borrow
/// bindings instead of collapsing to the Seq carrier. This mirrors compat
/// `bug/1562`, where `call_*_current` would otherwise be declared as Seq.
#[test]
#[timeout(30000)]
fn test_sort_annotation_registered_list_prefers_datatype_in_bindings() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_all();
    let list_dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "List".to_string(),
            fields: vec![DatatypeField {
                name: "list_head".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&list_dt);

    let mut final_values = HashMap::new();
    final_values.insert(
        "v".to_string(),
        PureExpr::Var(
            "v_current".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("crate::List"))),
        ),
    );

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("binding registered List final value should succeed");

    assert_eq!(
        encoder.var_sort("v_current"),
        Some(&Sort::Datatype(list_dt)),
        "registered List annotations must preserve the datatype sort in current bindings"
    );
}

// ── Cross-path interaction: _current_final with preconditions ───────────

/// Precondition constraint flows through `_current_final` to postcondition.
/// requires: *v > 0
/// final_values: v -> *v
/// ensures: ^(*v) > 0
/// The binding chain is: v_current_final = final_term = encode(*v) = v_current,
/// and requires says v_current > 0, so v_current_final > 0.
#[test]
#[timeout(30000)]
fn test_precondition_flows_through_current_final() {
    let requires = vec![gt(deref(var("v")), int(0))];

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let ensures = vec![gt(final_expr(deref(var("v"))), int(0))];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "precondition *v > 0 should flow to ^(*v) > 0 through _current_final: got {result:?}"
    );
}

/// Negative companion: without the precondition, ^(*v) > 0 should fail.
#[test]
#[timeout(30000)]
fn test_no_precondition_current_final_unconstrained() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Without requires, *v is unconstrained, so ^(*v) > 0 is not provable.
    let ensures = vec![gt(final_expr(deref(var("v"))), int(0))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without precondition, ^(*v) > 0 should not be provable: got {result:?}"
    );
}

// ── Mutation-continued view bridge (#2124 Phase 5c) ─────────────────────

/// For mutation_continued parameters, the view bridge links
/// `final_{v}_view == final_{v}_current_view` (bindings.rs:199-206).
/// This enables postconditions comparing final views of base and current.
#[test]
#[timeout(30000)]
fn test_mutation_continued_view_bridge() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    // Ghost: constrains the final view
    let ghost = vec![eq(
        view(final_expr(var("v"))),
        view(final_expr(deref(var("v")))),
    )];

    // Postcondition: final view of base == final view of current
    // View(Final(Var("v"))) → final_v_view
    // View(Final(Deref(Var("v")))) → final_v_current_view
    // The Phase 5c bridge asserts final_v_view == final_v_current_view.
    let ensures = vec![eq(
        view(final_expr(var("v"))),
        view(final_expr(deref(var("v")))),
    )];

    let mut mcp = HashSet::new();
    mcp.insert("v".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .ghost_context(Some(&ghost))
            .mutation_continued_params(Some(mcp)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mutation_continued view bridge should link final base and current views: got {result:?}"
    );
}

// ── Cross-reference: old(*v) == *v collapse interaction ─────────────────

/// After `collapse_old_over_mut_ref_currents`, `Old(Deref(Var("v")))` in
/// postconditions collapses to `Deref(Var("v"))` (both map to v_current).
/// This verifies the collapse + binding interaction: the old binding
/// at bindings.rs:64-67 creates `old_v_current = v_current`, but the
/// collapse makes this transparent to postconditions.
#[test]
#[timeout(30000)]
fn test_old_deref_collapse_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // old(*v) == *v — collapse removes Old wrapper for entry-state exprs.
    let ensures = vec![eq(old(deref(var("v"))), deref(var("v")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "old(*v) should equal *v after collapse: got {result:?}"
    );
}

/// Compound case: old(*v) in an arithmetic expression should still collapse.
#[test]
#[timeout(30000)]
fn test_old_deref_in_arithmetic_collapse() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    // ^v == old(*v) + 1, which after collapse is ^v == *v + 1
    let ensures = vec![eq(final_expr(var("v")), add(old(deref(var("v"))), int(1)))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "^v should equal old(*v) + 1 after collapse: got {result:?}"
    );
}

// ── Non-trivial sort inference: multiple fallback tiers ──────────────────

/// When the final expression is a logic function call, `infer_current_sort`
/// falls through the first tier (resolve_var_sort_or_int returns Int for
/// unknown vars) and uses `infer_expr_sort_with_context` at line 117.
#[test]
#[timeout(30000)]
fn test_sort_inference_logic_fn_fallback() {
    let mut final_values = HashMap::new();
    // A logic function call as the final expression — triggers tier 5 fallback
    final_values.insert(
        "v".to_string(),
        PureExpr::LogicFnCall {
            name: "identity".to_string(),
            args: vec![deref(var("v"))],
        },
    );

    let ensures = vec![eq(
        final_expr(var("v")),
        PureExpr::LogicFnCall {
            name: "identity".to_string(),
            args: vec![deref(var("v"))],
        },
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values));

    assert!(
        result.is_ok(),
        "logic function call final expression should not panic: {result:?}"
    );
}

/// When final expression contains `View(Var("v"))`, tier 3 in `infer_current_sort`
/// should resolve through `resolve_view_var_name`.
#[test]
#[timeout(30000)]
fn test_sort_inference_view_var_tier() {
    let mut final_values = HashMap::new();
    // View(Var("v")) triggers resolve_view_var_name at tier 3
    final_values.insert("v".to_string(), view(var("v")));

    let ensures = vec![eq(final_expr(var("v")), view(var("v")))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values));

    assert!(
        result.is_ok(),
        "view-based final expression sort inference should not panic: {result:?}"
    );
}

/// Non-mutation-continued postconditions can directly reference the final view of the
/// current referent (`View(Final(Deref(Var("v"))))`), which should alias the bound
/// `_current_final` scalar value.
#[test]
#[timeout(30000)]
fn test_non_mutation_continued_final_current_view_scalar_alias() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), int(1));

    let ensures = vec![eq(view(final_expr(deref(var("v")))), int(1))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "view(^(*v)) should alias v_current_final on non-mutation-continued scalar bodies: got {result:?}"
    );
}

/// Closure-capture names use dotted `self.N` identifiers. The final-current-view alias
/// path must work for those names too, not only for plain parameter identifiers.
#[test]
#[timeout(30000)]
fn test_non_mutation_continued_final_current_view_scalar_alias_for_dotted_name() {
    let mut final_values = HashMap::new();
    final_values.insert("self.0".to_string(), int(1));

    let ensures = vec![eq(view(final_expr(deref(var("self.0")))), int(1))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "view(^(*self.0)) should alias self.0_current_final for closure-capture names: got {result:?}"
    );
}

/// Newtype field postconditions can reference a field final value directly:
/// `View(Final(Var("x.0")))`. Bind that final-view name to the scalar final
/// value so it does not remain a fresh view placeholder.
#[test]
#[timeout(30000)]
fn test_non_mutation_continued_field_final_view_scalar_alias_for_dotted_name() {
    let mut final_values = HashMap::new();
    final_values.insert("x.0".to_string(), int(5));

    let ensures = vec![eq(view(final_expr(var("x.0"))), int(5))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "view(^x.0) should alias x.0_final for scalar field final values: got {result:?}"
    );
}

/// The bug/486 extractor provides both a whole-newtype final and a field final.
/// The field-level final view must remain strong even when the whole wrapper is
/// also present in the final-values map.
#[test]
#[timeout(30000)]
fn test_field_final_view_alias_with_whole_newtype_final_value() {
    let tuple1 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(1);
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), logic_fn_call(&tuple1, vec![int(5)]));
    final_values.insert("x.0".to_string(), int(5));

    let ensures = vec![eq(view(final_expr(var("x.0"))), int(5))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "view(^x.0) should stay tied to x.0_final when x is also finalized: got {result:?}"
    );
}

// ── Sort bridge gap: view aliasing with sort mismatches ────────────────

/// When the base view variable is predeclared with Int (sort_fallback) but
/// the current_view has a non-Int sort (e.g., Seq from collection inference),
/// the sort bridge should still allow aliasing. Without this, postconditions
/// like `x@ == (*x)@` fail for user-defined types because the sort gate
/// blocks the `base_view == current_view` assertion.
///
/// Re: traits/16_impl_cloning.rs
#[test]
#[timeout(30000)]
fn test_view_alias_bridges_int_to_seq_sort_gap() {
    let mut encoder = AYEncoder::new();

    // Predeclare x_view as Int (simulating sort_fallback from postcondition encoding)
    encoder
        .get_or_declare_var("x_view", ay_dpll::api::Sort::Int)
        .expect("predeclare x_view as Int");

    // Now bind final values where current_sort is Seq
    let x_ref = var_with_sort("x", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(x_ref));

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("binding with sort bridge should succeed");

    // x_view should have been upgraded from Int to the correct sort
    // and aliased to x_current_view
    let x_view = encoder
        .var_term("x_view")
        .expect("x_view should exist after binding");
    let x_current_view = encoder
        .var_term("x_current_view")
        .expect("x_current_view should exist after binding");

    // Negate the finite Seq semantics, not just the native carrier identity.
    assert_semantically_equal(
        &mut encoder,
        x_view,
        x_current_view,
        "x_view must be aliased to x_current_view even when predeclared as Int",
    );
}

/// When both the base view and current view have non-Int sorts from the same
/// structural family (e.g., both are Seq-model types), aliasing should proceed.
#[test]
#[timeout(30000)]
fn test_view_alias_bridges_structural_sort_family() {
    let mut encoder = AYEncoder::new();

    // Predeclare x_view with Seq(Int)
    let seq_sort = ay_dpll::api::Sort::Seq(Box::new(ay_dpll::api::Sort::Int));
    encoder
        .get_or_declare_var("x_view", seq_sort)
        .expect("predeclare x_view as Seq");

    // Bind with a Seq-annotated final expression
    let x_ref = var_with_sort("x", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(x_ref));

    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("binding with same-family sorts should succeed");

    let x_view = encoder
        .var_term("x_view")
        .expect("x_view should exist after binding");
    let x_current_view = encoder
        .var_term("x_current_view")
        .expect("x_current_view should exist after binding");

    assert_semantically_equal(
        &mut encoder,
        x_view,
        x_current_view,
        "x_view must be aliased to x_current_view for same-family sorts",
    );
}

/// The postcondition `x@ == (*x)@` (from 16_impl_cloning.rs) should verify
/// when x is a mut-borrow parameter. This is the end-to-end test for the
/// sort bridge fix.
#[test]
#[timeout(30000)]
fn test_view_base_equals_current_view_identity_body() {
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // Postcondition: x@ == (*x)@  (View(Var("x")) == View(Deref(Var("x"))))
    let ensures = vec![eq(view(var("x")), view(deref(var("x"))))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x@ == (*x)@ should verify for identity-body mut borrows: got {result:?}"
    );
}

// ── Phase 6 advancement vs entry-pinned base view (slices/range vacuity) ──

/// A `&mut [T]` slice parameter collapses to its Seq view: encoding `a@`
/// asserts the definitional identity `a == a_view`, so the bare view symbol
/// denotes the ENTRY state and element-pinning preconditions constrain it
/// directly. When the body writes through the slice (a `.set()` final value),
/// the Phase 6 (#2124) base-view advancement `a_view == final_a_view` would
/// equate the entry state with the post-write state — contradicting the
/// precondition pin (`0 == a@[1]` vs `(^a)@[1] == 1`) and collapsing the base
/// premises to UNSAT, which the vacuity guard then (correctly) demotes.
///
/// With the entry-pinned guard, the advancement is skipped, the premises stay
/// satisfiable, and the postcondition proves through the `.set()` chain:
/// `(^a)@[1] == 1`. Mirrors `slices/range.rs::slice_range_inclusive`.
#[test]
#[timeout(60000)]
fn test_indexed_write_entry_pinned_slice_view_not_vacuous() {
    let a_seq = || var_with_sort("a", ExprSort::Seq);

    // Preconditions pin the ENTRY view elements and length:
    //   a@[0] == 0, a@[1] == 0, a@.len() == 2
    let requires = vec![
        eq(
            method_call(view(a_seq()), "index_logic", vec![int(0)]),
            int(0),
        ),
        eq(
            method_call(view(a_seq()), "index_logic", vec![int(1)]),
            int(0),
        ),
        eq(method_call(view(a_seq()), "len", vec![]), int(2)),
    ];

    // Body writes through the slice: final value is a `.set()` chain.
    let mut final_values = HashMap::new();
    final_values.insert(
        "a".to_string(),
        method_call(view(deref(a_seq())), "set", vec![int(1), int(1)]),
    );

    // Postcondition: (^a)@[1] == 1 — provable from entry state + the write,
    // but only if the premises are not collapsed to UNSAT.
    let ensures = vec![eq(
        method_call(view(final_expr(a_seq())), "index_logic", vec![int(1)]),
        int(1),
    )];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN (strict UNSAT certification gap): the verdict may demote
    // to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "entry-pinned slice with .set() write must verify (not demote to \
         vacuous-unknown via the Phase 6 pre==post collapse): got {result:?}"
    );
}

/// Negative companion: the same entry-pinned write scenario must still REJECT
/// a wrong post-write value — the skipped advancement must not disconnect the
/// entry state from the `.set()` chain.
#[test]
#[timeout(60000)]
fn test_indexed_write_entry_pinned_slice_view_wrong_value_fails() {
    let a_seq = || var_with_sort("a", ExprSort::Seq);

    let requires = vec![
        eq(
            method_call(view(a_seq()), "index_logic", vec![int(0)]),
            int(0),
        ),
        eq(
            method_call(view(a_seq()), "index_logic", vec![int(1)]),
            int(0),
        ),
        eq(method_call(view(a_seq()), "len", vec![]), int(2)),
    ];

    let mut final_values = HashMap::new();
    final_values.insert(
        "a".to_string(),
        method_call(view(deref(a_seq())), "set", vec![int(1), int(1)]),
    );

    // Wrong: the write stored 1, not 2.
    let ensures = vec![eq(
        method_call(view(final_expr(a_seq())), "index_logic", vec![int(1)]),
        int(2),
    )];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong post-write value must be rejected, not accepted or demoted: got {result:?}"
    );
}

// ── view alias at the registered user View sort (mapping_test::incr) ─────

/// A user `impl View for T { type ViewTy = Mapping<Int, Int> }` is not an
/// identity view. `bind_view_aliases` must declare `t_current_view` at the
/// registered `Mapping` view sort, not at the carrier sort `T`; otherwise the
/// later `View(Var(t_current))` encode resolves `Mapping` and dies with a sort
/// conflict.
#[test]
#[timeout(30000)]
fn test_view_alias_declared_at_registered_view_sort_not_carrier_sort() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind, LogicFnDef},
    };

    let mut encoder = AYEncoder::new();
    let t_id = intern_sort_name("T");
    let adt = AdtDecl::new(
        "crate::T".to_string(),
        "T".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "T".to_string(),
            "T".to_string(),
            vec![AdtFieldDecl::new("a".to_string(), ExprSort::Int)],
        )],
    );
    encoder.register_adt_decls(&HashMap::from([("T".to_string(), adt)]));
    let mapping = ExprSort::Datatype(intern_sort_name("Mapping"));
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "crate::<T as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        var("dead"),
    )
    .with_param_sorts(vec![Some(ExprSort::Datatype(t_id))])
    .with_return_sort(Some(mapping.clone()))
    .with_opaque(true);
    encoder
        .register_logic_fn(&view_def)
        .expect("opaque view registration should succeed");

    let carrier_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(t_id));
    let mapping_sort = encoder.sort_from_expr_sort(mapping);
    assert_ne!(carrier_sort, mapping_sort, "test premise: distinct sorts");

    let t_ann = ExprSort::MutRef(Box::new(ExprSort::Datatype(t_id)));
    let final_values = HashMap::from([("t".to_string(), deref(var_with_sort("t", t_ann)))]);
    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("binding final values should succeed");

    assert_eq!(
        encoder.var_sort("t_current_view"),
        Some(&mapping_sort),
        "t_current_view must be declared at the registered View sort, not the carrier sort"
    );
    encoder
        .encode_pure(&view(var_with_sort("t_current", ExprSort::Datatype(t_id))))
        .expect("t_current@ must encode without a sort conflict");
}
