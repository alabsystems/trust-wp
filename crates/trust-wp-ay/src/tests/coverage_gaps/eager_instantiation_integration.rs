// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `assert_eager_negated_existential_instantiations`
//! using a live AYEncoder.
//!
//! These tests exercise the full eager instantiation pipeline:
//! 1. Encode and assert preconditions via AYEncoder
//! 2. Run `assert_eager_negated_existential_instantiations`
//! 3. Check SAT/UNSAT to verify the negated ground clause was asserted
//!
//! Coverage gaps addressed (relative to `eager_instantiation_audit.rs`):
//! - Multi-variable existential binding (`exists<st1, st2, r>`)
//! - Iterative fixpoint resolution in `build_witness_binding` (multi-round)
//! - Incomplete binding early return (distinct unresolvable bound vars)
//! - Deref/Final normalization bridging call-site ↔ ensures expressions
//! - `postcondition_mut` + `resolve` interaction via `extend_binding_with_resolves`
//!
//! Part of #1946 (eager_instantiation.rs integration tests).

use super::*;
use crate::verify::assert_eager_negated_existential_instantiations;

/// Run eager existential instantiation after asserting `requires`, then
/// return the SAT status. Uses `new_pure_with_quantifiers` to avoid heap
/// array declarations that are irrelevant to pure expression matching.
fn run_eager_sat(ensures: &[PureExpr], requires: &[PureExpr]) -> ay_dpll::api::SolveResult {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    for req in requires {
        let t = encoder
            .encode_pure(req)
            .expect("encode_pure failed for requires");
        encoder.assert_term(t);
    }
    let result =
        assert_eager_negated_existential_instantiations(&mut encoder, ensures, requires, &[]);
    assert!(
        result.is_ok(),
        "eager instantiation should not error, got: {result:?}"
    );
    encoder.check_sat()
}

/// Helper: build `exists<v1> exists<v2> ... body` from a list of var names.
fn nested_exists(vars: &[&str], body: PureExpr) -> PureExpr {
    vars.iter().rev().fold(body, |acc, v| exists(v, acc))
}

/// Helper: `receiver.postcondition_mut(args...)`
fn postcondition_mut(receiver: PureExpr, args: Vec<PureExpr>) -> PureExpr {
    method_call(receiver, "postcondition_mut", args)
}

// ── Multi-variable existential binding ──────────────────────────────

/// The canonical use case from the function docstring:
/// `exists<st1, st2, r> A(st1, r) && B(st1, st2) && C(st2)`
/// with matching ground calls for all three variables.
///
/// This tests the multi-variable flattening path in `flatten_nested_existentials`
/// and the multi-call matching in `build_witness_binding`.
#[test]
#[timeout(30000)]
fn multi_var_existential_all_bound() {
    // Body: st1.postcondition_mut(r) && st1.postcondition_mut(st2)
    // This lets both calls contribute to binding different variables.
    let body = and(
        postcondition_mut(var("st1"), vec![var("r")]),
        postcondition_mut(var("st1"), vec![var("st2")]),
    );
    let ensures = vec![nested_exists(&["st1", "st2", "r"], body)];

    // Ground calls that provide witnesses: f.postcondition_mut(result), f.postcondition_mut(g)
    let requires = vec![
        postcondition_mut(var("f"), vec![var("result")]),
        postcondition_mut(var("f"), vec![var("g")]),
    ];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "multi-var existential with full ground witnesses should produce Unsat, got: {result:?}"
    );
}

/// Two bound variables where one ground call binds both at once
/// (receiver and arg are both bound variables).
#[test]
#[timeout(30000)]
fn multi_var_existential_single_call_binds_two() {
    // Body: st.postcondition_mut(r)  -- both st and r are bound
    let body = postcondition_mut(var("st"), vec![var("r")]);
    let ensures = vec![nested_exists(&["st", "r"], body)];

    // Single ground call binds both: f.postcondition_mut(result)
    let requires = vec![postcondition_mut(var("f"), vec![var("result")])];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "single ground call binding two vars should produce Unsat, got: {result:?}"
    );
}

// ── Iterative fixpoint resolution ───────────────────────────────────

/// Tests the `while progress` loop in `build_witness_binding` requiring
/// multiple rounds. Round 1 binds `st1` from one ground call; round 2
/// uses that binding to match a second ground call that binds `st2`.
///
/// Setup:
/// - Body call A: `f.postcondition_mut(st1)` — `f` is free, `st1` is bound
/// - Body call B: `st1.postcondition_mut(st2)` — `st1` is bound (receiver), `st2` is bound
/// - Ground call 1: `f.postcondition_mut(g)` — matches A, binds st1 -> g
/// - Ground call 2: `g.postcondition_mut(h)` — matches B only AFTER st1 is bound to g
///
/// Without the fixpoint loop, call B wouldn't match in round 1 because st1
/// is unresolved as a receiver. Round 2 resolves it.
#[test]
#[timeout(30000)]
fn iterative_fixpoint_two_rounds() {
    let body = and(
        postcondition_mut(var("f"), vec![var("st1")]),
        postcondition_mut(var("st1"), vec![var("st2")]),
    );
    let ensures = vec![nested_exists(&["st1", "st2"], body)];

    let requires = vec![
        postcondition_mut(var("f"), vec![var("g")]),
        postcondition_mut(var("g"), vec![var("h")]),
    ];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "fixpoint requiring two rounds should produce Unsat, got: {result:?}"
    );
}

/// Three-round fixpoint: each round unlocks the next matching.
/// st1 -> g (round 1), st2 -> h (round 2), st3 -> k (round 3).
#[test]
#[timeout(30000)]
fn iterative_fixpoint_three_rounds() {
    let body = and(
        and(
            postcondition_mut(var("f"), vec![var("st1")]),
            postcondition_mut(var("st1"), vec![var("st2")]),
        ),
        postcondition_mut(var("st2"), vec![var("st3")]),
    );
    let ensures = vec![nested_exists(&["st1", "st2", "st3"], body)];

    let requires = vec![
        postcondition_mut(var("f"), vec![var("g")]),
        postcondition_mut(var("g"), vec![var("h")]),
        postcondition_mut(var("h"), vec![var("k")]),
    ];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "three-round fixpoint should produce Unsat, got: {result:?}"
    );
}

// ── Incomplete binding early return ─────────────────────────────────

/// When preconditions don't provide enough ground calls to bind all
/// existential variables, the function returns Ok(()) without asserting
/// the negated clause. The solver remains Sat.
#[test]
#[timeout(30000)]
fn incomplete_binding_leaves_sat() {
    // Body: st.postcondition_mut(r) && r > 0
    // Both st and r are bound, but we only provide a ground call that binds st.
    // r has no ground witness, so the binding is incomplete.
    let body = and(
        postcondition_mut(var("st"), vec![var("result")]),
        gt(var("r"), int(0)),
    );
    let ensures = vec![nested_exists(&["st", "r"], body)];

    // Only one ground call: binds st but NOT r (r appears in a pure expression, not a call)
    let requires = vec![postcondition_mut(var("f"), vec![var("result")])];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_sat(),
        "incomplete binding (missing r) should leave solver Sat, got: {result:?}"
    );
}

/// Incomplete binding: two bound variables, zero matching ground calls.
#[test]
#[timeout(30000)]
fn incomplete_binding_no_ground_calls_sat() {
    let body = postcondition_mut(var("st"), vec![var("r")]);
    let ensures = vec![nested_exists(&["st", "r"], body)];

    // Requires has a postcondition_mut call but with a different method name
    let requires = vec![method_call(var("f"), "precondition", vec![var("s")])];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_sat(),
        "no matching ground postcondition_mut calls should leave solver Sat, got: {result:?}"
    );
}

// ── Deref/Final normalization bridging ──────────────────────────────

/// Tests the normalization pipeline that bridges call-site expressions
/// (using Deref/Final wrappers from MIR's *self/^self) with ensures body
/// expressions (using bare variables).
///
/// Precondition pattern: `Deref(f).postcondition_mut(Final(f))`
/// Body pattern: `st.postcondition_mut(st_final)`
///
/// After normalization:
/// - Deref(f) → f (by-value dereference identity)
/// - Final(f) → f_final
/// So the ground call becomes: f.postcondition_mut(f_final)
/// And the body matches: st → f, st_final → f_final
#[test]
#[timeout(30000)]
fn deref_final_normalization_bridges_callsite_to_body() {
    // Body uses bare variables (as the ensures clause would)
    let body = postcondition_mut(var("st"), vec![var("st_final")]);
    let ensures = vec![nested_exists(&["st", "st_final"], body)];

    // Requires uses Deref/Final wrappers (as MIR-lowered call-site assumptions would)
    let requires = vec![postcondition_mut(
        deref(var("f")),
        vec![final_expr(var("f"))],
    )];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "Deref/Final normalization should bridge call-site to body, got: {result:?}"
    );
}

/// Deref/Final on receiver AND arg: both must be normalized for matching.
/// Tests that normalization recurses into both receiver and args of the
/// ground postcondition_mut call.
///
/// Precondition: `Deref(f).postcondition_mut(Deref(g))`
/// After normalization: `f.postcondition_mut(g)` (both Deref stripped)
/// Body matches: st → f, st2 → g
#[test]
#[timeout(30000)]
fn deref_final_normalization_receiver_and_args() {
    // Body: st.postcondition_mut(st2) — bare variables
    let body = postcondition_mut(var("st"), vec![var("st2")]);
    let ensures = vec![nested_exists(&["st", "st2"], body)];

    // Requires: Deref(f).postcondition_mut(Deref(g))
    // Both receiver and arg have Deref wrappers from MIR lowering.
    // Normalization strips both, making them match the body pattern.
    // The precondition also has a bare-variable form that the SMT solver
    // can use to verify the negated instantiation.
    let requires = vec![
        postcondition_mut(deref(var("f")), vec![deref(var("g"))]),
        postcondition_mut(var("f"), vec![var("g")]),
    ];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "Deref normalization on receiver+args should produce Unsat, got: {result:?}"
    );
}

// ── postcondition_mut + resolve interaction ──────────────────────────

/// Tests the full interaction between postcondition_mut matching and resolve
/// matching via `extend_binding_with_resolves`. The postcondition_mut call
/// binds some variables, and a resolve() call in the body needs to bind
/// additional variables from ground resolve() calls in preconditions.
///
/// This is the by-value FnMut consumption pattern: the terminal state
/// resolves because Rust ownership transfers at function exit.
#[test]
#[timeout(30000)]
fn postcondition_mut_plus_resolve_binds_all_vars() {
    // Body: st.postcondition_mut(r) && resolve(st2) && st2 == st
    // st is bound by postcondition_mut, st2 is bound by resolve matching
    let body = and(
        and(
            postcondition_mut(var("st"), vec![var("r")]),
            resolve_call(var("st2")),
        ),
        eq(var("st2"), var("st")),
    );
    let ensures = vec![nested_exists(&["st", "r", "st2"], body)];

    // Requires: f.postcondition_mut(result) + resolve(f)
    // postcondition_mut binds st -> f, r -> result
    // resolve(f) matches resolve(st2), binding st2 -> f
    let requires = vec![
        postcondition_mut(var("f"), vec![var("result")]),
        resolve_call(value_state("f")),
    ];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "postcondition_mut + resolve cooperation should produce Unsat, got: {result:?}"
    );
}

/// When resolve ground calls are under a quantifier, they should NOT be
/// collected as ground witnesses (they are not ground).
#[test]
#[timeout(30000)]
fn resolve_under_quantifier_excluded_from_ground() {
    // Body: st.postcondition_mut(r) && resolve(st2)
    let body = and(
        postcondition_mut(var("st"), vec![var("r")]),
        resolve_call(var("st2")),
    );
    let ensures = vec![nested_exists(&["st", "r", "st2"], body)];

    // Ground postcondition_mut exists, but resolve is under a forall (not
    // ground). The binder is a value: an unannotated one may range over
    // borrows, and its resolve is refused (D-127).
    let requires = vec![
        postcondition_mut(var("f"), vec![var("result")]),
        forall_with_sort(
            "x",
            trust_wp_core::formula::ExprSort::Int,
            resolve_call(var_with_sort("x", trust_wp_core::formula::ExprSort::Int)),
        ),
    ];

    // st and r are bound by postcondition_mut, but st2 has no ground resolve
    // witness → incomplete binding → Sat
    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_sat(),
        "quantified resolve should not be collected as ground witness, got: {result:?}"
    );
}

// ── Edge cases ──────────────────────────────────────────────────────

/// Triggered existential stops flattening — eager instantiation should not
/// fire for existentials with user-provided triggers (E-matching handles those).
#[test]
#[timeout(30000)]
fn triggered_existential_skipped() {
    // exists<st, triggers=[st]> st.postcondition_mut(result)
    let ensures = vec![exists_with_triggers(
        "st",
        postcondition_mut(var("st"), vec![var("result")]),
        vec![vec![var("st")]],
    )];
    let requires = vec![postcondition_mut(var("f"), vec![var("result")])];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_sat(),
        "triggered existential should be skipped by eager instantiation, got: {result:?}"
    );
}

/// Body without postcondition_mut call is skipped even if it has existentials.
/// This tests the `body_has_postcondition_mut_method_call` guard.
#[test]
#[timeout(30000)]
fn existential_without_postcondition_mut_skipped() {
    // exists<x> x > 0  — no postcondition_mut call in body
    let ensures = vec![exists("x", gt(var("x"), int(0)))];
    let requires = vec![postcondition_mut(var("f"), vec![var("result")])];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_sat(),
        "existential without postcondition_mut should be skipped, got: {result:?}"
    );
}

/// Multiple ensures clauses: only the ones with postcondition_mut existentials
/// trigger eager instantiation.
#[test]
#[timeout(30000)]
fn multiple_ensures_selective_instantiation() {
    let ensures = vec![
        // Non-existential — skipped
        gt(var("result"), int(0)),
        // Existential with postcondition_mut — triggers
        nested_exists(&["st"], postcondition_mut(var("st"), vec![var("result")])),
        // Existential without postcondition_mut — skipped
        exists("x", gt(var("x"), int(0))),
    ];
    let requires = vec![postcondition_mut(var("f"), vec![var("result")])];

    let result = run_eager_sat(&ensures, &requires);
    assert!(
        result.is_unsat(),
        "selective instantiation should still produce Unsat for matching clause, got: {result:?}"
    );
}
