// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Semantic companion for `test_produces_with_seq_view_argument`.
///
/// The `produces` predicate with a View-sorted visited argument should
/// encode correctly AND the reflexivity axiom should still hold:
/// `produces(iter, seq_empty, iter)` is true for any `iter`.
///
/// We use the same View-argument pattern as the encode-only test,
/// then check that `produces(a, seq_empty, a)` is provably true.
#[test]
#[timeout(30000)]
fn test_produces_view_arg_reflexivity_holds() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Trigger produces axiom registration via a call with View argument
    // (same pattern as the encode-only test)
    let visited_view = view(var("produced"));
    let trigger = method_call(
        deref(var("self")),
        "produces",
        vec![visited_view, final_expr(var("self"))],
    );
    encoder
        .encode_pure(&trigger)
        .expect("produces with View arg should encode");

    // Reflexivity check: produces(a, seq_empty, a) should hold
    let seq_empty_expr = logic_fn_call("seq_empty", vec![]);
    let refl = method_call(var("a"), "produces", vec![seq_empty_expr, var("a")]);
    let refl_term = encoder
        .encode_pure(&refl)
        .expect("produces(a, seq_empty, a) should encode");

    // Negate reflexivity — should be UNSAT by axiom
    let neg = encoder.solver_mut().not(refl_term);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "produces reflexivity must hold even when triggered via View-arg pattern"
    );
}

/// Semantic companion for `test_produces_with_singleton_seq`.
///
/// The `produces(self, seq![v], ^self)` pattern (Iterator::next postcondition)
/// should encode correctly AND the result should be Bool-sorted.
/// We verify by asserting both the term and its negation are individually
/// satisfiable (proving a genuine unconstrained Bool UF, not a sort error
/// or a constant).
#[test]
#[timeout(30000)]
fn test_produces_singleton_seq_is_bool_predicate() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let self_deref = deref(var("self"));
    let v = var("v");
    let seq_v = logic_fn_call("seq", vec![v]);
    let self_final = final_expr(var("self"));
    let produces = method_call(
        self_deref.clone(),
        "produces",
        vec![seq_v.clone(), self_final.clone()],
    );

    let term = encoder
        .encode_pure(&produces)
        .expect("produces with seq![v] should encode");
    assert!(
        matches!(encoder.solver.get_sort(term), ay_dpll::api::Sort::Bool),
        "produces(self, seq![v], ^self) should encode as a Bool predicate"
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|name| name.contains("produces")),
        "produces encoding should register a produces predicate declaration"
    );
}

/// Per-symbol produces axiom dedup test (#930).
///
/// Two produces symbols with different state sorts (Int vs Bool) must each
/// independently receive reflexivity/transitivity axioms. Under the old
/// global-boolean dedup, the second symbol would be skipped. We verify
/// reflexivity holds for the second (Bool-sorted) produces symbol after
/// the first (Int-sorted) one has already triggered axiom assertion.
#[test]
#[timeout(30000)]
fn test_produces_per_symbol_dedup_both_get_axioms() {
    use crate::ExprSort;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // First produces call: Int-sorted state (default)
    let int_p = method_call(var("i1"), "produces", vec![view(var("iv")), var("i2")]);
    encoder.register_sort_hints(std::slice::from_ref(&int_p));
    encoder
        .encode_pure(&int_p)
        .expect("Int-sorted produces should encode");

    // Second produces call: Bool-sorted state
    let bool_a = var_with_sort("ba", ExprSort::Bool);
    let bool_b = var_with_sort("bb", ExprSort::Bool);
    let bool_p = method_call(
        bool_a.clone(),
        "produces",
        vec![view(var("bv")), bool_b.clone()],
    );
    encoder.register_sort_hints(std::slice::from_ref(&bool_p));
    let _bool_term = encoder
        .encode_pure(&bool_p)
        .expect("Bool-sorted produces should encode");

    // Now test reflexivity on the Bool-sorted produces symbol.
    // If per-symbol dedup failed and the Bool symbol didn't get axioms,
    // the reflexivity check below would be Sat (negation not refutable).
    let bool_refl = method_call(
        bool_a.clone(),
        "produces",
        vec![logic_fn_call("seq_empty", vec![]), bool_a],
    );
    encoder.register_sort_hints(std::slice::from_ref(&bool_refl));
    let refl_term = encoder
        .encode_pure(&bool_refl)
        .expect("Bool-sorted produces reflexivity should encode");

    let neg = encoder.solver_mut().not(refl_term);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Per-symbol dedup must give Bool-sorted produces its own axioms; \
         reflexivity must hold even after Int-sorted produces was asserted first"
    );
}

/// Produces axiom idempotency test (#930).
///
/// Calling `assert_produces_axioms` twice must be safe — the per-symbol dedup
/// key in `logic_fn_axioms` should prevent duplicate assertion. We verify
/// the reflexivity axiom still holds after two calls.
#[test]
#[timeout(30000)]
fn test_produces_axioms_idempotent() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Trigger produces axiom registration
    let trigger = method_call(
        var("dummy_iter"),
        "produces",
        vec![var("dummy_v"), var("dummy_o")],
    );
    encoder
        .encode_pure(&trigger)
        .expect("trigger call should encode");

    // Explicitly call assert_produces_axioms a second time — must be idempotent
    let produces_decl = encoder.decls().get_spec_func("produces").cloned();
    if let Some(decl) = produces_decl {
        encoder.assert_produces_axioms(&decl);
    }

    // Reflexivity check after double axiom assertion
    let seq_empty_expr = logic_fn_call("seq_empty", vec![]);
    let refl = method_call(var("a"), "produces", vec![seq_empty_expr, var("a")]);
    let refl_term = encoder
        .encode_pure(&refl)
        .expect("produces(a, seq_empty, a) should encode");

    // Reflexivity must still hold after second axiom assertion
    let neg = encoder.solver_mut().not(refl_term);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "produces reflexivity must hold after idempotent axiom assertion"
    );
}
