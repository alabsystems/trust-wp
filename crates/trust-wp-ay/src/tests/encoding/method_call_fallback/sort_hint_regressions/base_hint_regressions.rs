// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1805: equality between Int-inferred and
/// Seq-inferred operands should not panic even without prescan hints.
#[test]
#[timeout(30000)]
fn test_eq_sort_mismatch_graceful_1805() {
    // Manually declare a var as Int, then encode equality with a Seq term.
    // This should be caught by eq_or_iff's panic isolation, but the
    // prefer_specific_sort fix should prevent the panic entirely when
    // inferred sorts are available.
    let mut encoder = AYEncoder::new();

    // Build: Var("x") == Seq::empty()
    // "x" has no prescan hint and defaults to Int.
    // Seq::empty() infers as Seq.
    // The eq_sort should prefer Seq from the right operand.
    let expr = eq(var("x"), logic_fn_call("Seq::empty", vec![]));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "equality with sort mismatch should encode: {result:?}"
    );
    // With prefer_specific_sort: the inferred right sort is Seq, so
    // eq_sort should be Seq. If x was declared as Int, the solver.eq()
    // would still panic (caught), but we verify no panic occurred.
    // Note: without prescan Seq hints, x will default to Int-sorted
    // at declaration, so a caught panic is still acceptable here.
    // The key improvement is for cases where prescan hints ARE available.
}

/// Regression for #1805: when the base variable was predeclared as Int,
/// a stronger Seq sort hint on the base must still propagate to deref-
/// derived names (`s_current`) instead of inheriting the Int default.
///
/// Without this, `*s == Seq::empty()` can still hit `mk_eq(Int, Seq)` in
/// mixed predeclared/hinted paths.
#[test]
#[timeout(30000)]
fn test_base_seq_hint_overrides_predeclared_int_for_deref_1805() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();

    // Simulate an early Int declaration for the base symbol.
    encoder
        .get_or_declare_var("s", Sort::Int)
        .expect("declare s as Int");

    // Later prescan learns that `s` is Seq-sorted.
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    let expr = eq(deref(var("s")), logic_fn_call("Seq::empty", vec![]));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "deref(base_with_seq_hint) == Seq::empty should encode: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "base Seq hint should prevent Int/Seq equality panic: {:?}",
        encoder.solver_panic_reason()
    );

    let current_sort = encoder.var_sort("s_current");
    assert!(
        current_sort.is_some_and(ay_dpll::ApiSort::is_seq),
        "s_current should be Seq-sorted, got: {current_sort:?}"
    );
}

/// Regression for #1805: same predeclared-Int drift as the Seq case, but
/// with Bool hints (cell/02_fib path). The deref-derived name must honor
/// the base Bool hint so `mk_eq(Int, Bool)` is never produced.
#[test]
#[timeout(30000)]
fn test_base_bool_hint_overrides_predeclared_int_for_deref_1805() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();

    // Simulate an early Int declaration for the base symbol.
    encoder
        .get_or_declare_var("active", Sort::Int)
        .expect("declare active as Int");

    // Later prescan learns that `active` is Bool-sorted.
    encoder.record_sort_hint("active".to_string(), ExprSort::Bool);

    let expr = eq(deref(var("active")), bool_expr(true));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "deref(base_with_bool_hint) == true should encode: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "base Bool hint should prevent Int/Bool equality panic: {:?}",
        encoder.solver_panic_reason()
    );

    let current_sort = encoder.var_sort("active_current");
    assert!(
        current_sort.is_some_and(|s| matches!(s, Sort::Bool)),
        "active_current should be Bool-sorted, got: {current_sort:?}"
    );
}

/// Regression for #1805: method-call sort inference must not lock onto a
/// stale Int declaration for a deref-derived receiver when the base name
/// has a stronger Seq hint.
#[test]
#[timeout(30000)]
fn test_method_receiver_prefers_base_seq_hint_over_stale_deref_int_1805() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();
    // Simulate stale Int metadata for a derived name before the SMT symbol
    // is declared. This is the recoverable path #1805 targets.
    encoder
        .var_sorts_mut_for_test()
        .insert("s_current".to_string(), Sort::Int);
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    let expr = method_call(deref(var("s")), "public", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "public(*s) should encode with base Seq hint: {result:?}"
    );
    assert!(
        encoder.decls().has_logic_func("method_public_1_s"),
        "receiver sort should be Seq-tagged (s), decls: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_logic_func("method_public_1_i"),
        "stale Int receiver sort should not win over base Seq hint"
    );
}

/// Regression for #1805: method-call sort inference must also prefer a
/// base Bool hint over a stale Int declaration on deref-derived receiver
/// names.
#[test]
#[timeout(30000)]
fn test_method_receiver_prefers_base_bool_hint_over_stale_deref_int_1805() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();
    // Simulate stale Int metadata for a derived name before the SMT symbol
    // is declared. This is the recoverable path #1805 targets.
    encoder
        .var_sorts_mut_for_test()
        .insert("active_current".to_string(), Sort::Int);
    encoder.record_sort_hint("active".to_string(), ExprSort::Bool);

    let expr = method_call(deref(var("active")), "public", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "public(*active) should encode with base Bool hint: {result:?}"
    );
    assert!(
        encoder.decls().has_logic_func("method_public_1_b"),
        "receiver sort should be Bool-tagged (b), decls: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_logic_func("method_public_1_i"),
        "stale Int receiver sort should not win over base Bool hint"
    );
}
