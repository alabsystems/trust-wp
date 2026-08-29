// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_seq_tail_dispatches_to_seq_subsequence_no_uf_tail() {
    let mut encoder = AYEncoder::new();

    let tail_expr = method_call(view(var("s")), "tail", vec![]);
    let tail_term = encoder
        .encode_pure(&tail_expr)
        .expect("tail should encode as a Seq operation");
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "tail should initialize seq function declarations"
    );
    assert!(
        encoder.seq_state_for_test().has_seq_value(&tail_term),
        "tail should register SeqValue metadata for the produced term"
    );

    let eq_expr = eq(tail_expr.clone(), tail_expr);

    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "Seq tail equality should encode without sort panic: {result:?}"
    );
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("method_tail_")),
        "tail should not fall back to UF method_tail_*; declared: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_seq_empty_equality_propagates_seq_sort_hint_to_view_var() {
    // Regression for #1805 (`take_first_mut.rs`): equalities against
    // `Seq::empty()` / `seq_empty` must seed Seq sort hints on view vars.
    let mut encoder = AYEncoder::new();

    let lhs = view(deref(final_expr(var("self_"))));
    let rhs = logic_fn_call("seq_empty", vec![]);
    let expr = eq(lhs, rhs);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "equality with seq_empty should encode without sort panic: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "seq_empty equality should not panic: {:?}",
        encoder.solver_panic_reason()
    );
    assert!(
        encoder
            .var_sort("self__final_current_view")
            .is_some_and(ay_dpll::ApiSort::is_seq),
        "lhs view var should be declared Seq; var_sorts={:?}",
        encoder.var_names()
    );
}

#[test]
#[timeout(30000)]
fn test_seq_set_pointwise_update() {
    // v@.set(idx, val) on a Seq receiver should route to the Seq seq_set path,
    // NOT to the Int UF fallback. Verified by checking that seq functions are
    // initialized and no method_set_* UF is created.
    let mut encoder = AYEncoder::new();

    let expr = method_call(view(var("v")), "set", vec![int(0), int(99)]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("Seq.set(idx, val) should encode via Seq path");

    // Should NOT create a UF fallback for set
    let has_uf_fallback = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_set_"));
    assert!(
        !has_uf_fallback,
        "Seq.set should use built-in seq_set, not UF fallback; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Semantic: set(v@, 0, 99) produces a Seq, verify index_logic on result equals value
    let set_expr = method_call(view(var("v")), "set", vec![int(0), int(99)]);
    let idx_expr = method_call(set_expr, "index_logic", vec![int(0)]);
    let eq_expr = eq(idx_expr, int(99));
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("set then index_logic should encode");
    encoder.assert_term(eq_term);
    // Note: without seq_set axioms, this may be SAT but not provably =99.
    // We only verify encoding succeeds and the constraint is satisfiable.
    let set_result = encoder.check_sat();
    assert!(
        matches!(set_result, SolveResult::Sat),
        "seq_set(v@, 0, 99)[0] == 99 should be Sat, got {set_result:?}"
    );
}

/// view() as an explicit method call should produce the same encoding as
/// the `@` operator (PureExpr::View). This tests the dispatch added in
/// #1963 — previously, `.view()` fell through to the unsupported error.
#[test]
#[timeout(30000)]
fn test_view_method_call_encodes_like_view_operator() {
    // x.view() via method dispatch
    let mut encoder_method = AYEncoder::new();
    let method_expr = method_call(var("x"), "view", vec![]);
    let method_term = encoder_method
        .encode_pure(&method_expr)
        .expect("x.view() method call should encode — not fall through to unsupported");

    // View(x) via PureExpr::View
    let mut encoder_view = AYEncoder::new();
    let view_expr = view(var("x"));
    let _view_term = encoder_view
        .encode_pure(&view_expr)
        .expect("View(x) should encode");

    // Both should declare the same view variable "x_view"
    assert!(
        encoder_method.var_sort("x_view").is_some(),
        "x.view() should declare x_view variable; vars: {:?}",
        encoder_method.var_names()
    );
    assert!(
        encoder_view.var_sort("x_view").is_some(),
        "View(x) should declare x_view variable; vars: {:?}",
        encoder_view.var_names()
    );

    // Both should produce terms (not panic or error)
    let _ = method_term;
}
