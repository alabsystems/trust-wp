// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// collect_formula_sort_hints tests via register_formula_body_sort_hints (#592)
// =============================================================================

/// `Formula::Pure(Not(var))` should mark the variable as Bool.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_pure_not_var() {
    let mut encoder = AYEncoder::new();
    let formula = pure(not(var("p")));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("p"),
        "Variable in Formula::Pure(Not(p)) should get Bool hint"
    );
}

/// `Formula::And` should recurse into both children.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_and_recurse() {
    let mut encoder = AYEncoder::new();
    let formula = formula_and(pure(not(var("p"))), pure(var("q")));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("p"),
        "Left child of Formula::And should be visited"
    );
    assert!(
        encoder.is_bool_var("q"),
        "Right child of Formula::And should be visited"
    );
}

/// `Formula::Or` should recurse into both children.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_or_recurse() {
    let mut encoder = AYEncoder::new();
    let formula = formula_or(pure(var("a")), pure(not(var("b"))));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("a"),
        "Left child of Formula::Or should be visited"
    );
    assert!(
        encoder.is_bool_var("b"),
        "Right child of Formula::Or should be visited"
    );
}

/// `Formula::Implies` should recurse into both children.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_implies_recurse() {
    let mut encoder = AYEncoder::new();
    let formula = formula_implies(pure(var("ante")), pure(var("cons")));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("ante"),
        "Antecedent of Implies should be visited"
    );
    assert!(
        encoder.is_bool_var("cons"),
        "Consequent of Implies should be visited"
    );
}

/// `Formula::SepConj` should recurse into both children.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_sep_conj_recurse() {
    let mut encoder = AYEncoder::new();
    let formula = sep_conj(pure(var("lhs")), pure(not(var("rhs"))));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("lhs"),
        "Left child of SepConj should be visited"
    );
    assert!(
        encoder.is_bool_var("rhs"),
        "Right child of SepConj should be visited"
    );
}

/// `Formula::MagicWand` should recurse into both children.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_magic_wand_recurse() {
    let mut encoder = AYEncoder::new();
    let formula = magic_wand(pure(var("guard")), pure(var("body")));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("guard"),
        "Guard of MagicWand should be visited"
    );
    assert!(
        encoder.is_bool_var("body"),
        "Body of MagicWand should be visited"
    );
}

/// `Formula::Forall` should recurse into body.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_forall_body() {
    let mut encoder = AYEncoder::new();
    let formula = formula_forall("x", pure(not(var("flag"))));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("flag"),
        "Body of Forall should be visited"
    );
}

/// `Formula::Exists` should recurse into body.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_exists_body() {
    let mut encoder = AYEncoder::new();
    let formula = formula_exists("x", pure(var("pred")));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        encoder.is_bool_var("pred"),
        "Body of Exists should be visited"
    );
}

/// `Formula::True`, `Formula::False` should be no-ops (no hints added).
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_true_false_noop() {
    let mut encoder = AYEncoder::new();
    encoder.register_formula_body_sort_hints(&Formula::True);
    encoder.register_formula_body_sort_hints(&Formula::False);
    assert!(
        !encoder.is_bool_var("anything"),
        "True/False should not produce sort hints"
    );
}

/// `Formula::PointsTo` should be a no-op (location/value are not Bool context).
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_points_to_noop() {
    let mut encoder = AYEncoder::new();
    let formula = points_to("loc", var("val"));
    encoder.register_formula_body_sort_hints(&formula);
    assert!(
        !encoder.is_bool_var("val"),
        "PointsTo value should not get Bool hint"
    );
    assert!(
        !encoder.is_bool_var("loc"),
        "PointsTo location should not get Bool hint"
    );
}

/// Logic function names in Bool context should get Bool hints through
/// the formula walker.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_logic_fn_in_bool_context() {
    let mut encoder = AYEncoder::new();
    let call = logic_fn_call("is_valid", vec![]);
    let formula = pure(not(call));
    encoder.register_formula_body_sort_hints(&formula);
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("is_valid");
    assert!(
        encoder.is_bool_var(&smt_name),
        "Logic fn in Bool context should get Bool hint via formula walker"
    );
}

/// Bare method calls asserted as formulas should mark the method name as Bool,
/// so ambiguous fallback UFs do not default to Int in `requires`.
/// The hint key is receiver-qualified (#2245): "cell.index_logic" not "index_logic".
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_top_level_method_call_marks_method_bool_2316() {
    let mut encoder = AYEncoder::new();
    let call = method_call(view(var("cell")), "index_logic", vec![var("k")]);
    encoder.register_formula_sort_hints(std::slice::from_ref(&call));
    assert_eq!(
        encoder
            .sort_resolver_for_test()
            .get_sort_hint("cell.index_logic"),
        Some(&trust_wp_core::formula::ExprSort::Bool),
        "top-level formula method call should mark cell.index_logic as Bool"
    );
}

/// Nested formulas: And(Or(Pure(p), Pure(q)), Implies(Pure(r), Pure(s)))
/// should visit all four variables.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_nested_connectives() {
    let mut encoder = AYEncoder::new();
    let formula = formula_and(
        formula_or(pure(var("p")), pure(var("q"))),
        formula_implies(pure(var("r")), pure(var("s"))),
    );
    encoder.register_formula_body_sort_hints(&formula);
    for name in &["p", "q", "r", "s"] {
        assert!(
            encoder.is_bool_var(name),
            "Variable {name} should get Bool hint from nested connectives"
        );
    }
}

/// Formula-level quantifier body with a Seq method call (`push_back`) should
/// collect Seq hint for the view-derived variable name. Before #1805, formula
/// hint collection only gathered Bool hints, causing bound variables used in
/// Seq method calls to default to Sort::Int and produce mk_eq sort mismatches.
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_seq_method_call_in_body_1805() {
    let mut encoder = AYEncoder::new();
    // forall s. Pure(view(deref(s)).push_back(42) == view(deref(s)))
    // The `push_back` is a Seq-only method, so the view-derived name for
    // `view(deref(var("s")))` — which resolves to "s_current_view" — should
    // get a Seq hint.
    let receiver = view(deref(var("s")));
    let push = method_call(receiver, "push_back", vec![int(42)]);
    let body = pure(binop(push, BinOp::Eq, view(deref(var("s")))));
    let formula = formula_forall("s", body);
    encoder.register_formula_body_sort_hints(&formula);
    // resolve_view_var_name(view(deref(var("s")))) = "s_current_view"
    let view_sort = encoder.resolve_var_sort("s_current_view");
    assert!(
        matches!(view_sort, Some(ref s) if s.is_seq()),
        "push_back receiver in formula body should produce Seq hint for \
         s_current_view (got: {view_sort:?})"
    );
}

/// Formula-level quantifier body with equality against a Seq-producing
/// expression should collect Seq hint for the view variable. (#1805)
#[test]
#[timeout(30000)]
fn test_formula_sort_hints_seq_equality_in_body_1805() {
    let mut encoder = AYEncoder::new();
    // exists s. Pure(view(deref(s)) == view(deref(dummy)).push_back(0))
    // push_back on the RHS produces Seq, which should propagate the Seq
    // hint to the LHS via equality hint collection.
    let lhs = view(deref(var("s")));
    let rhs = method_call(view(deref(var("dummy"))), "push_back", vec![int(0)]);
    let body = pure(binop(lhs, BinOp::Eq, rhs));
    let formula = formula_exists("s", body);
    encoder.register_formula_body_sort_hints(&formula);
    // RHS view-derived name gets Seq from push_back method
    let rhs_sort = encoder.resolve_var_sort("dummy_current_view");
    assert!(
        matches!(rhs_sort, Some(ref s) if s.is_seq()),
        "push_back receiver in formula RHS should produce Seq hint (got: {rhs_sort:?})"
    );
    // LHS should NOT be Bool (it's in an equality with a Seq expression)
    assert!(
        !encoder.is_bool_var("s"),
        "Seq-context variable should not get Bool hint"
    );
}

// =============================================================================
// reconcile_eq_sort_hints tests (#585)
// =============================================================================

/// When a LogicFnCall appears in equality with an Int expression, a stale
/// Bool hint for that function should be cleared to prevent mk_eq(Bool, Int)
/// panics. This tests the scenario from #585.
#[test]
#[timeout(30000)]
fn test_reconcile_eq_clears_stale_bool_hint() {
    let mut encoder = AYEncoder::new();

    // Pre-condition: register a Bool hint for logic function "f"
    // by encoding it in a Bool context (e.g., if f(x) then ...)
    let f_call = logic_fn_call("f", vec![var("x")]);
    let bool_ctx = ite(f_call.clone(), int(1), int(0));
    // register_sort_hints scans for Bool contexts
    encoder.register_sort_hints(&[bool_ctx]);

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("f");
    assert!(
        encoder.is_bool_var(&smt_name),
        "f should have Bool hint after Ite-condition context"
    );

    // Now encode f(x) == 42 — this triggers reconcile_eq_sort_hints
    // which should clear the stale Bool hint since 42 is Int.
    let eq_expr = eq(f_call, int(42));
    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "f(x) == 42 encoding should succeed (hint reconciled): {result:?}"
    );

    // After reconciliation, the Bool hint should be cleared
    assert!(
        !encoder.is_bool_var(&smt_name),
        "f's Bool hint should be cleared after equality with Int literal"
    );
}

/// When both sides of equality are LogicFnCalls, neither hint should be cleared
/// (we can't determine which is canonical).
#[test]
#[timeout(30000)]
fn test_reconcile_eq_both_logic_fn_no_clear() {
    let mut encoder = AYEncoder::new();

    let f_call = logic_fn_call("f", vec![var("x")]);
    let g_call = logic_fn_call("g", vec![var("y")]);

    // Give both Bool hints
    let bool_ctx = and(f_call.clone(), g_call.clone());
    encoder.register_sort_hints(&[bool_ctx]);

    let smt_f = trust_wp_core::logic::logic_fn_smt_name("f");
    let smt_g = trust_wp_core::logic::logic_fn_smt_name("g");
    assert!(encoder.is_bool_var(&smt_f));
    assert!(encoder.is_bool_var(&smt_g));

    // f(x) == g(y) — both are LogicFnCall, no clearing should happen
    let eq_expr = eq(f_call, g_call);
    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "f(x) == g(y) encoding should succeed: {result:?}"
    );

    // Both hints should remain (both sides are LogicFnCall)
    assert!(
        encoder.is_bool_var(&smt_f),
        "f's Bool hint should remain when compared with another LogicFnCall"
    );
    assert!(
        encoder.is_bool_var(&smt_g),
        "g's Bool hint should remain when compared with another LogicFnCall"
    );
}

/// When a LogicFnCall is compared with a Bool-valued expression, the Bool
/// hint should NOT be cleared.
#[test]
#[timeout(30000)]
fn test_reconcile_eq_logic_fn_with_bool_preserves_hint() {
    let mut encoder = AYEncoder::new();

    let f_call = logic_fn_call("f", vec![var("x")]);

    // Give f a Bool hint via Ite condition context
    let bool_ctx = ite(f_call.clone(), int(1), int(0));
    encoder.register_sort_hints(&[bool_ctx]);

    let smt_f = trust_wp_core::logic::logic_fn_smt_name("f");
    assert!(encoder.is_bool_var(&smt_f));

    // f(x) == (a > 0) — rhs is Bool, so hint should be preserved
    let cmp = gt(var("a"), int(0));
    let eq_expr = eq(f_call, cmp);
    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "f(x) == (a > 0) encoding should succeed: {result:?}"
    );

    // Bool hint should remain since rhs infers to Bool
    assert!(
        encoder.is_bool_var(&smt_f),
        "f's Bool hint should remain when compared with Bool expression"
    );
}

// =============================================================================
// produces sort inference tests (#379)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_produces_infer_expr_sort_returns_bool() {
    // produces(...) should infer as Bool
    let produces = method_call(var("iter"), "produces", vec![var("seq"), var("next")]);
    assert_eq!(infer_expr_sort(&produces), Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_produces_visited_arg_gets_seq_hint() {
    // self.produces(visited@, o): after register_sort_hints, visited@ is Seq
    let mut encoder = AYEncoder::new();

    let visited_view = view(var("visited"));
    let produces = method_call(
        var("self"),
        "produces",
        vec![visited_view.clone(), var("o")],
    );

    encoder.register_sort_hints(std::slice::from_ref(&produces));
    // If the sort hint is registered correctly, encoding succeeds.
    // Without the hint, the visited View would get Int sort, causing a
    // sort mismatch in the SMT function declaration.
    let result = encoder.encode_pure(&produces);
    assert!(
        result.is_ok(),
        "produces with View(visited) should encode after sort hint registration: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_produces_with_seq_literal_encodes() {
    // self.produces(seq![v], ^self) — seq literal arg encodes without error
    let mut encoder = AYEncoder::new();

    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let produces = method_call(
        deref(var("self")),
        "produces",
        vec![seq_v, final_expr(var("self"))],
    );

    encoder.register_sort_hints(std::slice::from_ref(&produces));
    let result = encoder.encode_pure(&produces);
    assert!(
        result.is_ok(),
        "produces with seq![v] should encode: {result:?}"
    );
}

// =============================================================================
