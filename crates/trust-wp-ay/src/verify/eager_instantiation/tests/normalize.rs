// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(5000)]
fn normalize_deref_strips_deref_on_var() {
    // Deref(Var("x")) -> Var("x")
    let input = deref(var("x"));
    let result = normalize_deref_final(&input);
    assert!(exprs_structurally_equal(&result, &var("x")));
}

#[test]
#[timeout(5000)]
fn normalize_final_appends_suffix() {
    // Final(Var("x")) -> Var("x_final")
    let input = final_expr(var("x"));
    let result = normalize_deref_final(&input);
    assert!(exprs_structurally_equal(&result, &var("x_final")));
}

#[test]
#[timeout(5000)]
fn normalize_nested_final() {
    // Final(Final(Var("x"))) -> Var("x_final_final")
    let input = final_expr(final_expr(var("x")));
    let result = normalize_deref_final(&input);
    assert!(exprs_structurally_equal(&result, &var("x_final_final")));
}

#[test]
#[timeout(5000)]
fn normalize_deref_final_on_method_call() {
    // Deref(Var("f")).postcondition_mut(Final(Var("f")))
    // -> Var("f").postcondition_mut(Var("f_final"))
    let input = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![final_expr(var("f"))],
    );
    let result = normalize_deref_final(&input);
    let expected = method_call(var("f"), "postcondition_mut", vec![var("f_final")]);
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_preserves_plain_var() {
    let input = var("x");
    let result = normalize_deref_final(&input);
    assert!(exprs_structurally_equal(&result, &var("x")));
}

#[test]
#[timeout(5000)]
fn normalize_preserves_int_literal() {
    let input = int(42);
    let result = normalize_deref_final(&input);
    assert!(exprs_structurally_equal(&result, &int(42)));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_binop() {
    let input = add(deref(var("x")), final_expr(var("y")));
    let result = normalize_deref_final(&input);
    let expected = add(var("x"), var("y_final"));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_ite() {
    let input = ite(bool_expr(true), deref(var("x")), final_expr(var("y")));
    let result = normalize_deref_final(&input);
    let expected = ite(bool_expr(true), var("x"), var("y_final"));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_unop() {
    let input = not(deref(var("x")));
    let result = normalize_deref_final(&input);
    let expected = not(var("x"));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_logic_fn_call() {
    let input = logic_fn_call("resolve", vec![final_expr(var("f"))]);
    let result = normalize_deref_final(&input);
    let expected = logic_fn_call("resolve", vec![var("f_final")]);
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_view() {
    let input = view(deref(var("v")));
    let result = normalize_deref_final(&input);
    let expected = view(var("v"));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_old() {
    let input = old(final_expr(var("x")));
    let result = normalize_deref_final(&input);
    let expected = old(var("x_final"));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_forall() {
    let input = forall("i", gt(deref(var("x")), var("i")));
    let result = normalize_deref_final(&input);
    let expected = forall("i", gt(var("x"), var("i")));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_recurses_through_let() {
    let input = let_bind("t", final_expr(var("x")), var("t"));
    let result = normalize_deref_final(&input);
    let expected = let_bind("t", var("x_final"), var("t"));
    assert!(exprs_structurally_equal(&result, &expected));
}

#[test]
#[timeout(5000)]
fn normalize_final_on_non_var_preserves_final() {
    // Final(Int(1)) stays Final(Int(1)) since the inner is not a Var
    let input = final_expr(int(1));
    let result = normalize_deref_final(&input);
    assert!(exprs_structurally_equal(&result, &final_expr(int(1))));
}

#[test]
#[timeout(5000)]
fn normalize_preserves_shared_arc_for_unchanged_view_inner() {
    let shared = Arc::new(var("x"));
    let input = PureExpr::View(Arc::clone(&shared));

    let result = normalize_deref_final(&input);

    match result {
        PureExpr::View(inner) => {
            assert!(
                Arc::ptr_eq(&inner, &shared),
                "normalize_deref_final should preserve unchanged Arc-backed subtrees"
            );
        }
        other => panic!("expected view expression, got: {other:?}"),
    }
}
