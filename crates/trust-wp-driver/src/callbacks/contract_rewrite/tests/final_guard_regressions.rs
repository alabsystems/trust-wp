// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── Final guard regression tests (#2124) ──

/// Regression test (#2124): tuple_get_0(Final(x)) must NOT simplify to Final(x)
/// when x is a newtype param. Inside Final, the parameter's final value is
/// wrapped in tuple1(field_val), so tuple_get_0 is needed to decompose it.
#[test]
fn simplify_newtype_tuple_get_0_of_final_preserved() {
    let mut params = HashSet::new();
    params.insert("x".to_string());

    // tuple_get_0(Final(Var("x"))) — should be preserved because arg contains Final
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    // The tuple_get_0 must remain because the arg contains Final
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None
            )))],
        },
    );
}

/// Bug/486 fix: Final(tuple_get_0(x)) — the Final wraps the entire
/// tuple_get_0 call for a newtype param. The inner tuple_get_0(Var("x"))
/// should simplify to Var("x.0") because the arg is a bare Var (no Final
/// wrapper on the arg itself) and the field-level final value is authoritative.
/// The outer Final is preserved.
///
/// User-written `^x.0` postconditions parse with Final around the field
/// projection. MIR extraction records the mutated inner reference as `x.0`,
/// so the rewrite keeps final-state lookup aligned with that key.
#[test]
fn simplify_newtype_final_of_tuple_get_0_uses_field_lane() {
    let mut params = HashSet::new();
    params.insert("x".to_string());

    // Final(tuple_get_0(Var("x"))) — use x.0 inside Final.
    let expr = PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    }));
    let result = simplify_newtype_field_access_expr(&expr, &params);
    // tuple_get_0(Var("x")) simplifies to Var("x.0"), outer Final preserved
    assert_eq!(
        result,
        PureExpr::Final(Arc::new(PureExpr::Var("x.0".to_string(), None))),
    );
}

/// Bug/486 fix: quantifier body and triggers containing
/// Final(tuple_get_0(Var("x.0"))) should simplify: the closure capture
/// "x.0" -> "x" rewrite applies, then tuple_get_0(Var("x")) simplifies
/// to Var("x.0") even inside Final (bare Var, no Final on the arg).
#[test]
fn simplify_newtype_quantifier_triggers_traverse_under_final_uses_field_lane() {
    let mut params = HashSet::new();
    params.insert("x".to_string());

    let final_tuple_get = PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("x.0".to_string(), None)],
    }));
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(final_tuple_get.clone()),
        triggers: vec![vec![final_tuple_get]],
    };

    let result = simplify_newtype_field_access_expr(&expr, &params);
    // Both body and triggers: Final(tuple_get_0(Var("x.0"))) -> Final(Var("x.0"))
    let expected_final = PureExpr::Final(Arc::new(PureExpr::Var("x.0".to_string(), None)));

    assert_eq!(
        result,
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(expected_final.clone()),
            triggers: vec![vec![expected_final]],
        }
    );
}
