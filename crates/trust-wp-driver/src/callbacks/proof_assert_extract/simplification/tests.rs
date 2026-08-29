// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for expression simplification passes.

use std::sync::Arc;

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::{
    constructor_methods::reduce_concrete_constructor_method_calls,
    match_reduction::reduce_concrete_matches,
};

fn logic_fn_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

fn deref(e: PureExpr) -> PureExpr {
    PureExpr::Deref(Arc::new(e))
}

fn match_expr(scrutinee: PureExpr, arms: Vec<(Pattern, PureExpr)>) -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(scrutinee),
        arms: arms
            .into_iter()
            .map(|(pattern, body)| MatchArm { pattern, body })
            .collect(),
    }
}

fn eq(l: PureExpr, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), trust_wp_core::formula::BinOp::Eq, Arc::new(r))
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(n: i64) -> PureExpr {
    PureExpr::Int(n)
}

// --- Tests for reduce_concrete_matches ---

/// `match *None() { Some(v) => body1, None => body2 }` reduces to body2
#[test]
fn reduce_match_none_scrutinee() {
    let scrutinee = deref(logic_fn_call("None", vec![]));
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            eq(var("result"), var("v")),
        ),
        (
            Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            eq(var("result"), int(42)),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, eq(var("result"), int(42)));
}

/// `match *Some(1) { Some(v) => result == v, None => ... }` reduces to `result == 1`
#[test]
fn reduce_match_some_scrutinee_with_binding() {
    let scrutinee = deref(logic_fn_call("Some", vec![int(1)]));
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            eq(var("result"), var("v")),
        ),
        (
            Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            eq(var("result"), int(42)),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, eq(var("result"), int(1)));
}

/// `whole @ Some(v)` binds both the full constructor and its payload.
#[test]
fn reduce_match_alias_constructor_binds_whole_and_inner() {
    let scrutinee = deref(logic_fn_call("Some", vec![int(1)]));
    let arms = vec![(
        Pattern::Alias {
            alias: "whole".to_string(),
            pattern: Box::new(Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            }),
        },
        logic_fn_call("Pair", vec![var("whole"), var("v")]),
    )];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(
        reduced,
        logic_fn_call("Pair", vec![logic_fn_call("Some", vec![int(1)]), int(1)])
    );
}

/// `match *Ok(5) { Ok(v) => result == v, Err(e) => ... }` reduces to `result == 5`
#[test]
fn reduce_match_ok_scrutinee() {
    let scrutinee = deref(logic_fn_call("Ok", vec![int(5)]));
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Ok".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            eq(var("result"), var("v")),
        ),
        (
            Pattern::Constructor {
                name: "Err".to_string(),
                inner: Some(Box::new(Pattern::Binding("e".to_string()))),
            },
            eq(var("result"), var("e")),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, eq(var("result"), int(5)));
}

/// `match *Err(7) { Ok(v) => ..., Err(e) => result == e }` reduces to `result == 7`
#[test]
fn reduce_match_err_scrutinee() {
    let scrutinee = deref(logic_fn_call("Err", vec![int(7)]));
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Ok".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            eq(var("result"), var("v")),
        ),
        (
            Pattern::Constructor {
                name: "Err".to_string(),
                inner: Some(Box::new(Pattern::Binding("e".to_string()))),
            },
            eq(var("result"), var("e")),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, eq(var("result"), int(7)));
}

/// Non-constructor scrutinee leaves match unchanged.
#[test]
fn non_constructor_scrutinee_unchanged() {
    let scrutinee = var("x");
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            var("v"),
        ),
        (
            Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            int(0),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr.clone());
    assert_eq!(reduced, expr);
}

/// Wildcard arm matches any constructor.
#[test]
fn wildcard_arm_matches_any_constructor() {
    let scrutinee = deref(logic_fn_call("None", vec![]));
    let arms = vec![(Pattern::Wildcard, int(99))];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, int(99));
}

/// Nested match with concrete scrutinee is reduced recursively.
#[test]
fn nested_match_reduced() {
    let inner = match_expr(
        deref(logic_fn_call("None", vec![])),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );
    let outer = eq(var("result"), inner);
    let reduced = reduce_concrete_matches(outer);
    assert_eq!(reduced, eq(var("result"), int(0)));
}

/// Match with path-qualified constructor name is recognized.
#[test]
fn path_qualified_constructor_name() {
    let scrutinee = deref(logic_fn_call("core::option::Option::None", vec![]));
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            var("v"),
        ),
        (
            Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            int(0),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, int(0));
}

/// Without Deref wrapper, bare LogicFnCall is also recognized.
#[test]
fn bare_logic_fn_call_without_deref() {
    let scrutinee = logic_fn_call("Some", vec![int(3)]);
    let arms = vec![
        (
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            eq(var("result"), var("v")),
        ),
        (
            Pattern::Constructor {
                name: "None".to_string(),
                inner: None,
            },
            eq(var("result"), int(0)),
        ),
    ];
    let expr = match_expr(scrutinee, arms);
    let reduced = reduce_concrete_matches(expr);
    assert_eq!(reduced, eq(var("result"), int(3)));
}

// --- Tests for reduce_concrete_constructor_method_calls ---

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn implies(l: PureExpr, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(l),
        trust_wp_core::formula::BinOp::Implies,
        Arc::new(r),
    )
}

/// `None().is_some()` reduces to `false`
#[test]
fn test_ctor_none_is_some_reduces_to_false() {
    let expr = method_call(logic_fn_call("None", vec![]), "is_some", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(false));
}

/// `None().is_none()` reduces to `true`
#[test]
fn test_ctor_none_is_none_reduces_to_true() {
    let expr = method_call(logic_fn_call("None", vec![]), "is_none", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `Some(1).is_some()` reduces to `true`
#[test]
fn test_ctor_some_is_some_reduces_to_true() {
    let expr = method_call(logic_fn_call("Some", vec![int(1)]), "is_some", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `Some(1).is_none()` reduces to `false`
#[test]
fn test_ctor_some_is_none_reduces_to_false() {
    let expr = method_call(logic_fn_call("Some", vec![int(1)]), "is_none", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(false));
}

/// `Some(42).unwrap()` reduces to `42`
#[test]
fn test_ctor_some_unwrap_reduces_to_inner() {
    let expr = method_call(logic_fn_call("Some", vec![int(42)]), "unwrap", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(42));
}

/// `Ok(5).is_ok()` reduces to `true`
#[test]
fn test_ctor_ok_is_ok_reduces_to_true() {
    let expr = method_call(logic_fn_call("Ok", vec![int(5)]), "is_ok", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `Err(7).is_err()` reduces to `true`
#[test]
fn test_ctor_err_is_err_reduces_to_true() {
    let expr = method_call(logic_fn_call("Err", vec![int(7)]), "is_err", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `Err(7).unwrap_err()` reduces to `7`
#[test]
fn test_ctor_err_unwrap_err_reduces_to_inner() {
    let expr = method_call(logic_fn_call("Err", vec![int(7)]), "unwrap_err", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(7));
}

/// `false ==> X` reduces to `true` (vacuously true)
#[test]
fn test_false_implies_reduces_to_true() {
    let expr = implies(PureExpr::Bool(false), var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `true ==> X` reduces to `X`
#[test]
fn test_true_implies_reduces_to_consequent() {
    let expr = implies(PureExpr::Bool(true), var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("x"));
}

/// `None().is_some() ==> (call_3 == Ok(old(None().unwrap())))` reduces to `true`
/// This is the real-world pattern from ok_or postcondition.
#[test]
fn test_ok_or_vacuous_implication_reduces_to_true() {
    let antecedent = method_call(logic_fn_call("None", vec![]), "is_some", vec![]);
    let consequent = eq(
        var("call_3"),
        logic_fn_call(
            "Ok",
            vec![PureExpr::Old(Arc::new(method_call(
                logic_fn_call("None", vec![]),
                "unwrap",
                vec![],
            )))],
        ),
    );
    let expr = implies(antecedent, consequent);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `None().is_none() ==> (call_3 == Err(true))` reduces to `call_3 == Err(true)`
/// The useful branch of the ok_or postcondition.
#[test]
fn test_ok_or_useful_implication_reduces_to_body() {
    let antecedent = method_call(logic_fn_call("None", vec![]), "is_none", vec![]);
    let consequent = eq(
        var("call_3"),
        logic_fn_call("Err", vec![PureExpr::Bool(true)]),
    );
    let expr = implies(antecedent, consequent);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(
        reduced,
        eq(
            var("call_3"),
            logic_fn_call("Err", vec![PureExpr::Bool(true)])
        )
    );
}

/// Deref-wrapped constructors are recognized: `*Some(1).is_some()` → `true`
#[test]
fn test_deref_wrapped_constructor_method_call() {
    let expr = method_call(
        deref(logic_fn_call("Some", vec![int(1)])),
        "is_some",
        vec![],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// Non-constructor receiver is not reduced.
#[test]
fn test_non_constructor_receiver_unchanged() {
    let expr = method_call(var("x"), "is_some", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr.clone());
    assert_eq!(reduced, expr);
}

// --- Tests for ok()/err() conversions ---

/// `Ok(5).ok()` → `Some(5)`
#[test]
fn test_ctor_ok_ok_reduces_to_some() {
    let expr = method_call(logic_fn_call("Ok", vec![int(5)]), "ok", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Some", vec![int(5)]));
}

/// `Err(7).ok()` → `None()`
#[test]
fn test_ctor_err_ok_reduces_to_none() {
    let expr = method_call(logic_fn_call("Err", vec![int(7)]), "ok", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("None", vec![]));
}

/// `Err(3).err()` → `Some(3)`
#[test]
fn test_ctor_err_err_reduces_to_some() {
    let expr = method_call(logic_fn_call("Err", vec![int(3)]), "err", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Some", vec![int(3)]));
}

/// `Ok(5).err()` → `None()`
#[test]
fn test_ctor_ok_err_reduces_to_none() {
    let expr = method_call(logic_fn_call("Ok", vec![int(5)]), "err", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("None", vec![]));
}

// --- Tests for unwrap_or ---

/// `Some(42).unwrap_or(0)` → `42`
#[test]
fn test_ctor_some_unwrap_or_reduces_to_inner() {
    let expr = method_call(
        logic_fn_call("Some", vec![int(42)]),
        "unwrap_or",
        vec![int(0)],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(42));
}

/// `None().unwrap_or(99)` → `99`
#[test]
fn test_ctor_none_unwrap_or_reduces_to_default() {
    let expr = method_call(logic_fn_call("None", vec![]), "unwrap_or", vec![int(99)]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(99));
}

/// `Ok(10).unwrap_or(0)` → `10`
#[test]
fn test_ctor_ok_unwrap_or_reduces_to_inner() {
    let expr = method_call(
        logic_fn_call("Ok", vec![int(10)]),
        "unwrap_or",
        vec![int(0)],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(10));
}

/// `Err(7).unwrap_or(0)` → `0`
#[test]
fn test_ctor_err_unwrap_or_reduces_to_default() {
    let expr = method_call(
        logic_fn_call("Err", vec![int(7)]),
        "unwrap_or",
        vec![int(0)],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(0));
}

// --- Tests for boolean constant folding ---

fn and(l: PureExpr, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), trust_wp_core::formula::BinOp::And, Arc::new(r))
}

fn or(l: PureExpr, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), trust_wp_core::formula::BinOp::Or, Arc::new(r))
}

fn not(inner: PureExpr) -> PureExpr {
    PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, Arc::new(inner))
}

fn ite(cond: PureExpr, then_br: PureExpr, else_br: PureExpr) -> PureExpr {
    PureExpr::Ite(Arc::new(cond), Arc::new(then_br), Arc::new(else_br))
}

/// `true && X` → `X`
#[test]
fn test_true_and_x_reduces_to_x() {
    let expr = and(PureExpr::Bool(true), var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("x"));
}

/// `false && X` → `false`
#[test]
fn test_false_and_x_reduces_to_false() {
    let expr = and(PureExpr::Bool(false), var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(false));
}

/// `X && true` → `X`
#[test]
fn test_x_and_true_reduces_to_x() {
    let expr = and(var("x"), PureExpr::Bool(true));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("x"));
}

/// `X && false` → `false`
#[test]
fn test_x_and_false_reduces_to_false() {
    let expr = and(var("x"), PureExpr::Bool(false));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(false));
}

/// `true || X` → `true`
#[test]
fn test_true_or_x_reduces_to_true() {
    let expr = or(PureExpr::Bool(true), var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `false || X` → `X`
#[test]
fn test_false_or_x_reduces_to_x() {
    let expr = or(PureExpr::Bool(false), var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("x"));
}

/// `X || true` → `true`
#[test]
fn test_x_or_true_reduces_to_true() {
    let expr = or(var("x"), PureExpr::Bool(true));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `X || false` → `X`
#[test]
fn test_x_or_false_reduces_to_x() {
    let expr = or(var("x"), PureExpr::Bool(false));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("x"));
}

/// `not(true)` → `false`
#[test]
fn test_not_true_reduces_to_false() {
    let expr = not(PureExpr::Bool(true));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(false));
}

/// `not(false)` → `true`
#[test]
fn test_not_false_reduces_to_true() {
    let expr = not(PureExpr::Bool(false));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// `not(X)` unchanged when X is not a constant
#[test]
fn test_not_var_unchanged() {
    let expr = not(var("x"));
    let reduced = reduce_concrete_constructor_method_calls(expr.clone());
    assert_eq!(reduced, expr);
}

/// `if true { X } else { Y }` → `X`
#[test]
fn test_ite_true_reduces_to_then() {
    let expr = ite(PureExpr::Bool(true), var("x"), var("y"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("x"));
}

/// `if false { X } else { Y }` → `Y`
#[test]
fn test_ite_false_reduces_to_else() {
    let expr = ite(PureExpr::Bool(false), var("x"), var("y"));
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, var("y"));
}

/// `if X { Y } else { Z }` unchanged when condition is not a constant
#[test]
fn test_ite_var_unchanged() {
    let expr = ite(var("cond"), var("x"), var("y"));
    let reduced = reduce_concrete_constructor_method_calls(expr.clone());
    assert_eq!(reduced, expr);
}

// --- Composite test: chained reductions ---

/// `None().is_some() && Some(1).is_some()` → `false` (short-circuit via And)
#[test]
fn test_chained_method_and_bool_reduction() {
    let expr = and(
        method_call(logic_fn_call("None", vec![]), "is_some", vec![]),
        method_call(logic_fn_call("Some", vec![int(1)]), "is_some", vec![]),
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(false));
}

/// `if None().is_some() { 1 } else { 2 }` → `2`
#[test]
fn test_ite_with_method_call_condition() {
    let expr = ite(
        method_call(logic_fn_call("None", vec![]), "is_some", vec![]),
        int(1),
        int(2),
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(2));
}

// --- Tests for Old-transparent extraction ---

/// Old-wrapped constructors are recognized: `old(Some(1)).unwrap()` → `1`
/// This pattern arises from postcondition substitution where `self` is
/// wrapped in `old()` for consumed parameters. (#2675)
#[test]
fn test_old_wrapped_constructor_unwrap() {
    let expr = method_call(
        PureExpr::Old(Arc::new(logic_fn_call("Some", vec![int(1)]))),
        "unwrap",
        vec![],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(1));
}

/// `old(None()).is_none()` → `true`
#[test]
fn test_old_wrapped_none_is_none() {
    let expr = method_call(
        PureExpr::Old(Arc::new(logic_fn_call("None", vec![]))),
        "is_none",
        vec![],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, PureExpr::Bool(true));
}

// --- Tests for ok_or reduction ---

/// `Some(v).ok_or(e)` → `Ok(v)`
#[test]
fn test_some_ok_or_reduces_to_ok() {
    let expr = method_call(
        logic_fn_call("Some", vec![int(1)]),
        "ok_or",
        vec![PureExpr::Bool(true)],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Ok", vec![int(1)]));
}

/// `None().ok_or(e)` → `Err(e)`
#[test]
fn test_none_ok_or_reduces_to_err() {
    let expr = method_call(
        logic_fn_call("None", vec![]),
        "ok_or",
        vec![PureExpr::Bool(true)],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Err", vec![PureExpr::Bool(true)]));
}

// --- Tests for expect/expect_err reduction ---

/// `Some(v).expect(msg)` → `v`
#[test]
fn test_some_expect_reduces_to_inner() {
    let expr = method_call(
        logic_fn_call("Some", vec![int(42)]),
        "expect",
        vec![var("msg")],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(42));
}

/// `Ok(v).expect(msg)` → `v`
#[test]
fn test_ok_expect_reduces_to_inner() {
    let expr = method_call(
        logic_fn_call("Ok", vec![int(7)]),
        "expect",
        vec![var("msg")],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(7));
}

/// `Err(e).expect_err(msg)` → `e`
#[test]
fn test_err_expect_err_reduces_to_inner() {
    let expr = method_call(
        logic_fn_call("Err", vec![int(99)]),
        "expect_err",
        vec![var("msg")],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, int(99));
}

// --- Short-circuit reduction tests ---

/// `None().map(f)` → `None()`
#[test]
fn test_none_map_reduces_to_none() {
    let expr = method_call(logic_fn_call("None", vec![]), "map", vec![var("f")]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("None", vec![]));
}

/// `Err(e).map(f)` → `Err(e)`
#[test]
fn test_err_map_reduces_to_err() {
    let expr = method_call(logic_fn_call("Err", vec![int(5)]), "map", vec![var("f")]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Err", vec![int(5)]));
}

/// `None().and_then(f)` → `None()`
#[test]
fn test_none_and_then_reduces_to_none() {
    let expr = method_call(logic_fn_call("None", vec![]), "and_then", vec![var("f")]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("None", vec![]));
}

/// `Err(e).and_then(f)` → `Err(e)`
#[test]
fn test_err_and_then_reduces_to_err() {
    let expr = method_call(
        logic_fn_call("Err", vec![int(3)]),
        "and_then",
        vec![var("f")],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Err", vec![int(3)]));
}

/// `Some(v).or(y)` → `Some(v)`
#[test]
fn test_some_or_reduces_to_some() {
    let expr = method_call(logic_fn_call("Some", vec![int(1)]), "or", vec![var("y")]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Some", vec![int(1)]));
}

/// `Ok(v).or(y)` → `Ok(v)`
#[test]
fn test_ok_or_alt_reduces_to_ok() {
    let expr = method_call(logic_fn_call("Ok", vec![int(1)]), "or", vec![var("y")]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Ok", vec![int(1)]));
}

/// `Ok(v).map_err(f)` → `Ok(v)`
#[test]
fn test_ok_map_err_reduces_to_ok() {
    let expr = method_call(
        logic_fn_call("Ok", vec![int(10)]),
        "map_err",
        vec![var("f")],
    );
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("Ok", vec![int(10)]));
}

/// `None().flatten()` → `None()`
#[test]
fn test_none_flatten_reduces_to_none() {
    let expr = method_call(logic_fn_call("None", vec![]), "flatten", vec![]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("None", vec![]));
}

/// `None().filter(f)` → `None()`
#[test]
fn test_none_filter_reduces_to_none() {
    let expr = method_call(logic_fn_call("None", vec![]), "filter", vec![var("f")]);
    let reduced = reduce_concrete_constructor_method_calls(expr);
    assert_eq!(reduced, logic_fn_call("None", vec![]));
}

// --- Tests for synthesize_constructor_equalities ---

use super::synthesize_constructor_equalities;

/// `x.is_none()` → synthesize `x == None()`
#[test]
fn test_synthesize_none_from_tester() {
    let facts = vec![method_call(var("x"), "is_none", vec![])];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert_eq!(synthesized.len(), 1);
    assert_eq!(synthesized[0], eq(var("x"), logic_fn_call("None", vec![])));
}

/// `x.is_err()` + `x.unwrap_err() == v` → synthesize `x == Err(v)`
#[test]
fn test_synthesize_err_from_tester_selector() {
    let facts = vec![
        method_call(var("call_3"), "is_err", vec![]),
        eq(
            method_call(var("call_3"), "unwrap_err", vec![]),
            PureExpr::Bool(true),
        ),
    ];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert_eq!(synthesized.len(), 1);
    assert_eq!(
        synthesized[0],
        eq(
            var("call_3"),
            logic_fn_call("Err", vec![PureExpr::Bool(true)])
        )
    );
}

/// `x.is_ok()` + `x.unwrap() == v` → synthesize `x == Ok(v)`
#[test]
fn test_synthesize_ok_from_tester_selector() {
    let facts = vec![
        method_call(var("call_7"), "is_ok", vec![]),
        eq(method_call(var("call_7"), "unwrap", vec![]), int(1)),
    ];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert_eq!(synthesized.len(), 1);
    assert_eq!(
        synthesized[0],
        eq(var("call_7"), logic_fn_call("Ok", vec![int(1)]))
    );
}

/// `x.is_some()` + `x.unwrap() == v` → synthesize `x == Some(v)`
#[test]
fn test_synthesize_some_from_tester_selector() {
    let facts = vec![
        method_call(var("result"), "is_some", vec![]),
        eq(method_call(var("result"), "unwrap", vec![]), int(42)),
    ];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert_eq!(synthesized.len(), 1);
    assert_eq!(
        synthesized[0],
        eq(var("result"), logic_fn_call("Some", vec![int(42)]))
    );
}

/// Tester without matching selector: `x.is_some()` alone → no synthesis
#[test]
fn test_synthesize_tester_without_selector_no_output() {
    let facts = vec![method_call(var("x"), "is_some", vec![])];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert!(synthesized.is_empty());
}

/// Selector without tester: `x.unwrap() == v` alone → no synthesis
#[test]
fn test_synthesize_selector_without_tester_no_output() {
    let facts = vec![eq(method_call(var("x"), "unwrap", vec![]), int(5))];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert!(synthesized.is_empty());
}

/// Symmetric selector: `v == x.unwrap_err()` → still matched
#[test]
fn test_synthesize_symmetric_selector() {
    let facts = vec![
        method_call(var("r"), "is_err", vec![]),
        eq(int(99), method_call(var("r"), "unwrap_err", vec![])),
    ];
    let synthesized = synthesize_constructor_equalities(&facts);
    assert_eq!(synthesized.len(), 1);
    assert_eq!(
        synthesized[0],
        eq(var("r"), logic_fn_call("Err", vec![int(99)]))
    );
}

// --- Tests for apply_constructor_equality_substitutions ---

use super::{
    apply_constructor_equality_substitutions, apply_constructor_equality_substitutions_to_facts,
    normalize_old_constructor_equality_facts, synthesize_ground_equality_substitution_facts,
};

/// Substitutes `result` with `Ok(v)` in a match expression.
#[test]
fn test_apply_ctor_eq_resolves_match() {
    // match result { Ok(i) => i < 5, Err(_) => false }
    let assertion = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("i".to_string()))),
                },
                PureExpr::BinOp(
                    Arc::new(var("i")),
                    trust_wp_core::formula::BinOp::Lt,
                    Arc::new(int(5)),
                ),
            ),
            (
                Pattern::Constructor {
                    name: "Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                PureExpr::Bool(false),
            ),
        ],
    );
    let facts = vec![eq(var("result"), logic_fn_call("Ok", vec![var("call_2")]))];
    let reduced = apply_constructor_equality_substitutions(assertion, &facts);
    // Should resolve to: call_2 < 5
    assert_eq!(
        reduced,
        PureExpr::BinOp(
            Arc::new(var("call_2")),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(int(5)),
        )
    );
}

/// Constructor equalities also reduce match expressions carried as assumed facts.
#[test]
fn test_apply_ctor_eq_reduces_assumed_fact_match() {
    let match_fact = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("i".to_string()))),
                },
                PureExpr::BinOp(
                    Arc::new(var("i")),
                    trust_wp_core::formula::BinOp::Lt,
                    Arc::new(int(5)),
                ),
            ),
            (
                Pattern::Constructor {
                    name: "Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                PureExpr::Bool(false),
            ),
        ],
    );
    let facts = vec![
        eq(var("result"), logic_fn_call("Ok", vec![var("call_2")])),
        match_fact,
    ];

    let (reduced, reduced_count) = apply_constructor_equality_substitutions_to_facts(&facts);

    assert_eq!(reduced_count, 1);
    assert!(
        reduced.contains(&PureExpr::BinOp(
            Arc::new(var("call_2")),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(int(5)),
        )),
        "match fact should reduce to its Ok branch"
    );
}

/// Literal equality facts instantiate reduced branch facts without solver help.
#[test]
fn test_ground_equality_substitution_instantiates_len_bound() {
    let len_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(var("s")))),
        method: "len".to_string(),
        args: vec![],
    };
    let branch_fact = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(var("call_2")),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(len_call.clone()),
        )),
        trust_wp_core::formula::BinOp::And,
        Arc::new(eq(var("x"), int(2))),
    );
    let equality_sources = vec![eq(len_call, int(5))];
    let facts = vec![branch_fact];

    let synthesized = synthesize_ground_equality_substitution_facts(&equality_sources, &facts);

    assert!(
        synthesized.contains(&PureExpr::BinOp(
            Arc::new(var("call_2")),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(int(5)),
        )),
        "len equality should instantiate the branch bound"
    );
}

/// No substitution when facts contain no constructor equalities.
#[test]
fn test_apply_ctor_eq_no_facts_returns_unchanged() {
    let expr = var("x");
    let reduced = apply_constructor_equality_substitutions(expr.clone(), &[]);
    assert_eq!(reduced, expr);
}

/// Symmetric: `Ok(v) == result` also works.
#[test]
fn test_apply_ctor_eq_symmetric() {
    let assertion = match_expr(
        var("r"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );
    // Constructor on the left side of equality
    let facts = vec![eq(logic_fn_call("Some", vec![int(42)]), var("r"))];
    let reduced = apply_constructor_equality_substitutions(assertion, &facts);
    assert_eq!(reduced, int(42));
}

/// Old-wrapped constructor equalities also substitute into the assertion.
#[test]
fn test_apply_ctor_eq_old_wrapped_result_resolves_tester() {
    let assertion = method_call(var("result"), "is_ok", vec![]);
    let facts = vec![eq(
        logic_fn_call("Ok", vec![int(42)]),
        PureExpr::Old(Arc::new(var("result"))),
    )];
    let reduced = apply_constructor_equality_substitutions(assertion, &facts);
    assert_eq!(reduced, PureExpr::Bool(true));
}

/// Old-wrapped constructor equalities can be normalized to a current-value fact.
#[test]
fn test_normalize_old_constructor_equality_fact() {
    let fact = eq(
        logic_fn_call("Ok", vec![int(42)]),
        PureExpr::Old(Arc::new(var("result"))),
    );
    let normalized = normalize_old_constructor_equality_facts(&fact);
    assert_eq!(
        normalized,
        vec![eq(logic_fn_call("Ok", vec![int(42)]), var("result"))]
    );
}

/// Call-result aliases also produce an upgraded constructor fact.
#[test]
fn test_normalize_old_constructor_equality_fact_for_call_alias() {
    let fact = eq(
        logic_fn_call("Ok", vec![int(42)]),
        PureExpr::Old(Arc::new(var("call_3"))),
    );
    let normalized = normalize_old_constructor_equality_facts(&fact);
    assert!(
        normalized.contains(&eq(logic_fn_call("Ok", vec![int(42)]), var("call_3"))),
        "normalized facts should retain the current-value bridge"
    );
    assert!(
        normalized.contains(&eq(
            logic_fn_call("Ok", vec![int(42)]),
            var("call_3__upgraded"),
        )),
        "normalized facts should add an upgraded bridge for call-result aliases"
    );
}

/// Non-constructor equality facts are ignored.
#[test]
fn test_apply_ctor_eq_ignores_non_constructor_facts() {
    let expr = var("x");
    let facts = vec![eq(var("x"), int(5))]; // Int is not a constructor
    let reduced = apply_constructor_equality_substitutions(expr.clone(), &facts);
    assert_eq!(reduced, expr);
}
