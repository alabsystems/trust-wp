// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `LogicFnDef::detect_recursion()` (#1296).

use std::sync::Arc;

use trust_wp_core::{
    formula::{ExprSort, PureExpr},
    logic::LogicFnDef,
};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.into(), None)
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

fn logic_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.into(),
        args,
    }
}

// ── Positive cases (should detect recursion) ─────────────────────────

#[test]
fn test_detect_recursion_self_call() {
    // f(x) = f(x) — simplest recursive body
    let body = logic_call("f", vec![var("x")]);
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(def.is_recursive(), "direct self-call should be recursive");
}

#[test]
fn test_detect_recursion_nested_in_ite() {
    // f(x) = if x > 0 then f(x - 1) else 0
    let body = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        )),
        Arc::new(logic_call(
            "f",
            vec![PureExpr::BinOp(
                Arc::new(var("x")),
                trust_wp_core::formula::BinOp::Sub,
                Arc::new(int(1)),
            )],
        )),
        Arc::new(int(0)),
    );
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call nested in Ite branch should be recursive"
    );
}

#[test]
fn test_detect_recursion_nested_in_let() {
    // f(x) = let y = f(x) in y
    let body = PureExpr::Let {
        var: "y".into(),
        value: Arc::new(logic_call("f", vec![var("x")])),
        body: Arc::new(var("y")),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Let value should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_let_body() {
    // f(x) = let y = 0 in f(y)
    let body = PureExpr::Let {
        var: "y".into(),
        value: Arc::new(int(0)),
        body: Arc::new(logic_call("f", vec![var("y")])),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Let body should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_forall_body() {
    // f(x) = forall<y> f(y)
    let body = PureExpr::Forall {
        var: "y".into(),
        var_sort: None,
        body: Arc::new(logic_call("f", vec![var("y")])),
        triggers: vec![],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Forall body should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_forall_trigger() {
    // f(x) = forall<y: Int> (y > 0) :pattern ((f(y)))
    // Self-call appears ONLY in the trigger, not in the body.
    let body = PureExpr::Forall {
        var: "y".into(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("y")),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        )),
        triggers: vec![vec![logic_call("f", vec![var("y")])]],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Forall trigger should be detected as recursive"
    );
}

#[test]
fn test_detect_recursion_in_exists_trigger() {
    // f(x) = exists<y: Int> true :pattern ((f(y)))
    let body = PureExpr::Exists {
        var: "y".into(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![logic_call("f", vec![var("y")])]],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Exists trigger should be detected as recursive"
    );
}

#[test]
fn test_detect_recursion_nested_in_args() {
    // f(x) = g(f(x))  — self-call nested inside another function's args
    let body = logic_call("g", vec![logic_call("f", vec![var("x")])]);
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call nested in another call's args should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_binop() {
    // f(x) = x + f(x - 1)
    let body = PureExpr::BinOp(
        Arc::new(var("x")),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(logic_call(
            "f",
            vec![PureExpr::BinOp(
                Arc::new(var("x")),
                trust_wp_core::formula::BinOp::Sub,
                Arc::new(int(1)),
            )],
        )),
    );
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in BinOp operand should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_deref() {
    // f(x) = *f(x)
    let body = PureExpr::Deref(Arc::new(logic_call("f", vec![var("x")])));
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call inside Deref should be recursive"
    );
}

// ── Negative cases (should NOT detect recursion) ─────────────────────

#[test]
fn test_detect_recursion_non_recursive() {
    let body = var("x");
    let def =
        LogicFnDef::new("g".into(), "test::g".into(), vec!["x".into()], body).detect_recursion();
    assert!(!def.is_recursive(), "identity function is not recursive");
}

#[test]
fn test_detect_recursion_calls_other_fn() {
    // f(x) = g(x) — calls a different function, not self
    let body = logic_call("g", vec![var("x")]);
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        !def.is_recursive(),
        "calling a different function is not recursive"
    );
}

#[test]
fn test_detect_recursion_complex_non_recursive() {
    // f(x) = if x > 0 then g(x - 1) + h(x) else 0
    let body = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        )),
        Arc::new(PureExpr::BinOp(
            Arc::new(logic_call(
                "g",
                vec![PureExpr::BinOp(
                    Arc::new(var("x")),
                    trust_wp_core::formula::BinOp::Sub,
                    Arc::new(int(1)),
                )],
            )),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(logic_call("h", vec![var("x")])),
        )),
        Arc::new(int(0)),
    );
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        !def.is_recursive(),
        "complex body calling only other functions is not recursive"
    );
}

#[test]
fn test_detect_recursion_forall_trigger_other_fn() {
    // f(x) = forall<y> true :pattern ((g(y))) — trigger has g, not f
    let body = PureExpr::Forall {
        var: "y".into(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![logic_call("g", vec![var("y")])]],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        !def.is_recursive(),
        "trigger with different function name is not recursive"
    );
}

// ── LetAssume / LetObligation / Match / Closure / MethodCall variants ─

#[test]
fn test_detect_recursion_in_let_assume_assumption() {
    // f(x) = let_assume f(x) in x
    let body = PureExpr::LetAssume {
        assumption: Arc::new(logic_call("f", vec![var("x")])),
        body: Arc::new(var("x")),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in LetAssume assumption should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_let_assume_body() {
    // f(x) = let_assume true in f(x)
    let body = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(logic_call("f", vec![var("x")])),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in LetAssume body should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_let_obligation_obligation() {
    // f(x) = let_obligation f(x) in x
    let body = PureExpr::LetObligation {
        obligation: Arc::new(logic_call("f", vec![var("x")])),
        body: Arc::new(var("x")),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in LetObligation obligation should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_let_obligation_body() {
    // f(x) = let_obligation true in f(x)
    let body = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(logic_call("f", vec![var("x")])),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in LetObligation body should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_match_scrutinee() {
    use trust_wp_core::formula::{MatchArm, Pattern};
    // f(x) = match f(x) { _ => 0 }
    let body = PureExpr::Match {
        scrutinee: Arc::new(logic_call("f", vec![var("x")])),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: int(0),
        }],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Match scrutinee should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_match_arm_body() {
    use trust_wp_core::formula::{MatchArm, Pattern};
    // f(x) = match x { _ => f(x) }
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: logic_call("f", vec![var("x")]),
        }],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Match arm body should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_closure_body() {
    // f(x) = |y| f(y)
    let body = PureExpr::Closure {
        params: vec![("y".into(), None)],
        body: Arc::new(logic_call("f", vec![var("y")])),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in Closure body should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_method_call_receiver() {
    // f(x) = f(x).len()
    let body = PureExpr::MethodCall {
        receiver: Arc::new(logic_call("f", vec![var("x")])),
        method: "len".into(),
        args: vec![],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in MethodCall receiver should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_method_syntax_self_call() {
    // lemma(self) = self.lemma() — method-syntax recursive call (#2548)
    // Logic functions on impl blocks (e.g., `impl List { fn lemma_sum_nonneg(&self) }`)
    // are called in method syntax: `self.lemma_sum_nonneg()`. The MethodCall.method
    // must be checked against the function name to detect recursion.
    let body = PureExpr::MethodCall {
        receiver: Arc::new(var("self")),
        method: "lemma".into(),
        args: vec![],
    };
    let def = LogicFnDef::new(
        "lemma".into(),
        "test::T::lemma".into(),
        vec!["self".into()],
        body,
    )
    .detect_recursion();
    assert!(
        def.is_recursive(),
        "method-syntax self-call (self.lemma()) should be recursive"
    );
}

#[test]
fn test_detect_recursion_method_syntax_different_name() {
    // f(self) = self.g() — method call to a DIFFERENT function is NOT recursive
    let body = PureExpr::MethodCall {
        receiver: Arc::new(var("self")),
        method: "g".into(),
        args: vec![],
    };
    let def = LogicFnDef::new("f".into(), "test::T::f".into(), vec!["self".into()], body)
        .detect_recursion();
    assert!(
        !def.is_recursive(),
        "method-syntax call to a different method should not be recursive"
    );
}

#[test]
fn test_detect_recursion_in_method_call_args() {
    // f(x) = x.push(f(x))
    let body = PureExpr::MethodCall {
        receiver: Arc::new(var("x")),
        method: "push".into(),
        args: vec![logic_call("f", vec![var("x")])],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call in MethodCall args should be recursive"
    );
}

// ── Negative cases for new variants ───────────────────────────────────

#[test]
fn test_detect_recursion_let_assume_no_self_call() {
    // f(x) = let_assume (x > 0) in g(x)
    let body = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        )),
        body: Arc::new(logic_call("g", vec![var("x")])),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        !def.is_recursive(),
        "LetAssume with no self-call should not be recursive"
    );
}

#[test]
fn test_detect_recursion_match_no_self_call() {
    use trust_wp_core::formula::{MatchArm, Pattern};
    // f(x) = match x { _ => g(x) }
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: logic_call("g", vec![var("x")]),
        }],
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        !def.is_recursive(),
        "Match calling only other functions should not be recursive"
    );
}

#[test]
fn test_detect_recursion_closure_no_self_call() {
    // f(x) = |y| g(y)
    let body = PureExpr::Closure {
        params: vec![("y".into(), None)],
        body: Arc::new(logic_call("g", vec![var("y")])),
    };
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        !def.is_recursive(),
        "Closure calling only other functions should not be recursive"
    );
}

#[test]
fn test_detect_recursion_in_old_wrapper() {
    // f(x) = old(f(x))
    let body = PureExpr::Old(Arc::new(logic_call("f", vec![var("x")])));
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call inside Old wrapper should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_final_wrapper() {
    // f(x) = final(f(x))
    let body = PureExpr::Final(Arc::new(logic_call("f", vec![var("x")])));
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call inside Final wrapper should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_view_wrapper() {
    // f(x) = view(f(x))
    let body = PureExpr::View(Arc::new(logic_call("f", vec![var("x")])));
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call inside View wrapper should be recursive"
    );
}

#[test]
fn test_detect_recursion_in_unop() {
    // f(x) = !f(x)
    let body = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(logic_call("f", vec![var("x")])),
    );
    let def =
        LogicFnDef::new("f".into(), "test::f".into(), vec!["x".into()], body).detect_recursion();
    assert!(
        def.is_recursive(),
        "self-call inside UnOp should be recursive"
    );
}
