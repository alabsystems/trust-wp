// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the structural-recursion termination check
//! (`is_structurally_recursive`), exercising the exact PureExpr shapes the
//! parser produces for the deep_model / bug-corpus cases.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::{
    formula::{MatchArm, Pattern, PureExpr},
    logic::LogicMode,
};

use super::{super::LogicRecursionNode, is_structurally_recursive};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn field(field_name: &str, on: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: format!("__trust_wp_field_{field_name}"),
        args: vec![on],
    }
}

fn deep_model_call(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "deep_model".to_string(),
        args: vec![],
    }
}

fn node(name: &str, params: &[&str], body: PureExpr) -> LogicRecursionNode {
    LogicRecursionNode {
        full_path: format!("crate::{name}"),
        name: name.to_string(),
        params: params.iter().map(|s| (*s).to_string()).collect(),
        param_sort_hints: params.iter().map(|_| None).collect(),
        mode: LogicMode::Default,
        is_trait_method: false,
        body,
        body_text: String::new(),
        requires: vec![],
        ensures: vec![],
        raw_variants: vec![],
        parsed_variants: vec![],
        variant_parse_errors: vec![],
        body_parse_failed: false,
        deep_model_dispatch_targets: Some(HashSet::new()),
    }
}

/// mixed.rs `List::deep_model`: matches `self.tail`, binds `tail`, recurses via
/// `(*tail).deep_model()`. `*tail` is a strict subterm of arg 0 (self). ACCEPT.
#[test]
fn list_deep_model_is_structurally_recursive() {
    // match __trust_wp_field_tail(self) {
    //   None => None,
    //   Some(tail) => Some(Box::new((*tail).deep_model())),
    // }
    let body = PureExpr::Match {
        scrutinee: Arc::new(field("tail", var("self"))),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: var("None"),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("tail".to_string()))),
                },
                body: PureExpr::LogicFnCall {
                    name: "Some".to_string(),
                    args: vec![PureExpr::LogicFnCall {
                        name: "Box::new".to_string(),
                        args: vec![deep_model_call(PureExpr::Deref(Arc::new(var("tail"))))],
                    }],
                },
            },
        ],
    };
    let n = node("deep_model", &["self"], body);
    assert!(
        is_structurally_recursive(&n),
        "List::deep_model must be accepted"
    );
}

/// mixed.rs `Expr::deep_model`: matches `self`, binds `e1`/`e2` under a
/// constructor+tuple pattern, recurses via `(*e1).deep_model()`. ACCEPT.
#[test]
fn expr_deep_model_is_structurally_recursive() {
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Expr::Var".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: deep_model_call(var("v")), // v: V (generic), Deref-less — not a self-call
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Expr::Add".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("e1".to_string()),
                        Pattern::Binding("e2".to_string()),
                    ]))),
                },
                body: PureExpr::LogicFnCall {
                    name: "ExprDeepModel::Add".to_string(),
                    args: vec![
                        deep_model_call(PureExpr::Deref(Arc::new(var("e1")))),
                        deep_model_call(PureExpr::Deref(Arc::new(var("e2")))),
                    ],
                },
            },
        ],
    };
    let n = node("deep_model", &["self"], body);
    assert!(
        is_structurally_recursive(&n),
        "Expr::deep_model must be accepted"
    );
}

/// bug/459 `A::deep_model`: `*a.deep_model() + 1`. The receiver is the BARE
/// `Box<A>` binding `a` (the `Deref` is OUTSIDE the call), so the recursion is
/// mutual through `Box`'s impl, NOT a same-type self-call. REJECT.
#[test]
fn bug459_box_mediated_is_not_structurally_recursive() {
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "A::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Binding("a".to_string()))),
                },
                // *(a.deep_model()) + 1  -- Deref OUTSIDE the MethodCall.
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Deref(Arc::new(deep_model_call(var("a"))))),
                    trust_wp_core::formula::BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                ),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "A::Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ],
    };
    let n = node("deep_model", &["self"], body);
    assert!(
        !is_structurally_recursive(&n),
        "bug/459 Box-mediated recursion must NOT be structural (false-accept guard)"
    );
}

/// bug/1966 `nonstrictly(i)`: `match i { i => nonstrictly(i) }`. The arm binds
/// `i` as a plain (irrefutable) alias of the whole scrutinee — NON-strict — so
/// `nonstrictly(i)` does not decrease. REJECT.
#[test]
fn bug1966_nonstrictly_is_not_structurally_recursive() {
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("i")),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("i".to_string()),
            body: PureExpr::LogicFnCall {
                name: "nonstrictly".to_string(),
                args: vec![var("i")],
            },
        }],
    };
    let n = node("nonstrictly", &["i"], body);
    assert!(
        !is_structurally_recursive(&n),
        "nonstrictly (non-strict same-arg) must NOT be structural"
    );
}

/// bug/1966 `nested(n, _)`: `match n { Never(m) => nested(*m, nested(n, ())) }`.
/// Outer arg0 `*m` is strict, but the INNER `nested(n, ())` passes `n`
/// unchanged for arg0 → arg0 removed → no decreasing arg. REJECT.
#[test]
fn bug1966_nested_inner_call_breaks_decrease() {
    let inner = PureExpr::LogicFnCall {
        name: "nested".to_string(),
        args: vec![
            var("n"),
            PureExpr::LogicFnCall {
                name: "__trust_wp_tuple0".to_string(),
                args: vec![],
            },
        ],
    };
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("n")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Never".to_string(),
                inner: Some(Box::new(Pattern::Binding("m".to_string()))),
            },
            body: PureExpr::LogicFnCall {
                name: "nested".to_string(),
                args: vec![PureExpr::Deref(Arc::new(var("m"))), inner],
            },
        }],
    };
    let n = node("nested", &["n", "arg1"], body);
    assert!(
        !is_structurally_recursive(&n),
        "nested inner non-decreasing self-call must break structural decrease"
    );
}

/// `me(self) { self.me() }` passes `self` unchanged → not strict. REJECT.
#[test]
fn same_arg_identity_is_not_structurally_recursive() {
    let body = PureExpr::LogicFnCall {
        name: "me".to_string(),
        args: vec![var("self")],
    };
    let n = node("me", &["self"], body);
    assert!(
        !is_structurally_recursive(&n),
        "identity self-pass must not be structural"
    );
}

/// Zero-arg `falso()` has no argument to decrease. REJECT.
#[test]
fn zero_arg_is_not_structurally_recursive() {
    let body = PureExpr::LogicFnCall {
        name: "falso".to_string(),
        args: vec![],
    };
    let n = node("falso", &[], body);
    assert!(
        !is_structurally_recursive(&n),
        "zero-arg recursion must not be structural"
    );
}

/// A genuinely-decreasing direct recursion `f(x) { ... f(child(x)) }` where the
/// argument is a strict projection of a matched scrutinee. ACCEPT.
#[test]
fn direct_strict_subterm_recursion_is_structural() {
    // match x { Cons(h) => f(*h) }  with f a normal logic fn.
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Cons".to_string(),
                inner: Some(Box::new(Pattern::Binding("h".to_string()))),
            },
            body: PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![PureExpr::Deref(Arc::new(var("h")))],
            },
        }],
    };
    let n = node("f", &["x"], body);
    assert!(
        is_structurally_recursive(&n),
        "strict-subterm direct recursion must be structural"
    );
}
