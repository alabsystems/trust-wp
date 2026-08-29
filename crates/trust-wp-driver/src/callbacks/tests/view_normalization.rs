// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- normalize_view_fn_calls tests (#2209) ---

#[test]
fn test_normalize_view_fn_calls_view_single_arg() {
    // LogicFnCall("view", [Var("x")]) → View(Var("x"))
    let input = PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)))
    );
}

#[test]
fn test_normalize_view_fn_calls_final_value_single_arg() {
    // LogicFnCall("final_value", [Var("x")]) → Final(Var("x"))
    let input = PureExpr::LogicFnCall {
        name: "final_value".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)))
    );
}

#[test]
fn test_normalize_view_fn_calls_non_view_single_arg_preserved() {
    // LogicFnCall("other_fn", [Var("x")]) stays unchanged
    let input = PureExpr::LogicFnCall {
        name: "other_fn".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let expected = input.clone();
    let result = normalize_view_fn_calls(input);
    assert_eq!(result, expected);
}

#[test]
fn test_normalize_view_fn_calls_multi_arg_view_not_transformed() {
    // LogicFnCall("view", [a, b]) should NOT become View — only single-arg view()
    let input = PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("b".to_string(), None),
        ],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![
                PureExpr::Var("a".to_string(), None),
                PureExpr::Var("b".to_string(), None),
            ],
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_nested_view_in_binop() {
    // BinOp(LogicFnCall("view", [a]), Add, LogicFnCall("view", [b]))
    // → BinOp(View(a), Add, View(b))
    let input = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("a".to_string(), None)],
        }),
        BinOp::Add,
        Arc::new(PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("b".to_string(), None)],
        }),
    );
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "a".to_string(),
                None
            )))),
            BinOp::Add,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "b".to_string(),
                None
            )))),
        )
    );
}

#[test]
fn test_normalize_view_fn_calls_nested_view_of_view() {
    // LogicFnCall("view", [LogicFnCall("view", [x])]) → View(View(x))
    let input = PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "x".to_string(),
            None
        )))))
    );
}

#[test]
fn test_collapse_idempotent_views_nested_view_of_view() {
    let input = PureExpr::View(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))));
    let result = collapse_idempotent_views(input);
    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)))
    );
}

#[test]
fn test_collapse_idempotent_views_collapses_triple_view_after_normalization() {
    let input = PureExpr::View(Arc::new(normalize_view_fn_calls(PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("xs".to_string(), None)],
        }],
    })));
    let result = collapse_idempotent_views(input);
    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::Var("xs".to_string(), None)))
    );
}

#[test]
fn test_collapse_idempotent_views_collapses_scalar_method_call_result() {
    let input = PureExpr::View(Arc::new(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "xs".to_string(),
            Some(ExprSort::Seq),
        )))),
        method: "len".to_string(),
        args: Vec::new(),
    }));
    let result = collapse_idempotent_views(input.clone());
    assert_eq!(
        result,
        match input {
            PureExpr::View(inner) => inner.as_ref().clone(),
            other => other,
        }
    );
}

#[test]
fn test_collapse_idempotent_views_collapses_scalar_logic_call_result() {
    let input = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "resolve".to_string(),
        args: vec![PureExpr::Var("pred".to_string(), Some(ExprSort::Bool))],
    }));
    let result = collapse_idempotent_views(input.clone());
    assert_eq!(
        result,
        match input {
            PureExpr::View(inner) => inner.as_ref().clone(),
            other => other,
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_passthrough_literals() {
    assert_eq!(
        normalize_view_fn_calls(PureExpr::Int(42)),
        PureExpr::Int(42)
    );
    assert_eq!(
        normalize_view_fn_calls(PureExpr::Bool(true)),
        PureExpr::Bool(true)
    );
    assert_eq!(
        normalize_view_fn_calls(PureExpr::Var("x".to_string(), None)),
        PureExpr::Var("x".to_string(), None)
    );
}

#[test]
fn test_normalize_view_fn_calls_unop_recurses() {
    // UnOp(Not, LogicFnCall("view", [x])) → UnOp(Not, View(x))
    let input = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
    );
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::UnOp(
            UnOp::Not,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "x".to_string(),
                None
            )))),
        )
    );
}

#[test]
fn test_normalize_view_fn_calls_ite_recurses() {
    let input = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("a".to_string(), None)],
        }),
        Arc::new(PureExpr::Var("b".to_string(), None)),
    );
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "a".to_string(),
                None
            )))),
            Arc::new(PureExpr::Var("b".to_string(), None)),
        )
    );
}

#[test]
fn test_normalize_view_fn_calls_method_call_recurses() {
    // MethodCall { receiver: LogicFnCall("view", [v]), method: "len" }
    // → MethodCall { receiver: View(v), method: "len" }
    let input = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("v".to_string(), None)],
        }),
        method: "len".to_string(),
        args: vec![],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None
            )))),
            method: "len".to_string(),
            args: vec![],
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_already_view_passthrough() {
    // View(x) stays View(x)
    let input = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
    let result = normalize_view_fn_calls(input.clone());
    assert_eq!(result, input);
}

#[test]
fn test_normalize_view_fn_calls_already_final_passthrough() {
    // Final(x) stays Final(x)
    let input = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));
    let result = normalize_view_fn_calls(input.clone());
    assert_eq!(result, input);
}

#[test]
fn test_normalize_view_fn_calls_forall_body_normalized() {
    let input = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(trust_wp_core::formula::ExprSort::Int),
        body: Arc::new(PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
        triggers: vec![],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::Forall {
            var: "x".to_string(),
            var_sort: Some(trust_wp_core::formula::ExprSort::Int),
            body: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "x".to_string(),
                None
            )))),
            triggers: vec![],
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_forall_triggers_normalized() {
    let input = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(trust_wp_core::formula::ExprSort::Int),
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "view".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }]],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::Forall {
            var: "x".to_string(),
            var_sort: Some(trust_wp_core::formula::ExprSort::Int),
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![vec![PureExpr::View(Arc::new(PureExpr::Var(
                "x".to_string(),
                None
            )))]],
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_match_arm_bodies_normalized() {
    let input = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("tag".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("bound".to_string()),
            body: PureExpr::LogicFnCall {
                name: "view".to_string(),
                args: vec![PureExpr::Var("value".to_string(), None)],
            },
        }],
    };

    let result = normalize_view_fn_calls(input);

    assert_eq!(
        result,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("tag".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("bound".to_string()),
                body: PureExpr::View(Arc::new(PureExpr::Var("value".to_string(), None))),
            }],
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_exists_body_normalized() {
    let input = PureExpr::Exists {
        var: "y".to_string(),
        var_sort: Some(trust_wp_core::formula::ExprSort::Int),
        body: Arc::new(PureExpr::LogicFnCall {
            name: "final_value".to_string(),
            args: vec![PureExpr::Var("y".to_string(), None)],
        }),
        triggers: vec![],
    };
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::Exists {
            var: "y".to_string(),
            var_sort: Some(trust_wp_core::formula::ExprSort::Int),
            body: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "y".to_string(),
                None
            )))),
            triggers: vec![],
        }
    );
}

#[test]
fn test_normalize_view_fn_calls_old_deref_recurse() {
    // Old(LogicFnCall("view", [x])) → Old(View(x))
    let input = PureExpr::Old(Arc::new(PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    }));
    let result = normalize_view_fn_calls(input);
    assert_eq!(
        result,
        PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "x".to_string(),
            None
        )))))
    );

    // Deref(LogicFnCall("view", [x])) → Deref(View(x))
    let input2 = PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    }));
    let result2 = normalize_view_fn_calls(input2);
    assert_eq!(
        result2,
        PureExpr::Deref(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "x".to_string(),
            None
        )))))
    );
}

// ── is_deref_precondition tests (#994 coverage gap) ──

#[test]
fn test_is_deref_precondition_positive_deref_mut() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("Vec::<i32>::deref_mut".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![],
    };
    assert!(is_deref_precondition(&expr));
}

#[test]
fn test_is_deref_precondition_positive_deref() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("Foo::deref".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![],
    };
    assert!(is_deref_precondition(&expr));
}

#[test]
fn test_is_deref_precondition_wrong_method_name() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("Foo::deref_mut".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![],
    };
    assert!(!is_deref_precondition(&expr));
}

#[test]
fn test_is_deref_precondition_receiver_not_deref() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("Vec::push".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![],
    };
    assert!(!is_deref_precondition(&expr));
}

#[test]
fn test_is_deref_precondition_non_method_call() {
    let expr = PureExpr::Var("deref_mut".to_string(), None);
    assert!(!is_deref_precondition(&expr));
}

#[test]
fn test_is_deref_precondition_receiver_not_var() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Int(42)),
        method: "precondition".to_string(),
        args: vec![],
    };
    assert!(!is_deref_precondition(&expr));
}
