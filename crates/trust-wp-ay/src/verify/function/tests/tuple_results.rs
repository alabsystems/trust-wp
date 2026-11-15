// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn user_defined_tuple_result_wraps_multi_field_constructor() {
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Pair".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x0".to_string()),
                        Pattern::Binding("x1".to_string()),
                    ]))),
                },
                body: and(eq(var("x0"), int(0)), eq(var("x1"), int(1))),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];
    let body = logic_fn_call("Pair", vec![int(0), int(1)]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "multi-field tuple constructor results should wrap as a datatype, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn user_defined_named_result_wraps_multi_field_constructor() {
    // The placed spelling of `Named { x, y }`: the driver's placement pass
    // drops the field-name metadata once the fields are at their declared
    // indices, and the encoder's one door refuses it otherwise
    // (verify::placement_gate).
    let ctor = "Named".to_string();
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: ctor.clone(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x".to_string()),
                        Pattern::Binding("y".to_string()),
                    ]))),
                },
                body: and(eq(var("x"), int(0)), eq(var("y"), int(1))),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];
    let body = logic_fn_call(&ctor, vec![int(0), int(1)]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "named constructor metadata should still wrap through the declared datatype, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn user_defined_tuple_result_wraps_tuple_lowered_body() {
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Pair".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x0".to_string()),
                        Pattern::Binding("x1".to_string()),
                    ]))),
                },
                body: and(eq(var("x0"), int(0)), eq(var("x1"), int(1))),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];
    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![int(0), int(1)]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "tuple-lowered multi-field results should re-wrap into the constructor datatype, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn user_defined_tuple_result_wraps_tuple_sorted_var_body() {
    let tuple_var = PureExpr::Var("pair".to_string(), Some(ExprSort::Tuple(2)));
    let tuple_get_0 = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_var.clone()]);
    let tuple_get_1 = logic_fn_call(&tuple_field_logic_fn_name(1), vec![tuple_var.clone()]);
    let requires = vec![eq(tuple_get_0, int(0)), eq(tuple_get_1, int(1))];
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Pair".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x0".to_string()),
                        Pattern::Binding("x1".to_string()),
                    ]))),
                },
                body: and(eq(var("x0"), int(0)), eq(var("x1"), int(1))),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&tuple_var)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "tuple-sorted result aliases should project tuple fields into the constructor datatype, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn tuple_default_postconditions_flow_through_tuple_lowered_result() {
    let tuple0 = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let call_1 = PureExpr::Var("call_1".to_string(), Some(ExprSort::Int));
    let call_2 = PureExpr::Var("call_2".to_string(), Some(ExprSort::Int));
    let default_fn = PureExpr::Var("core::default::Default::default".to_string(), None);
    let requires = vec![
        method_call_with_args(
            default_fn.clone(),
            "postcondition",
            vec![tuple0.clone(), call_1.clone()],
        ),
        method_call_with_args(
            default_fn.clone(),
            "postcondition",
            vec![tuple0.clone(), call_2.clone()],
        ),
    ];
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Tuple".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x0".to_string()),
                        Pattern::Binding("x1".to_string()),
                    ]))),
                },
                body: and(
                    method_call_with_args(
                        default_fn.clone(),
                        "postcondition",
                        vec![tuple0.clone(), var("x0")],
                    ),
                    method_call_with_args(default_fn, "postcondition", vec![tuple0, var("x1")]),
                ),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];
    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![call_1, call_2]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "tuple-lowered struct defaults should preserve per-field Default::postcondition facts, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn named_default_postconditions_flow_through_tuple_lowered_result() {
    let tuple0 = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let call_1 = PureExpr::Var("call_1".to_string(), Some(ExprSort::Int));
    let call_2 = PureExpr::Var("call_2".to_string(), None);
    let default_fn = PureExpr::Var("core::default::Default::default".to_string(), None);
    // The placed spelling of `Named { x, y }`: the driver's placement pass
    // drops the field-name metadata once the fields are at their declared
    // indices, and the encoder's one door refuses it otherwise
    // (verify::placement_gate).
    let ctor = "Named".to_string();
    let requires = vec![
        method_call_with_args(
            default_fn.clone(),
            "postcondition",
            vec![tuple0.clone(), call_1.clone()],
        ),
        method_call_with_args(
            default_fn.clone(),
            "postcondition",
            vec![tuple0.clone(), call_2.clone()],
        ),
    ];
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: ctor,
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x".to_string()),
                        Pattern::Binding("y".to_string()),
                    ]))),
                },
                body: and(
                    method_call_with_args(
                        default_fn.clone(),
                        "postcondition",
                        vec![tuple0.clone(), var("x")],
                    ),
                    method_call_with_args(default_fn, "postcondition", vec![tuple0, var("y")]),
                ),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];
    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![call_1, call_2]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "tuple-lowered named struct defaults should preserve per-field Default::postcondition facts, got {result:?}"
    );
}

/// Negative companion: without ghost, multiple ensures with unconstrained
/// `x` should fail because `x` could be any value including non-positive.
#[test]
#[timeout(30000)]
fn multiple_ensures_fail_without_ghost_context() {
    use trust_wp_core::formula::BinOp;

    let ensures = vec![
        eq(var("result"), int(42)),
        PureExpr::BinOp(Arc::new(var("result")), BinOp::Gt, Arc::new(int(0))),
    ];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without ghost context, unconstrained x should NOT satisfy \
         multiple ensures (result==42, result>0). Got: {result:?}"
    );
}

/// Ghost context combined with logic function AND multiple ensures.
/// This exercises the full interaction: ghost constrains via a logic
/// function, and the result must satisfy two independent postconditions.
#[test]
#[timeout(30000)]
fn ghost_context_logic_fn_and_multiple_ensures() {
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // ghost: double(x) == 42 constrains x to 21
    let ghost_facts = vec![eq(logic_fn_call("double", vec![var("x")]), int(42))];
    // ensures: result == 42 AND result > 0
    let ensures = vec![
        eq(var("result"), logic_fn_call("double", vec![var("x")])),
        eq(var("result"), int(42)),
    ];
    let body = logic_fn_call("double", vec![var("x")]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&double_fn))),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost(double(x)==42) + body=double(x) should verify both \
         ensures (result==double(x), result==42). Got: {result:?}"
    );
}
