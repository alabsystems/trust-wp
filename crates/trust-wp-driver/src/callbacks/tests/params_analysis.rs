// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn projected_write_substitution_repair_follows_synthetic_local_aliases() {
    let tuple2_name = tuple_logic_fn_name(2);
    let get_0_name = tuple_field_logic_fn_name(0);

    let mut substitutions = std::collections::HashMap::from([(
        "p".to_string(),
        PureExpr::LogicFnCall {
            name: tuple2_name.clone(),
            args: vec![PureExpr::Int(2), PureExpr::Int(3)],
        },
    )]);
    let call_assumptions = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("$call_7".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: tuple2_name.clone(),
                args: vec![PureExpr::Int(2), PureExpr::Int(3)],
            }),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: get_0_name,
                args: vec![PureExpr::Var("$local_7".into(), None)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(4)),
        ),
    ];

    let applied = apply_projected_writes_to_substitutions(&mut substitutions, &call_assumptions);

    assert_eq!(
        applied, 1,
        "expected projected write to update the tuple substitution"
    );
    assert_eq!(
        substitutions.get("p"),
        Some(&PureExpr::LogicFnCall {
            name: tuple2_name,
            args: vec![PureExpr::Int(4), PureExpr::Int(3)],
        }),
        "synthetic _local_N projected write should update the corresponding source substitution",
    );
}

// =========================================================================
// analyze_call_assumptions tests (#530)
// =========================================================================

#[test]
fn test_analyze_fn_postcondition_is_safe() {
    // (*f).postcondition(arg, result) — Fn::call is immutable, safe for identity
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("f".into(), None)))),
        method: "postcondition".into(),
        args: vec![
            PureExpr::Var("arg".into(), None),
            PureExpr::Var("result".into(), None),
        ],
    }];
    let (has_mutating, receivers) = analyze_call_assumptions(&assumptions);
    assert!(!has_mutating);
    assert!(receivers.contains("f"));
}

#[test]
fn test_analyze_fn_mut_postcondition_blocks_synthesis() {
    // (*f).postcondition_mut(arg, ^f, result) — FnMut modifies param
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("f".into(), None)))),
        method: "postcondition_mut".into(),
        args: vec![
            PureExpr::Var("arg".into(), None),
            PureExpr::Final(Arc::new(PureExpr::Var("f".into(), None))),
            PureExpr::Var("result".into(), None),
        ],
    }];
    let (has_mutating, _) = analyze_call_assumptions(&assumptions);
    assert!(has_mutating);
}

#[test]
fn test_analyze_fn_once_postcondition_blocks_synthesis() {
    // f.postcondition_once(arg, result) — FnOnce consumes param
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".into(), None)),
        method: "postcondition_once".into(),
        args: vec![
            PureExpr::Var("arg".into(), None),
            PureExpr::Var("result".into(), None),
        ],
    }];
    let (has_mutating, _) = analyze_call_assumptions(&assumptions);
    assert!(has_mutating);
}

#[test]
fn test_analyze_non_method_call_blocks_synthesis() {
    // BinOp assumption (e.g., "x > 0") — conservatively unsafe (#530 finding 1)
    let assumptions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let (has_mutating, receivers) = analyze_call_assumptions(&assumptions);
    assert!(has_mutating);
    assert!(receivers.is_empty());
}

#[test]
fn test_analyze_receiver_extraction_deref_var() {
    // (*f).postcondition(arg, result) — receiver is Deref(Var("f"))
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("f".into(), None)))),
        method: "postcondition".into(),
        args: vec![
            PureExpr::Var("arg".into(), None),
            PureExpr::Var("result".into(), None),
        ],
    }];
    let (_, receivers) = analyze_call_assumptions(&assumptions);
    assert_eq!(receivers.len(), 1);
    assert!(receivers.contains("f"));
}

#[test]
fn test_analyze_receiver_extraction_bare_var() {
    // f.postcondition_once(arg, result) — receiver is Var("f") (FnOnce style)
    // Note: postcondition is safe, postcondition_once is not. Using precondition
    // here since it's also a closure-spec method.
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("g".into(), None)),
        method: "precondition".into(),
        args: vec![PureExpr::Var("arg".into(), None)],
    }];
    let (has_mutating, receivers) = analyze_call_assumptions(&assumptions);
    assert!(!has_mutating);
    assert_eq!(receivers.len(), 1);
    assert!(receivers.contains("g"));
}

#[test]
fn test_analyze_multiple_receivers() {
    // Two different closure params: (*f).postcondition and (*g).postcondition
    let assumptions = vec![
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("f".into(), None)))),
            method: "postcondition".into(),
            args: vec![
                PureExpr::Var("a".into(), None),
                PureExpr::Var("r1".into(), None),
            ],
        },
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("g".into(), None)))),
            method: "postcondition".into(),
            args: vec![
                PureExpr::Var("b".into(), None),
                PureExpr::Var("r2".into(), None),
            ],
        },
    ];
    let (has_mutating, receivers) = analyze_call_assumptions(&assumptions);
    assert!(!has_mutating);
    assert_eq!(receivers.len(), 2);
    assert!(receivers.contains("f"));
    assert!(receivers.contains("g"));
}

#[test]
fn test_analyze_empty_assumptions() {
    let (has_mutating, receivers) = analyze_call_assumptions(&[]);
    assert!(!has_mutating);
    assert!(receivers.is_empty());
}

// =========================================================================
// extract_old_deref_vars tests
// =========================================================================

#[test]
fn test_extract_old_deref_vars_simple() {
    let mut vars = std::collections::HashSet::new();
    let expr = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".into(),
        None,
    )))));

    crate::callbacks::helpers::extract_old_deref_vars(&expr, &mut vars);

    assert_eq!(vars.len(), 1);
    assert!(vars.contains("x"));
}

#[test]
fn test_extract_old_deref_vars_in_triggers_and_match_arms() {
    let mut vars = std::collections::HashSet::new();
    let expr = PureExpr::Forall {
        var: "i".into(),
        var_sort: None,
        body: Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("xs".into(), None)),
            arms: vec![trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Wildcard,
                body: PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                    "body_var".into(),
                    None,
                ))))),
            }],
        }),
        triggers: vec![vec![PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("trigger_var".into(), None),
        ))))]],
    };

    crate::callbacks::helpers::extract_old_deref_vars(&expr, &mut vars);

    assert_eq!(vars.len(), 2);
    assert!(vars.contains("trigger_var"));
    assert!(vars.contains("body_var"));
}

// =========================================================================
// extract_final_vars tests
// =========================================================================

#[test]
fn test_extract_final_vars_simple() {
    let mut vars = std::collections::HashSet::new();
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".into(), None)));
    extract_final_vars(&expr, &mut vars);
    assert_eq!(vars.len(), 1);
    assert!(vars.contains("x"));
}

#[test]
fn test_extract_final_vars_nested_in_binop() {
    let mut vars = std::collections::HashSet::new();
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var("a".into(), None)))),
        BinOp::Eq,
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var("b".into(), None)))),
    );
    extract_final_vars(&expr, &mut vars);
    assert_eq!(vars.len(), 2);
    assert!(vars.contains("a"));
    assert!(vars.contains("b"));
}

#[test]
fn test_extract_final_vars_no_finals() {
    let mut vars = std::collections::HashSet::new();
    let expr = PureExpr::Var("x".into(), None);
    extract_final_vars(&expr, &mut vars);
    assert!(vars.is_empty());
}

// =========================================================================
// OpenSelf scoping tests (#519)
// =========================================================================

#[test]
fn test_parent_module_qualified_path() {
    assert_eq!(parent_module("crate::specs::max"), "crate::specs");
}

#[test]
fn test_parent_module_deeply_nested() {
    assert_eq!(parent_module("crate::a::b::c::func"), "crate::a::b::c");
}

#[test]
fn test_parent_module_top_level() {
    assert_eq!(parent_module("max"), "");
}

#[test]
fn test_parent_module_single_module() {
    assert_eq!(parent_module("crate::max"), "crate");
}
