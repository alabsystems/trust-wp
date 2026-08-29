// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for logic function recursion validation.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::{
    formula::{ExprSort, MatchArm, Pattern, PureExpr},
    logic::LogicMode,
};

use super::*;

fn call(name: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args: Vec::new(),
    }
}

/// Create a self-call that passes the same parameter variable back (identity pass-through).
fn identity_self_call(name: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args: vec![PureExpr::Var("n".to_string(), Some(ExprSort::Int))],
    }
}

fn make_recursion_node(
    name: &str,
    full_path: &str,
    has_variant: bool,
    body: PureExpr,
) -> LogicRecursionNode {
    LogicRecursionNode {
        full_path: full_path.to_string(),
        name: name.to_string(),
        params: vec!["n".to_string()],
        param_sort_hints: vec![Some(ExprSort::Int)],
        mode: LogicMode::Default,
        is_trait_method: false,
        body,
        body_text: String::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        raw_variants: if has_variant {
            vec!["n".to_string()]
        } else {
            Vec::new()
        },
        parsed_variants: if has_variant {
            vec![PureExpr::Var("n".to_string(), Some(ExprSort::Int))]
        } else {
            Vec::new()
        },
        variant_parse_errors: Vec::new(),
        body_parse_failed: false,
        deep_model_dispatch_targets: None,
    }
}

fn make_zero_param_node(name: &str, full_path: &str, body: PureExpr) -> LogicRecursionNode {
    LogicRecursionNode {
        full_path: full_path.to_string(),
        name: name.to_string(),
        params: Vec::new(),
        param_sort_hints: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        body,
        body_text: String::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        raw_variants: Vec::new(),
        parsed_variants: Vec::new(),
        variant_parse_errors: Vec::new(),
        body_parse_failed: false,
        deep_model_dispatch_targets: None,
    }
}

#[test]
fn test_detect_logic_fn_recursion_errors_mutual_cycle_without_variants() {
    let nodes = vec![
        make_recursion_node("f", "crate::f", false, call("g")),
        make_recursion_node("g", "crate::g", false, call("f")),
    ];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert_eq!(errors.len(), 2);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
    assert!(errors.iter().all(|e| e.message.contains("missing variant")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_unconditional_zero_arg_self_recursion_rejected() {
    // Unconditional zero-arg self-recursion rejected (#2686).
    // `fn falso() { falso() }` always calls itself — cannot terminate.
    let nodes = vec![make_zero_param_node("f", "crate::f", call("f"))];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("unconditional self-recursion"),
        "expected unconditional recursion error, got: {}",
        errors[0].message
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_unconditional_identity_self_recursion_rejected() {
    // Unconditional identity-passthrough self-recursion rejected (#2686).
    // `fn f(n) { f(n) }` passes the same arg — no progress, cannot terminate.
    let nodes = vec![make_recursion_node(
        "f",
        "crate::f",
        false,
        identity_self_call("f"),
    )];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("unconditional self-recursion"),
        "expected unconditional recursion error, got: {}",
        errors[0].message
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_unconditional_different_args_allowed() {
    // Unconditional self-recursion with structurally different args is allowed.
    // `fn fib(n) { fib(n-1) + fib(n-2) }` — args differ, may terminate via domain.
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![int_sub(int_var("n"), PureExpr::Int(1))],
        }),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![int_sub(int_var("n"), PureExpr::Int(2))],
        }),
    );
    let nodes = vec![make_recursion_node("f", "crate::f", false, body)];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert!(
        errors.is_empty(),
        "unconditional self-recursion with different args should be allowed: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_conditional_self_recursion_allowed() {
    // Conditional self-recursion without #[variant] is allowed (Creusot-compatible).
    // `fn f(n) { if n == 0 { true } else { f(n - 1) } }` — guarded by branch.
    let body = PureExpr::Ite(
        Arc::new(int_eq(int_var("n"), PureExpr::Int(0))),
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![int_sub(int_var("n"), PureExpr::Int(1))],
        }),
    );
    let nodes = vec![make_recursion_node("f", "crate::f", false, body)];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert!(
        errors.is_empty(),
        "conditional self-recursion should be allowed: {errors:?}"
    );
}

fn int_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Int))
}

fn int_eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(lhs),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(rhs),
    )
}

fn int_ge(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(lhs),
        trust_wp_core::formula::BinOp::Ge,
        Arc::new(rhs),
    )
}

fn int_sub(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(lhs),
        trust_wp_core::formula::BinOp::Sub,
        Arc::new(rhs),
    )
}

#[test]
fn test_detect_logic_fn_recursion_errors_self_cycle_with_variant_allowed() {
    let nodes = vec![make_recursion_node("f", "crate::f", true, call("f"))];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert!(errors.is_empty());
}

#[test]
fn test_detect_logic_fn_recursion_errors_uses_method_and_requires_edges() {
    let method_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
        method: "g".to_string(),
        args: Vec::new(),
    };
    let mut g = make_recursion_node("g", "crate::g", false, PureExpr::Bool(true));
    g.requires.push(call("f"));
    let nodes = vec![make_recursion_node("f", "crate::f", false, method_call), g];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert_eq!(errors.len(), 2);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_resolves_ufcs_suffix_paths() {
    let nodes = vec![
        make_recursion_node("f", "creusot_test::<T as Foo>::f", false, call("h")),
        make_recursion_node("g", "creusot_test::<i32 as Foo>::g", false, call("Self::f")),
        make_recursion_node("h", "creusot_test::h", false, call("<i32 as Foo>::g")),
    ];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert_eq!(errors.len(), 3);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_self_dispatch_to_trait_default_rejected() {
    // Self-dispatch via OpenSelf creates a conservative self-edge. The trait
    // default may dispatch back to the impl method, so accepting it as ordinary
    // structural self-recursion would false-accept Creusot's
    // default_function_non_open.rs should-fail case.
    let mut trait_f = make_recursion_node(
        "f",
        "creusot_test::inner::Foo::f",
        false,
        PureExpr::Bool(true),
    );
    trait_f.is_trait_method = true;
    trait_f.mode = LogicMode::OpenSelf;

    let impl_g = make_recursion_node(
        "g",
        "creusot_test::<impl inner::Foo for i32>::g",
        false,
        call("Self::f"),
    );

    let errors = detect_logic_fn_recursion_errors(&[trait_f, impl_g]);

    assert_eq!(errors.len(), 1);
    assert!(
        errors[0]
            .message
            .contains("self-dispatch through a trait default"),
        "expected trait-default self-dispatch diagnostic: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_open_trait_default_not_forced_recursive() {
    let mut trait_f = make_recursion_node(
        "f",
        "creusot_test::inner::Foo::f",
        false,
        PureExpr::Bool(true),
    );
    trait_f.is_trait_method = true;
    trait_f.mode = LogicMode::Open;

    let impl_g = make_recursion_node(
        "g",
        "creusot_test::<impl inner::Foo for i32>::g",
        false,
        call("Self::f"),
    );

    let errors = detect_logic_fn_recursion_errors(&[trait_f, impl_g]);

    assert!(errors.is_empty());
}

#[test]
fn test_detect_logic_fn_recursion_errors_default_trait_default_not_forced_recursive() {
    let mut trait_f = make_recursion_node(
        "f",
        "creusot_test::inner::Foo::f",
        false,
        PureExpr::Bool(true),
    );
    trait_f.is_trait_method = true;
    trait_f.mode = LogicMode::Default;

    let impl_g = make_recursion_node(
        "g",
        "creusot_test::<impl inner::Foo for ()>::g",
        false,
        call("Self::f"),
    );

    let errors = detect_logic_fn_recursion_errors(&[trait_f, impl_g]);

    assert!(
        errors.is_empty(),
        "default-mode trait defaults should not force recursion: {errors:?}"
    );
}

/// Verify that `LogicMode::Prophetic` trait methods don't create false
/// conservative self-dispatch edges (same fix as Default mode, #1510).
#[test]
fn test_detect_logic_fn_recursion_errors_prophetic_trait_not_forced_recursive() {
    let mut trait_f = make_recursion_node(
        "f",
        "creusot_test::inner::Foo::f",
        false,
        PureExpr::Bool(true),
    );
    trait_f.is_trait_method = true;
    trait_f.mode = LogicMode::Prophetic;

    let impl_g = make_recursion_node(
        "g",
        "creusot_test::<impl inner::Foo for ()>::g",
        false,
        call("Self::f"),
    );

    let errors = detect_logic_fn_recursion_errors(&[trait_f, impl_g]);

    assert!(
        errors.is_empty(),
        "prophetic-mode trait defaults should not force recursion: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_ignores_field_method_name_collision() {
    let mut view_impl = make_recursion_node(
        "view",
        "creusot_test::<Formula as creusot_std::View>::view",
        false,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self_vec".to_string(), None)),
            method: "view".to_string(),
            args: Vec::new(),
        },
    );
    view_impl.body_text = "self.vec.view()".to_string();

    let nodes = [view_impl];
    let graph = build_logic_call_graph(&nodes);

    assert!(
        !has_self_edge(&graph, 0),
        "non-self field method calls must not create self-recursion edges: {graph:?}"
    );

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert!(
        errors.is_empty(),
        "non-self method calls should not create self-recursion edges: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_detects_calls_in_statement_blocks() {
    let f = make_recursion_node("f", "creusot_test::f", false, call("g"));
    let mut g = make_recursion_node("g", "creusot_test::g", false, PureExpr::Bool(true));
    g.body_text = "if x { f(); }".to_string();

    let errors = detect_logic_fn_recursion_errors(&[f, g]);

    assert_eq!(errors.len(), 2);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_detects_self_method_calls_in_text() {
    let f = make_recursion_node("f", "creusot_test::f", false, call("g"));
    let mut g = make_recursion_node("g", "creusot_test::g", false, PureExpr::Bool(true));
    g.body_text = "if cond { self.f(); }".to_string();

    let errors = detect_logic_fn_recursion_errors(&[f, g]);

    assert_eq!(errors.len(), 2);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_recovers_statement_ufcs_edges() {
    let mut f = make_recursion_node(
        "f",
        "creusot_test::<T as Foo>::f",
        false,
        PureExpr::Bool(true),
    );
    f.body_text = "{ h(); }".to_string();
    let g = make_recursion_node("g", "creusot_test::<i32 as Foo>::g", false, call("Self::f"));
    let mut h = make_recursion_node("h", "creusot_test::h", false, PureExpr::Bool(true));
    h.body_text = "{ < i32 as Foo > :: g(); }".to_string();

    let errors = detect_logic_fn_recursion_errors(&[f, g, h]);

    assert_eq!(errors.len(), 3);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_contract_recursion_from_statement_calls() {
    let mut with_proof_assert = make_recursion_node(
        "with_proof_assert",
        "creusot_test::with_proof_assert",
        false,
        PureExpr::Bool(true),
    );
    with_proof_assert.body_text = "{ proof_assert! { x == f1() } }".to_string();

    let mut f1 = make_recursion_node("f1", "creusot_test::f1", false, PureExpr::Int(3));
    f1.body_text = "{ with_proof_assert(5); 3 }".to_string();

    let mut with_requires = make_recursion_node(
        "with_requires",
        "creusot_test::with_requires",
        false,
        PureExpr::Bool(true),
    );
    with_requires.requires.push(call("f2"));

    let mut f2 = make_recursion_node("f2", "creusot_test::f2", false, PureExpr::Int(3));
    f2.body_text = "{ with_requires(5); 3 }".to_string();

    let errors = detect_logic_fn_recursion_errors(&[with_proof_assert, f1, with_requires, f2]);

    assert_eq!(errors.len(), 4);
    assert!(errors
        .iter()
        .all(|e| e.message.contains("mutual recursion")));
}

#[test]
fn test_detect_logic_fn_recursion_errors_default_impl_dispatch_loop_from_parsed_edges() {
    // Mirrors should_fail/terminates/loop_through_default_impl.rs:
    // default impl f -> h -> concrete impl g -> Self::f. The h -> g qualified
    // path may not resolve structurally, so the recursion checker must still
    // use raw parsed call names to fail closed.
    let f = make_recursion_node("f", "creusot_test::<T as Foo>::f", false, call("h"));
    let h = make_recursion_node("h", "creusot_test::h", false, call("<i32 as Foo>::g"));
    let default_g = make_recursion_node(
        "g",
        "creusot_test::<T as Foo>::g",
        false,
        PureExpr::Bool(true),
    );
    let g = make_recursion_node(
        "g",
        "creusot_test::<impl Foo for i32>::g",
        false,
        call("Self::f"),
    );

    let errors = detect_logic_fn_recursion_errors(&[f, h, default_g, g]);

    assert_eq!(errors.len(), 3);
    assert!(
        errors
            .iter()
            .all(|error| error.message.contains("trait method dispatch")),
        "expected trait dispatch diagnostics: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_default_impl_dispatch_loop_is_name_independent() {
    let default_read = make_recursion_node(
        "read_default",
        "creusot_test::<T as Store>::read_default",
        false,
        call("dispatch_bridge"),
    );
    let dispatch_bridge = make_recursion_node(
        "dispatch_bridge",
        "creusot_test::dispatch_bridge",
        false,
        call("<i32 as Store>::write_impl"),
    );
    let concrete_write = make_recursion_node(
        "write_impl",
        "creusot_test::<impl Store for i32>::write_impl",
        false,
        call("Self::read_default"),
    );

    let errors = detect_logic_fn_recursion_errors(&[default_read, dispatch_bridge, concrete_write]);

    assert_eq!(errors.len(), 3);
    assert!(
        errors.iter().all(|error| {
            error.message.contains("trait method dispatch")
                || error.message.contains("mutual recursion")
        }),
        "expected trait dispatch or mutual-recursion diagnostics: {errors:?}"
    );
}

#[test]
fn test_analyze_logic_fn_recursion_accepts_variant_gated_mutual_pair() {
    let mut f = make_recursion_node(
        "is_even",
        "crate::is_even",
        true,
        PureExpr::Ite(
            Arc::new(int_eq(int_var("n"), PureExpr::Int(0))),
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::LogicFnCall {
                name: "is_odd".to_string(),
                args: vec![int_sub(int_var("n"), PureExpr::Int(1))],
            }),
        ),
    );
    f.raw_variants = vec!["n".to_string()];
    f.parsed_variants = vec![int_var("n")];
    f.requires.push(int_ge(int_var("n"), PureExpr::Int(0)));

    let mut g = make_recursion_node(
        "is_odd",
        "crate::is_odd",
        true,
        PureExpr::Ite(
            Arc::new(int_eq(int_var("n"), PureExpr::Int(0))),
            Arc::new(PureExpr::Bool(false)),
            Arc::new(PureExpr::LogicFnCall {
                name: "is_even".to_string(),
                args: vec![int_sub(int_var("n"), PureExpr::Int(1))],
            }),
        ),
    );
    g.raw_variants = vec!["n".to_string()];
    g.parsed_variants = vec![int_var("n")];
    g.requires.push(int_ge(int_var("n"), PureExpr::Int(0)));

    let analysis = analyze_logic_fn_recursion_nodes(&[f, g]);

    assert!(
        analysis.errors.is_empty(),
        "supported mutual pair should not produce recursion errors: {:?}",
        analysis.errors
    );
    assert_eq!(
        analysis.supported_scc_members,
        HashSet::from(["crate::is_even".to_string(), "crate::is_odd".to_string()]),
    );
}

#[test]
fn test_analyze_logic_fn_recursion_rejects_text_only_variant_edge() {
    let mut f = make_recursion_node("f", "crate::f", true, PureExpr::Bool(true));
    f.body_text = "g(n - 1)".to_string();
    let mut g = make_recursion_node("g", "crate::g", true, PureExpr::Bool(true));
    g.body_text = "f(n - 1)".to_string();

    let analysis = analyze_logic_fn_recursion_nodes(&[f, g]);

    assert_eq!(analysis.errors.len(), 2);
    assert!(analysis
        .errors
        .iter()
        .all(|error| error.message.contains("text")));
}

#[test]
fn test_analyze_logic_fn_recursion_rejects_match_only_descent() {
    let mut f = make_recursion_node(
        "f",
        "crate::f",
        true,
        PureExpr::Match {
            scrutinee: Arc::new(int_var("n")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(PureExpr::Int(0)),
                    body: PureExpr::Bool(true),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::LogicFnCall {
                        name: "g".to_string(),
                        args: vec![int_sub(int_var("n"), PureExpr::Int(1))],
                    },
                },
            ],
        },
    );
    f.requires.push(int_ge(int_var("n"), PureExpr::Int(0)));

    let mut g = make_recursion_node(
        "g",
        "crate::g",
        true,
        PureExpr::Match {
            scrutinee: Arc::new(int_var("n")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(PureExpr::Int(0)),
                    body: PureExpr::Bool(false),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::LogicFnCall {
                        name: "f".to_string(),
                        args: vec![int_sub(int_var("n"), PureExpr::Int(1))],
                    },
                },
            ],
        },
    );
    g.requires.push(int_ge(int_var("n"), PureExpr::Int(0)));

    let analysis = analyze_logic_fn_recursion_nodes(&[f, g]);

    assert_eq!(analysis.errors.len(), 2);
    assert!(analysis
        .errors
        .iter()
        .all(|error| error.message.contains("match-based")));
}

#[test]
fn test_collect_logic_references_from_text_ignores_comments_and_strings() {
    let mut names = HashSet::new();
    let text = r#"
        {
            // fake_comment_call();
            let _ = "fake_string_call()";
            real_call();
        }
    "#;

    collect_logic_references_from_text(text, &mut names);

    assert!(
        names.contains("real_call"),
        "expected concrete call in code region to be collected"
    );
    assert!(
        !names.contains("fake_comment_call"),
        "comment text must not produce recursion edges"
    );
    assert!(
        !names.contains("fake_string_call"),
        "string literals must not produce recursion edges"
    );
}

#[test]
fn test_collect_logic_references_from_text_ignores_field_method_collision() {
    let mut names = HashSet::new();
    collect_logic_references_from_text("self.vec.view()", &mut names);

    assert!(
        !names.contains("view"),
        "field method calls must not create recursion edges: {names:?}"
    );
}

#[test]
fn test_collect_logic_references_visits_triggers_patterns_and_wrapped_self_dispatch() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
            arms: vec![MatchArm {
                pattern: Pattern::Literal(PureExpr::LogicFnCall {
                    name: "pattern_logic".to_string(),
                    args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
                }),
                body: PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
                        PureExpr::Final(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                            "self".to_string(),
                            None,
                        ))))),
                    ))))),
                    method: "dispatch_logic".to_string(),
                    args: vec![PureExpr::LogicFnCall {
                        name: "body_logic".to_string(),
                        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
                    }],
                },
            }],
        }),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "trigger_logic".to_string(),
            args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
        }]],
    };

    let mut names = HashSet::new();
    collect_logic_references(&expr, &mut names);

    assert_eq!(
        names,
        HashSet::from([
            "pattern_logic".to_string(),
            "dispatch_logic".to_string(),
            "body_logic".to_string(),
            "trigger_logic".to_string(),
        ])
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_ignores_false_text_cycle_from_comments() {
    let f = make_recursion_node("f", "crate::f", false, call("g"));
    let mut g = make_recursion_node("g", "crate::g", false, PureExpr::Bool(true));
    g.body_text = r#"
        {
            // f();
            /* f(); */
            let _ = "f()";
            true
        }
    "#
    .to_string();

    let errors = detect_logic_fn_recursion_errors(&[f, g]);

    assert!(
        errors.is_empty(),
        "comment/string-only text references should not create recursion cycles: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_ignores_constructor_name_edges() {
    let some_logic = make_recursion_node("Some", "crate::Some", false, call("g"));
    let mut g = make_recursion_node("g", "crate::g", false, PureExpr::Bool(true));
    g.body_text = r#"
        {
            let _ = Some(1);
            let _ = Ok(2);
            let _ = Err(3);
            let _ = None::<i32>;
            true
        }
    "#
    .to_string();

    let errors = detect_logic_fn_recursion_errors(&[some_logic, g]);

    assert!(
        errors.is_empty(),
        "constructor names should not be interpreted as logic-call edges: {errors:?}"
    );
}

#[test]
fn test_resolve_logic_call_targets_suffix_must_be_segment_boundary() {
    // A qualified call name like "a::f" should NOT match "crate::ba::f" via
    // bare `ends_with` — it must match at a `::` boundary.
    let f_in_ba = make_recursion_node("f", "crate::ba::f", false, PureExpr::Bool(true));
    let g = make_recursion_node("g", "crate::g", false, PureExpr::Bool(true));

    // g's body text references "a::f()" — should NOT resolve to "crate::ba::f".
    let mut g_with_text = g;
    g_with_text.body_text = "a::f()".to_string();

    let errors = detect_logic_fn_recursion_errors(&[f_in_ba, g_with_text]);

    assert!(
        errors.is_empty(),
        "qualified suffix 'a::f' must not match 'crate::ba::f' across segment boundary: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_ignores_macro_names_in_text() {
    // A logic function named "assert" (hypothetical) should not be matched
    // when body text contains assert!(...) — the `!` filter already handles
    // macros, but "assert(" without `!` could appear after sanitization.
    // The keyword blocklist should filter it.
    let assert_fn = make_recursion_node(
        "assert",
        "crate::specs::assert",
        false,
        PureExpr::Bool(true),
    );
    let mut g = make_recursion_node("g", "crate::g", false, PureExpr::Bool(true));
    g.body_text = r#"
        {
            assert(x > 0);
            println(y);
            format(z);
            true
        }
    "#
    .to_string();

    let errors = detect_logic_fn_recursion_errors(&[assert_fn, g]);

    assert!(
        errors.is_empty(),
        "blocklisted macro-like names must not create false call-graph edges: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_no_false_positive_from_unrelated_name_collision() {
    // f calls g via AST. g's text mentions "f(" in a real-code context but
    // g does NOT actually call f — only uses a local variable named `f`.
    // Since the AST-based collector doesn't find a call to f, only the text
    // parser picks it up. With singleton short-name fallback, this creates
    // a spurious cycle.
    //
    // This test documents the known limitation: text-based extraction is
    // conservative and MAY create false edges for true code references.
    // The keyword blocklist and comment/string stripping reduce but don't
    // eliminate this. The test verifies the detection still works correctly
    // (i.e., the cycle IS detected) — this is intentionally conservative.
    let f = make_recursion_node("f", "crate::f", false, call("g"));
    let mut g = make_recursion_node("g", "crate::g", false, PureExpr::Bool(true));
    g.body_text = "let result = f(x);".to_string();

    let errors = detect_logic_fn_recursion_errors(&[f, g]);

    // The text parser conservatively treats "f(" as a call reference.
    // This is intentional — false negatives (missing real cycles) are worse
    // than false positives (reporting spurious cycles) for soundness.
    assert!(
        !errors.is_empty(),
        "text-based 'f(' reference should conservatively create a cycle edge"
    );
}

/// Helper to create a parse-failed node that uses text-only body scanning.
fn make_parse_failed_node(name: &str, full_path: &str, body_text: &str) -> LogicRecursionNode {
    LogicRecursionNode {
        full_path: full_path.to_string(),
        name: name.to_string(),
        params: vec!["n".to_string()],
        param_sort_hints: vec![Some(ExprSort::Int)],
        mode: LogicMode::Default,
        is_trait_method: false,
        body: PureExpr::Bool(true),
        body_text: body_text.to_string(),
        requires: Vec::new(),
        ensures: Vec::new(),
        raw_variants: Vec::new(),
        parsed_variants: Vec::new(),
        variant_parse_errors: Vec::new(),
        body_parse_failed: true,
        deep_model_dispatch_targets: None,
    }
}

#[test]
fn test_parse_failed_self_recursive_node_rejected_without_variant() {
    // Simulates bug/1966.rs sneak/nonstrictly patterns: the body is too complex
    // to parse but contains self-recursive calls detected via text scanning.
    // Parse-failed nodes must be rejected when recursive without #[variant].
    let sneak = make_parse_failed_node(
        "sneak",
        "crate::sneak",
        "match n { Never(m) => sneak(*m), } sneak(n)",
    );

    let errors = detect_logic_fn_recursion_errors(&[sneak]);

    assert_eq!(errors.len(), 1, "expected exactly one error: {errors:?}");
    assert!(
        errors[0].message.contains("unparseable body"),
        "error should mention unparseable body: {}",
        errors[0].message
    );
}

#[test]
fn test_parse_failed_self_recursive_node_accepted_with_variant() {
    // A parse-failed node WITH a #[variant] should not be rejected —
    // the variant provides a termination argument even without parsed body.
    let mut node = make_parse_failed_node("f", "crate::f", "match n { 0 => true, _ => f(n - 1) }");
    node.raw_variants = vec!["n".to_string()];

    let errors = detect_logic_fn_recursion_errors(&[node]);

    assert!(
        errors.is_empty(),
        "parse-failed node with variant should not produce errors: {errors:?}"
    );
}

#[test]
fn test_parse_failed_non_recursive_node_no_error() {
    // A parse-failed node that does NOT have self-recursion should pass.
    let node = make_parse_failed_node("f", "crate::f", "if n > 0 { n * 2 } else { 0 }");

    let errors = detect_logic_fn_recursion_errors(&[node]);

    assert!(
        errors.is_empty(),
        "non-recursive parse-failed node should not produce errors: {errors:?}"
    );
}

#[test]
fn test_parse_failed_mutual_recursion_detected() {
    // Two parse-failed nodes that call each other via text scanning
    // should be detected as mutual recursion. Uses match-arm style body
    // text to verify the `=>` fix in the text scanner.
    let f = make_parse_failed_node("f", "crate::f", "match n { 0 => true, _ => g(n - 1) }");
    let g = make_parse_failed_node("g", "crate::g", "match n { 0 => false, _ => f(n - 1) }");

    let errors = detect_logic_fn_recursion_errors(&[f, g]);

    assert_eq!(
        errors.len(),
        2,
        "expected mutual recursion errors: {errors:?}"
    );
    assert!(
        errors
            .iter()
            .all(|e| e.message.contains("mutual recursion")),
        "errors should report mutual recursion: {errors:?}"
    );
}

#[test]
fn test_text_scanner_handles_match_arm_arrow() {
    // The text scanner must extract call names after `=>` in match arms.
    // Previously, `>` in `=>` was included in the backward scan (for generics),
    // producing `> g` instead of `g`.
    let mut names = HashSet::new();
    collect_logic_references_from_text("match n { 0 => true, _ => g(n - 1) }", &mut names);

    assert!(
        names.contains("g"),
        "text scanner should extract 'g' after `=>` in match arms: {names:?}"
    );
    assert!(
        !names.iter().any(|n| n.contains('>')),
        "text scanner should not include '>' in extracted names: {names:?}"
    );
}

fn int_add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(lhs),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(rhs),
    )
}

fn int_mod(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(lhs),
        trust_wp_core::formula::BinOp::Mod,
        Arc::new(rhs),
    )
}

/// Build a single-param Int self-recursive node with variant `x` (raw + parsed),
/// the given `#[requires]` clauses, and a body to derive self-edges from.
fn make_variant_x_node(
    name: &str,
    full_path: &str,
    requires: Vec<PureExpr>,
    body: PureExpr,
) -> LogicRecursionNode {
    LogicRecursionNode {
        full_path: full_path.to_string(),
        name: name.to_string(),
        params: vec!["x".to_string()],
        param_sort_hints: vec![Some(ExprSort::Int)],
        mode: LogicMode::Default,
        is_trait_method: false,
        body,
        body_text: String::new(),
        requires,
        ensures: Vec::new(),
        raw_variants: vec!["x".to_string()],
        parsed_variants: vec![int_var("x")],
        variant_parse_errors: Vec::new(),
        body_parse_failed: false,
        deep_model_dispatch_targets: None,
    }
}

fn x_var() -> PureExpr {
    int_var("x")
}

/// terminates/incorrect_variant.rs `incorrect_recursion_logic`: `#[variant(x)]`
/// but the even branch recurses on `x + 1`, which does NOT strictly decrease.
/// The old text heuristic accepted this (only `name(-` was rejected); the new
/// solver-backed obligation must return a definitive Failed -> REJECTED.
#[test]
fn test_analyze_logic_fn_recursion_rejects_incorrect_variant_increasing_self_call() {
    // if x == 0 { 0 }
    // else if x % 2 == 0 { f(x + 1) }   // <-- variant does NOT decrease
    // else { f(x - 1) }
    let body = PureExpr::Ite(
        Arc::new(int_eq(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Int(0)),
        Arc::new(PureExpr::Ite(
            Arc::new(int_eq(int_mod(x_var(), PureExpr::Int(2)), PureExpr::Int(0))),
            Arc::new(PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![int_add(x_var(), PureExpr::Int(1))],
            }),
            Arc::new(PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![int_sub(x_var(), PureExpr::Int(1))],
            }),
        )),
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);

    let analysis = analyze_logic_fn_recursion_nodes(&[node]);

    assert!(
        analysis
            .errors
            .iter()
            .any(|error| error.full_path == "crate::f"
                && error.message.contains("does not strictly")),
        "increasing-variant self-call must be rejected with a strict-decrease error: {:?}",
        analysis.errors
    );
}

/// Direct unit test of the solver-backed outcome: the `incorrect_variant` shape
/// yields `SelfVariantDecrease::Failed` (not Proven, not Unsupported).
#[test]
fn test_try_prove_self_variant_decrease_failed_on_increasing_edge() {
    let body = PureExpr::Ite(
        Arc::new(int_eq(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Int(0)),
        Arc::new(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![int_add(x_var(), PureExpr::Int(1))],
        }),
    );
    let nodes = vec![make_variant_x_node("f", "crate::f", Vec::new(), body)];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);

    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "x + 1 self-call must give a definitive Failed, got: {outcome:?}"
    );
}

/// should_succeed simple_trigger.rs `id`: `#[variant(i)] #[requires(i >= 0)]`,
/// `if i == 0 { 0 } else { id(i - 1) + 1 }`. Must NOT be newly rejected (the
/// `i - 1` edge strictly decreases under `i >= 0`); maps to Proven.
#[test]
fn test_try_prove_self_variant_decrease_proven_for_id() {
    let body = PureExpr::Ite(
        Arc::new(int_eq(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Int(0)),
        Arc::new(int_add(
            PureExpr::LogicFnCall {
                name: "id".to_string(),
                args: vec![int_sub(x_var(), PureExpr::Int(1))],
            },
            PureExpr::Int(1),
        )),
    );
    let nodes = vec![make_variant_x_node(
        "id",
        "crate::id",
        vec![int_ge(x_var(), PureExpr::Int(0))],
        body,
    )];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);

    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "id's `i - 1` self-call must prove decrease, got: {outcome:?}"
    );

    // End-to-end: id must not be newly rejected.
    let analysis = analyze_logic_fn_recursion_nodes(&nodes);
    assert!(
        analysis.errors.iter().all(|e| e.full_path != "crate::id"),
        "id must not be newly rejected: {:?}",
        analysis.errors
    );
}

/// should_succeed cell/02_fib.rs `fib`: `#[variant(i)]` with no `#[requires]`,
/// two self-calls `fib(i - 1)` and `fib(i - 2)` under `i > 1`. Both edges
/// strictly decrease under the implicit Int-variant precondition `i >= 0`;
/// maps to Proven and must NOT be newly rejected.
#[test]
fn test_fib_two_decreasing_self_calls_not_rejected() {
    let recurse = int_add(
        PureExpr::LogicFnCall {
            name: "fib".to_string(),
            args: vec![int_sub(x_var(), PureExpr::Int(1))],
        },
        PureExpr::LogicFnCall {
            name: "fib".to_string(),
            args: vec![int_sub(x_var(), PureExpr::Int(2))],
        },
    );
    let body = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(x_var()),
            trust_wp_core::formula::BinOp::Le,
            Arc::new(PureExpr::Int(0)),
        )),
        Arc::new(PureExpr::Int(0)),
        Arc::new(PureExpr::Ite(
            Arc::new(int_eq(x_var(), PureExpr::Int(1))),
            Arc::new(PureExpr::Int(1)),
            Arc::new(recurse),
        )),
    );
    let nodes = vec![make_variant_x_node("fib", "crate::fib", Vec::new(), body)];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "fib's `i - 1` and `i - 2` self-calls must prove decrease, got: {outcome:?}"
    );

    let analysis = analyze_logic_fn_recursion_nodes(&nodes);
    assert!(
        analysis.errors.iter().all(|e| e.full_path != "crate::fib"),
        "fib must not be newly rejected: {:?}",
        analysis.errors
    );
}

/// should_succeed termination/recursion_logic.rs `variant_int`:
/// `#[variant(x)] #[requires(x >= 0)]`, `if x == 0 { 0 } else { 1 + variant_int(x - 1) }`.
/// Maps to Proven; must NOT be newly rejected.
#[test]
fn test_variant_int_decreasing_self_call_not_rejected() {
    let body = PureExpr::Ite(
        Arc::new(int_eq(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Int(0)),
        Arc::new(int_add(
            PureExpr::Int(1),
            PureExpr::LogicFnCall {
                name: "variant_int".to_string(),
                args: vec![int_sub(x_var(), PureExpr::Int(1))],
            },
        )),
    );
    let nodes = vec![make_variant_x_node(
        "variant_int",
        "crate::variant_int",
        vec![int_ge(x_var(), PureExpr::Int(0))],
        body,
    )];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "variant_int's `x - 1` self-call must prove decrease, got: {outcome:?}"
    );

    let analysis = analyze_logic_fn_recursion_nodes(&nodes);
    assert!(
        analysis
            .errors
            .iter()
            .all(|e| e.full_path != "crate::variant_int"),
        "variant_int must not be newly rejected: {:?}",
        analysis.errors
    );
}

/// should_succeed filter_positive.rs `num_of_pos`: `#[variant(j - i)]` over
/// `(i: Int, j: Int, t: Seq<i32>)`, self-calls pass `(i, j - 1, t)`. The Seq
/// param / `t[j-1]@` path condition is outside the supported integer fragment,
/// so the decrease proof must FALL BACK (Unsupported, never reject) and
/// num_of_pos must NOT be newly rejected. Variant `j - i` is parsed but the
/// edges carry a Seq arg.
#[test]
fn test_num_of_pos_seq_param_falls_back_not_rejected() {
    // f(i, j - 1, t) self-edge (and a base case), variant j - i.
    let i = int_var("i");
    let j = int_var("j");
    let t = PureExpr::Var("t".to_string(), Some(ExprSort::Seq));
    let recurse = PureExpr::LogicFnCall {
        name: "num_of_pos".to_string(),
        args: vec![i.clone(), int_sub(j.clone(), PureExpr::Int(1)), t.clone()],
    };
    let body = PureExpr::Ite(
        Arc::new(int_ge(i.clone(), j.clone())),
        Arc::new(PureExpr::Int(0)),
        Arc::new(recurse),
    );
    let node = LogicRecursionNode {
        full_path: "crate::num_of_pos".to_string(),
        name: "num_of_pos".to_string(),
        params: vec!["i".to_string(), "j".to_string(), "t".to_string()],
        param_sort_hints: vec![
            Some(ExprSort::Int),
            Some(ExprSort::Int),
            Some(ExprSort::Seq),
        ],
        mode: LogicMode::Default,
        is_trait_method: false,
        body,
        body_text: String::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        raw_variants: vec!["j - i".to_string()],
        parsed_variants: vec![int_sub(j, i)],
        variant_parse_errors: Vec::new(),
        body_parse_failed: false,
        deep_model_dispatch_targets: None,
    };
    let nodes = vec![node];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);
    assert!(
        !matches!(outcome, SelfVariantDecrease::Failed(_)),
        "num_of_pos must not be definitively rejected; got: {outcome:?}"
    );

    let analysis = analyze_logic_fn_recursion_nodes(&nodes);
    assert!(
        analysis
            .errors
            .iter()
            .all(|e| e.full_path != "crate::num_of_pos"),
        "num_of_pos must not be newly rejected: {:?}",
        analysis.errors
    );
}

/// should_succeed bug/1538.rs `baz`: `#[logic]` with NO `#[variant]` and a
/// non-recursive quantifier body. It has no self-edge, so the new variant
/// branch is never reached and baz must not be rejected.
#[test]
fn test_baz_non_recursive_quantifier_body_not_rejected() {
    let node = LogicRecursionNode {
        full_path: "crate::baz".to_string(),
        name: "baz".to_string(),
        params: vec!["foo".to_string()],
        // `foo: Foo` is a struct; its exact interned sort id is irrelevant here
        // because baz has no self-edge and the variant branch is never reached.
        param_sort_hints: vec![None],
        mode: LogicMode::Default,
        is_trait_method: false,
        // forall<_x: ()> foo.bar == ()  -- no `baz(` call, not self-recursive.
        body: PureExpr::Bool(true),
        body_text: "pearlite! { forall<_x: ()> foo.bar == () }".to_string(),
        requires: Vec::new(),
        ensures: Vec::new(),
        raw_variants: Vec::new(),
        parsed_variants: Vec::new(),
        variant_parse_errors: Vec::new(),
        body_parse_failed: false,
        deep_model_dispatch_targets: None,
    };
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(
        analysis.errors.iter().all(|e| e.full_path != "crate::baz"),
        "non-recursive baz must not be rejected: {:?}",
        analysis.errors
    );
}

// ---- Self-named self-dispatch threading (the `terminates` trio class) ----
//
// `self.m(...)` inside the logic fn NAMED `m` provably dispatches back into
// the caller (via the enclosing impl, a trait/supertrait where-clause bound,
// or a trait default), but short-name resolution only accepts a UNIQUE name
// match and the trait declaration and its impls ALWAYS share the method name
// — so exactly the recursive case was silently dropped from the walk
// (creusot tests/should_fail/terminates/trait_impl_where.rs false accept).

fn self_named_dispatch_call(method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
        method: method.to_string(),
        args,
    }
}

/// RED pin (trait_impl_where.rs): an identity self-named self-dispatch —
/// `self.f()` inside `<i32 as Tr>::f` — must be rejected as unconditional
/// self-recursion even though the short name `f` is ambiguous (trait decl +
/// impl share it) and resolution returns no target.
#[test]
fn test_detect_logic_fn_recursion_errors_ambiguous_self_named_identity_dispatch_rejected() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let mut impl_f = make_recursion_node(
        "f",
        "creusot_test::<i32 as Tr>::f",
        false,
        self_named_dispatch_call("f", Vec::new()),
    );
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];
    impl_f.body_text = "self.f()".to_string();

    let errors = detect_logic_fn_recursion_errors(&[trait_decl, impl_f]);

    assert_eq!(
        errors.len(),
        1,
        "identity self-named dispatch must be rejected: {errors:?}"
    );
    assert_eq!(errors[0].full_path, "creusot_test::<i32 as Tr>::f");
    assert!(
        errors[0]
            .message
            .contains("unconditional self-recursion without #[variant(...)]"),
        "expected unconditional-self-recursion diagnostic: {errors:?}"
    );
}

/// RED pin: a parse-failed body whose TEXT shows a self-named self-dispatch
/// stays fail-closed through the unparseable-body reject.
#[test]
fn test_detect_logic_fn_recursion_errors_parse_failed_self_named_dispatch_rejected() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let mut impl_f = make_recursion_node(
        "f",
        "creusot_test::<i32 as Tr>::f",
        false,
        PureExpr::Bool(true),
    );
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];
    impl_f.body_text = "self.f()".to_string();
    impl_f.body_parse_failed = true;

    let errors = detect_logic_fn_recursion_errors(&[trait_decl, impl_f]);

    assert_eq!(errors.len(), 1, "parse-failed self-dispatch: {errors:?}");
    assert!(
        errors[0].message.contains("unparseable body"),
        "expected unparseable-body diagnostic: {errors:?}"
    );
}

/// The graph itself must carry the self-edge for ambiguous self-named
/// dispatch (the hole was in edge threading, not only in the verdict).
#[test]
fn test_build_logic_call_graph_threads_ambiguous_self_named_dispatch_self_edge() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let mut impl_f = make_recursion_node(
        "f",
        "creusot_test::<i32 as Tr>::f",
        false,
        self_named_dispatch_call("f", Vec::new()),
    );
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];

    let nodes = [trait_decl, impl_f];
    let graph = build_logic_call_graph(&nodes);

    assert!(
        has_self_edge(&graph, 1),
        "self-named self-dispatch must thread a self-edge: {graph:?}"
    );
    assert!(
        !has_self_edge(&graph, 0),
        "the trait declaration has no self-dispatch body: {graph:?}"
    );
}

/// GREEN: conditional self-named dispatch (guarded by a branch) keeps the
/// Creusot-compatible acceptance for conditional recursion — the edge is
/// threaded, but the unconditional reject must not fire.
#[test]
fn test_detect_logic_fn_recursion_errors_conditional_self_named_dispatch_allowed() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let body = PureExpr::Ite(
        Arc::new(int_ge(int_var("self"), PureExpr::Int(1))),
        Arc::new(self_named_dispatch_call("f", Vec::new())),
        Arc::new(PureExpr::Bool(true)),
    );
    let mut impl_f = make_recursion_node("f", "creusot_test::<i32 as Tr>::f", false, body);
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];

    let errors = detect_logic_fn_recursion_errors(&[trait_decl, impl_f]);

    assert!(
        errors.is_empty(),
        "conditional self-named dispatch stays accepted: {errors:?}"
    );
}

/// GREEN: a `(*self).f()` forwarding impl (e.g. `impl Tr for &T`) passes a
/// structurally different receiver — not an identity pass-through — so the
/// unconditional reject must not fire.
#[test]
fn test_detect_logic_fn_recursion_errors_deref_forwarding_self_named_dispatch_allowed() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let forwarding_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        )))),
        method: "f".to_string(),
        args: Vec::new(),
    };
    let mut impl_f =
        make_recursion_node("f", "creusot_test::<&T as Tr>::f", false, forwarding_call);
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];

    let errors = detect_logic_fn_recursion_errors(&[trait_decl, impl_f]);

    assert!(
        errors.is_empty(),
        "deref-forwarding self-named dispatch stays accepted: {errors:?}"
    );
}

/// GREEN: a `#[variant(...)]`-annotated self-named dispatch routes to the
/// variant lane (method-style edges are outside the supported proof fragment,
/// so the variant fallback heuristics apply) — the unconditional reject must
/// not fire.
#[test]
fn test_detect_logic_fn_recursion_errors_variant_annotated_self_named_dispatch_allowed() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let mut impl_f = make_recursion_node(
        "f",
        "creusot_test::<i32 as Tr>::f",
        true,
        self_named_dispatch_call("f", Vec::new()),
    );
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];

    let errors = detect_logic_fn_recursion_errors(&[trait_decl, impl_f]);

    assert!(
        errors.is_empty(),
        "variant-annotated self-named dispatch is adjudicated by the variant lane: {errors:?}"
    );
}

/// GREEN: the compact-text fallback must not misread `myself.f(` or a field
/// dispatch `self.vec.f(` as a bare `self.f(` call.
#[test]
fn test_compact_text_self_named_dispatch_guards_against_substring_matches() {
    assert!(compact_text_has_self_named_dispatch("self.f()", "f"));
    assert!(compact_text_has_self_named_dispatch(
        "if c { self.f(x) }",
        "f"
    ));
    assert!(!compact_text_has_self_named_dispatch("myself.f()", "f"));
    assert!(!compact_text_has_self_named_dispatch("self.vec.f()", "f"));
    assert!(!compact_text_has_self_named_dispatch("self.other()", "f"));
}

/// GREEN (comment-scoped text fallback): a successfully PARSED non-recursive
/// body whose raw source text mentions `self.f(` only inside a comment must
/// not fabricate a self-edge — the AST walk is authoritative for parsed
/// bodies, and the compact-text fallback is scoped to `body_parse_failed`
/// nodes only.
#[test]
fn test_parsed_body_with_self_dispatch_only_in_comment_not_rejected() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;

    let mut impl_f = make_recursion_node(
        "f",
        "creusot_test::<i32 as Tr>::f",
        false,
        PureExpr::Bool(true),
    );
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];
    // The raw source carries the pattern ONLY in a comment; the parsed body
    // is the literal `true` (body_parse_failed stays false).
    impl_f.body_text = "// resembles self.f() but never calls it\ntrue".to_string();

    let nodes = [trait_decl, impl_f];
    let graph = build_logic_call_graph(&nodes);
    assert!(
        !has_self_edge(&graph, 1),
        "a comment-only `self.f(` must not thread a self-edge on a parsed body: {graph:?}"
    );

    let errors = detect_logic_fn_recursion_errors(&nodes);
    assert!(
        errors.is_empty(),
        "a comment-only `self.f(` in a parsed body must not be rejected: {errors:?}"
    );
}
