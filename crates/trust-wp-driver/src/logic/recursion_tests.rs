// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for logic function recursion validation.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::{
    formula::{ExprSort, MatchArm, Pattern, PureExpr, UnOp},
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
        param_int_widths: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
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
        param_int_widths: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
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
fn test_detect_logic_fn_recursion_errors_unconditional_different_args_rejected() {
    // `fn fib(n) { fib(n-1) + fib(n-2) }` on Int with no #[variant]: not
    // structurally recursive, so Creusot (validate/terminates.rs) refuses it
    // ("Recursive logic function without a #[variant] clause or a
    // structurally decreasing argument"; should_fail/bug/1966).
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
        errors.iter().any(|e| e
            .message
            .contains("Recursive logic function without a #[variant] clause")),
        "free non-structural recursion without #[variant] must be refused: {errors:?}"
    );
}

#[test]
fn test_detect_logic_fn_recursion_errors_conditional_self_recursion_rejected() {
    // `fn f(n) { if n == 0 { true } else { f(n - 1) } }` on Int with no
    // #[variant]: guarded, but Int is not a structurally decreasing argument,
    // so Creusot (validate/terminates.rs) refuses it (should_fail/bug/1966).
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
        errors.iter().any(|e| e
            .message
            .contains("Recursive logic function without a #[variant] clause")),
        "free non-structural recursion without #[variant] must be refused: {errors:?}"
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
fn test_detect_logic_fn_recursion_errors_self_cycle_with_variant_rejected_without_proof() {
    // `#[variant] fn f() { f() }`: a variant annotation is not a termination
    // proof. With no checked decrease, the recursion is never credited.
    let nodes = vec![make_recursion_node("f", "crate::f", true, call("f"))];

    let errors = detect_logic_fn_recursion_errors(&nodes);

    assert_eq!(errors.len(), 1, "{errors:?}");
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
    trait_f.is_associated_fn = true;
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
    trait_f.is_associated_fn = true;
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
    trait_f.is_associated_fn = true;
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
    trait_f.is_associated_fn = true;
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

    // The wildcard arm carries no fact excluding `n == 0`, so `0 <= n - 1`
    // is not provable from `n >= 0`: the cycle stays rejected.
    assert_eq!(analysis.errors.len(), 2, "{:?}", analysis.errors);
    assert!(analysis.supported_scc_members.is_empty());
    assert!(analysis
        .errors
        .iter()
        .all(|error| error.message.contains("mutual recursion")));
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
        param_int_widths: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
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
fn test_parse_failed_self_recursive_node_rejected_even_with_variant() {
    // A parse-failed body has no structured call edges, so no decrease can be
    // proven; a `#[variant]` annotation alone is not credited.
    let mut node = make_parse_failed_node("f", "crate::f", "match n { 0 => true, _ => f(n - 1) }");
    node.raw_variants = vec!["n".to_string()];

    let errors = detect_logic_fn_recursion_errors(&[node]);

    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].message.contains("could not be proven"),
        "{errors:?}"
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
        param_int_widths: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
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
/// two self-calls `fib(i - 1)` and `fib(i - 2)` under `!(i <= 0) && i != 1`.
/// That path condition itself proves `i >= 0` and both decreases (no implicit
/// nonnegativity is assumed); maps to Proven and must NOT be newly rejected.
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
        param_int_widths: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
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
        param_int_widths: Vec::new(),
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
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
    trait_decl.is_associated_fn = true;

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
    trait_decl.is_associated_fn = true;

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
    trait_decl.is_associated_fn = true;

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
    trait_decl.is_associated_fn = true;

    let body = PureExpr::Ite(
        Arc::new(int_ge(int_var("self"), PureExpr::Int(1))),
        Arc::new(self_named_dispatch_call("f", Vec::new())),
        Arc::new(PureExpr::Bool(true)),
    );
    let mut impl_f = make_recursion_node("f", "creusot_test::<i32 as Tr>::f", false, body);
    impl_f.is_associated_fn = true;
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
    trait_decl.is_associated_fn = true;

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
    impl_f.is_associated_fn = true;
    impl_f.params = vec!["self".to_string()];
    impl_f.param_sort_hints = vec![None];

    let errors = detect_logic_fn_recursion_errors(&[trait_decl, impl_f]);

    assert!(
        errors.is_empty(),
        "deref-forwarding self-named dispatch stays accepted: {errors:?}"
    );
}

/// A `#[variant(...)]`-annotated self-named dispatch routes to the variant
/// lane. Method-style edges are outside the modelled proof fragment, so no
/// decrease proof exists and the recursion is rejected (never credited).
#[test]
fn test_detect_logic_fn_recursion_errors_variant_annotated_self_named_dispatch_rejected() {
    let mut trait_decl =
        make_recursion_node("f", "creusot_test::Tr::f", false, PureExpr::Bool(true));
    trait_decl.is_trait_method = true;
    trait_decl.is_associated_fn = true;

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
        errors
            .iter()
            .any(|e| e.full_path == "creusot_test::<i32 as Tr>::f"
                && e.message.contains("could not be proven")),
        "variant-annotated self-named dispatch without a decrease proof is rejected: {errors:?}"
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
    trait_decl.is_associated_fn = true;

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

/// bug/1204 `evil`: `#[requires(false)] #[variant(x)] fn evil(x: Int) -> Int
/// { evil(-x) + 1 }`. Creusot's termination goal is
/// `requires -> well_founded(x, -x)`, valid because the requires is
/// unsatisfiable, so Creusot accepts `evil`. The logic `Int` parameter carries
/// the ADT sort hint `Datatype(creusot_std::Int)`, which must count as an
/// integer variant; the negated-argument text heuristic must not overrule the
/// proven decrease.
#[test]
fn test_analyze_logic_fn_recursion_accepts_negated_self_call_under_unsat_requires() {
    let body = int_add(
        PureExpr::LogicFnCall {
            name: "evil".to_string(),
            args: vec![PureExpr::UnOp(UnOp::Neg, Arc::new(x_var()))],
        },
        PureExpr::Int(1),
    );
    let mut node = make_variant_x_node("evil", "crate::evil", vec![PureExpr::Bool(false)], body);
    node.body_text = "evil(-x) + 1".to_string();
    node.param_sort_hints = vec![Some(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("creusot_std::Int"),
    ))];

    let analysis = analyze_logic_fn_recursion_nodes(&[node]);

    assert!(
        analysis.errors.is_empty(),
        "requires(false) makes every decrease goal valid (Creusot accepts evil): {:?}",
        analysis.errors
    );
}

/// RED guard for the test above: the SAME negated self-call without an
/// unsatisfiable requires does not terminate (`evil(0)` calls `evil(0)`) and
/// must stay rejected.
#[test]
fn test_analyze_logic_fn_recursion_rejects_negated_self_call_without_requires() {
    let body = int_add(
        PureExpr::LogicFnCall {
            name: "evil".to_string(),
            args: vec![PureExpr::UnOp(UnOp::Neg, Arc::new(x_var()))],
        },
        PureExpr::Int(1),
    );
    let mut node = make_variant_x_node("evil", "crate::evil", Vec::new(), body);
    node.body_text = "evil(-x) + 1".to_string();
    node.param_sort_hints = vec![Some(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("creusot_std::Int"),
    ))];

    let analysis = analyze_logic_fn_recursion_nodes(&[node]);

    assert!(
        analysis
            .errors
            .iter()
            .any(|error| error.full_path == "crate::evil"),
        "a non-decreasing negated self-call must be rejected: {:?}",
        analysis.errors
    );
}

/// Review probe pr8 (`osc`): `#[variant(x)] fn osc(x: Int) -> Int
/// { if x != 0 { osc(-x) + 1 } else { 0 } }`, NO requires. Creusot's goal
/// `x != 0 -> x >= 0 && -x < x` is false at `x = -1`; `osc(1)`/`osc(-1)` do
/// not terminate and the defining axiom gives `0 = 2`. The decrease obligation
/// must NOT assume `0 <= x` (which made the query valid and returned Proven):
/// the outcome must be a definitive Failed, and the fn must be rejected.
#[test]
fn test_try_prove_self_variant_decrease_rejects_guarded_negated_osc() {
    let body = PureExpr::Ite(
        Arc::new(PureExpr::UnOp(
            UnOp::Not,
            Arc::new(int_eq(x_var(), PureExpr::Int(0))),
        )),
        Arc::new(int_add(
            PureExpr::LogicFnCall {
                name: "osc".to_string(),
                args: vec![PureExpr::UnOp(UnOp::Neg, Arc::new(x_var()))],
            },
            PureExpr::Int(1),
        )),
        Arc::new(PureExpr::Int(0)),
    );
    let mut node = make_variant_x_node("osc", "crate::osc", Vec::new(), body);
    node.param_sort_hints = vec![Some(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("creusot_std::Int"),
    ))];
    let nodes = vec![node];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);
    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "osc(-x) under `x != 0` must fail the decrease goal (x = -1), got: {outcome:?}"
    );

    let analysis = analyze_logic_fn_recursion_nodes(&nodes);
    assert!(
        analysis
            .errors
            .iter()
            .any(|error| error.full_path == "crate::osc"),
        "osc must be rejected: {:?}",
        analysis.errors
    );
}

/// Control for the osc test: the same shape with the nonnegativity STATED as
/// the fn's own requires, `#[requires(x >= 0)] #[variant(x)] fn f(x: Int)
/// { if x > 0 { f(x - 1) } else { 0 } }`, is a valid variant and stays Proven.
#[test]
fn test_try_prove_self_variant_decrease_proven_for_requires_guarded_int() {
    let body = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(x_var()),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        Arc::new(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![int_sub(x_var(), PureExpr::Int(1))],
        }),
        Arc::new(PureExpr::Int(0)),
    );
    let mut node = make_variant_x_node(
        "f",
        "crate::f",
        vec![int_ge(x_var(), PureExpr::Int(0))],
        body,
    );
    node.param_sort_hints = vec![Some(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("creusot_std::Int"),
    ))];
    let nodes = vec![node];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let parsed_edges = collect_parsed_logic_call_edges(&nodes, &lookup);

    let outcome = try_prove_self_variant_decrease(0, &nodes, &graph, &parsed_edges);
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "requires-guarded f(x - 1) must prove decrease, got: {outcome:?}"
    );
    let analysis = analyze_logic_fn_recursion_nodes(&nodes);
    assert!(
        analysis.errors.iter().all(|e| e.full_path != "crate::f"),
        "requires-guarded f must not be rejected: {:?}",
        analysis.errors
    );
}

fn machine_int(signed: bool, bits: u32) -> Option<super::super::discovery::MachineIntWidth> {
    Some(super::super::discovery::MachineIntWidth { signed, bits })
}

/// The machine-integer parameter ranges `to_logic_fn_def` adds to a variant
/// logic fn's requires (and so to its defining-axiom guard).
fn range_requires(node: &LogicRecursionNode) -> Vec<PureExpr> {
    super::super::discovery::machine_int_parameter_range_requires(
        &node.params,
        &node.param_int_widths,
    )
}

fn variant_outcome(node: LogicRecursionNode) -> SelfVariantDecrease {
    let nodes = vec![node];
    let lookup = build_logic_name_lookup(&nodes);
    let graph = build_logic_call_graph(&nodes);
    let variant_edges = collect_variant_proof_call_edges(&nodes, &lookup);
    try_prove_self_variant_decrease(0, &nodes, &graph, &variant_edges)
}

fn gt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(lhs),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(rhs),
    )
}

fn not_eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::UnOp(UnOp::Not, Arc::new(int_eq(lhs, rhs)))
}

fn self_call(name: &str, arg: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args: vec![arg],
    }
}

/// `#[variant(i)] fn lemma(i: u64)` recursing on `i - 2` only when `i >= 2`
/// (cell/02_fib `lemma_fib_bound` over `u64`): `0 <= i` is a consequence of
/// the `u64` type, and the arguments stay in range. Proven.
#[test]
fn test_try_prove_self_variant_decrease_u64_param_range_is_a_fact() {
    let body = PureExpr::Ite(
        Arc::new(int_ge(x_var(), PureExpr::Int(2))),
        Arc::new(self_call("lemma", int_sub(x_var(), PureExpr::Int(2)))),
        Arc::new(PureExpr::Int(0)),
    );
    let mut node = make_variant_x_node("lemma", "crate::lemma", Vec::new(), body);
    node.param_int_widths = vec![machine_int(false, 64)];
    node.requires = range_requires(&node);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "u64 lemma recursing on x - 2 under x >= 2 must prove, got: {outcome:?}"
    );
}

/// The same body WITHOUT the width (a mathematical `Int` parameter) must not
/// prove: `0 <= x` is not derivable, so the new fact is what makes it pass.
#[test]
fn test_try_prove_self_variant_decrease_int_param_gets_no_range_fact() {
    let body = PureExpr::Ite(
        Arc::new(not_eq(x_var(), PureExpr::Int(0))),
        Arc::new(self_call("lemma", int_sub(x_var(), PureExpr::Int(1)))),
        Arc::new(PureExpr::Int(0)),
    );
    let node = make_variant_x_node("lemma", "crate::lemma", Vec::new(), body);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "Int x - 1 under x != 0 must fail (x = -5), got: {outcome:?}"
    );
}

/// `fn down(x: i64) -> Int { if x > 0 { down(x - 1) } else { 0 } }`: Proven.
#[test]
fn test_try_prove_self_variant_decrease_i64_guarded_down_proven() {
    let body = PureExpr::Ite(
        Arc::new(gt(x_var(), PureExpr::Int(0))),
        Arc::new(self_call("down", int_sub(x_var(), PureExpr::Int(1)))),
        Arc::new(PureExpr::Int(0)),
    );
    let mut node = make_variant_x_node("down", "crate::down", Vec::new(), body);
    node.param_int_widths = vec![machine_int(true, 64)];
    node.requires = range_requires(&node);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "i64 down under x > 0 must prove, got: {outcome:?}"
    );
}

/// `fn bad(x: i64) -> Int { if x != 0 { bad(x - 1) } else { 0 } }`: a
/// negative `i64` recurses forever. Failed.
#[test]
fn test_try_prove_self_variant_decrease_i64_negative_bad_rejected() {
    let body = PureExpr::Ite(
        Arc::new(not_eq(x_var(), PureExpr::Int(0))),
        Arc::new(self_call("bad", int_sub(x_var(), PureExpr::Int(1)))),
        Arc::new(PureExpr::Int(0)),
    );
    let mut node = make_variant_x_node("bad", "crate::bad", Vec::new(), body);
    node.param_int_widths = vec![machine_int(true, 64)];
    node.requires = range_requires(&node);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "i64 bad under x != 0 must fail (x = -1), got: {outcome:?}"
    );
}

/// `#[variant(x)] fn f(x: u64) { if x != 0 { f(0 - x) } }`: the caller range
/// makes `0 <= x && -x < x` valid, but `-x` is outside `u64`, where the Int
/// model has no range fact. The argument range GOAL rejects it.
#[test]
fn test_try_prove_self_variant_decrease_u64_out_of_range_argument_rejected() {
    let body = PureExpr::Ite(
        Arc::new(not_eq(x_var(), PureExpr::Int(0))),
        Arc::new(self_call("f", int_sub(PureExpr::Int(0), x_var()))),
        Arc::new(PureExpr::Int(0)),
    );
    let mut node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    node.param_int_widths = vec![machine_int(false, 64)];
    node.requires = range_requires(&node);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "u64 f(0 - x) must fail the argument range goal, got: {outcome:?}"
    );
}

/// Unguarded `fib(n: u64) = fib(n - 1) + ..`: at n = 0 the argument leaves
/// `u64` (and the recursion never stops). Failed.
#[test]
fn test_try_prove_self_variant_decrease_u64_unguarded_fib_rejected() {
    let body = int_add(
        self_call("fib", int_sub(x_var(), PureExpr::Int(1))),
        self_call("fib", int_sub(x_var(), PureExpr::Int(2))),
    );
    let mut node = make_variant_x_node("fib", "crate::fib", Vec::new(), body);
    node.param_int_widths = vec![machine_int(false, 64)];
    node.requires = range_requires(&node);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "unguarded u64 fib must fail, got: {outcome:?}"
    );
}

/// Review probe pd1: `#[requires(!(x <= x))] #[variant(n)] fn fneg(n: Int, x:
/// f64) { fneg(-n, x) + 1 }`. The requires mentions a float parameter, so the
/// unsatisfiable-requires shortcut must refuse, and `-n` fails the decrease.
#[test]
fn test_try_prove_self_variant_decrease_float_requires_refuses_unsat_shortcut() {
    let float_x = PureExpr::Var("x".to_string(), None);
    let body = int_add(
        PureExpr::LogicFnCall {
            name: "fneg".to_string(),
            args: vec![
                PureExpr::UnOp(UnOp::Neg, Arc::new(int_var("n"))),
                float_x.clone(),
            ],
        },
        PureExpr::Int(1),
    );
    let requires = vec![PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::BinOp(
            Arc::new(float_x.clone()),
            trust_wp_core::formula::BinOp::Le,
            Arc::new(float_x),
        )),
    )];
    assert!(
        !requires_proven_unsatisfiable_for_test(
            &requires,
            &["n".to_string(), "x".to_string()],
            &[
                Some(ExprSort::Int),
                Some(ExprSort::Float(trust_wp_core::formula::FloatWidth::F64))
            ],
        ),
        "a float-sorted requires must refuse the unsatisfiable shortcut"
    );
    assert!(
        requires_proven_unsatisfiable_for_test(
            &[PureExpr::Bool(false)],
            &["n".to_string(), "x".to_string()],
            &[
                Some(ExprSort::Int),
                Some(ExprSort::Float(trust_wp_core::formula::FloatWidth::F64))
            ],
        ),
        "a literal `false` requires is still proven unsatisfiable"
    );

    let mut node = make_variant_x_node("fneg", "crate::fneg", requires, body);
    node.params = vec!["n".to_string(), "x".to_string()];
    node.param_sort_hints = vec![
        Some(ExprSort::Int),
        Some(ExprSort::Float(trust_wp_core::formula::FloatWidth::F64)),
    ];
    node.param_int_widths = vec![None, None];
    node.raw_variants = vec!["n".to_string()];
    node.parsed_variants = vec![int_var("n")];
    let outcome = variant_outcome(node);
    assert!(
        !matches!(outcome, SelfVariantDecrease::Proven),
        "fneg must not be Proven, got: {outcome:?}"
    );
}

/// `#[variant(x)] fn f(x: u64) -> Int { if x == 0 { 0 } else { f(x - 1) } }`.
/// The guard `x != 0` does NOT imply `0 <= x`: the proof needs the u64 range,
/// which reaches the query only through the range requires that also guard the
/// definition. With the requires: Proven. Same node, width known but no range
/// requires: Failed (x = -1) — the range requires are load-bearing.
#[test]
fn test_try_prove_self_variant_decrease_u64_eq_zero_guard_needs_range_requires() {
    let body = PureExpr::Ite(
        Arc::new(int_eq(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Int(0)),
        Arc::new(self_call("f", int_sub(x_var(), PureExpr::Int(1)))),
    );
    let mut node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    node.param_int_widths = vec![machine_int(false, 64)];
    let unguarded = variant_outcome(node.clone());
    assert!(
        matches!(unguarded, SelfVariantDecrease::Failed(_)),
        "without the range requires `x != 0 |- 0 <= x` must fail, got: {unguarded:?}"
    );
    node.requires = range_requires(&node);
    let guarded = variant_outcome(node);
    assert!(
        matches!(guarded, SelfVariantDecrease::Proven),
        "with the u64 range requires the decrease must prove, got: {guarded:?}"
    );
}

/// Review probe r4: `#[variant(x)] fn f(x: Int) -> Int { if x > 0 { let x = x
/// + 1; f(x - 1) + 1 } else { 0 } }` recurses on `f(x)`. The let binding must
/// be substituted into the call, so the decrease `x < x` fails.
#[test]
fn test_try_prove_self_variant_decrease_let_shadowing_parameter_rejected() {
    let body = PureExpr::Ite(
        Arc::new(gt(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(int_add(x_var(), PureExpr::Int(1))),
            body: Arc::new(int_add(
                self_call("f", int_sub(x_var(), PureExpr::Int(1))),
                PureExpr::Int(1),
            )),
        }),
        Arc::new(PureExpr::Int(0)),
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Failed(_)),
        "let-shadowed f(x + 1 - 1) must fail, got: {outcome:?}"
    );
}

/// Control for the let substitution: `if x > 0 { let y = x - 1; f(y) } else
/// { 0 }` recurses on `x - 1`. Proven (it was Failed while `y` stayed free).
#[test]
fn test_try_prove_self_variant_decrease_let_bound_argument_proven() {
    let body = PureExpr::Ite(
        Arc::new(gt(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Let {
            var: "y".to_string(),
            value: Arc::new(int_sub(x_var(), PureExpr::Int(1))),
            body: Arc::new(self_call("f", int_var("y"))),
        }),
        Arc::new(PureExpr::Int(0)),
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    let outcome = variant_outcome(node);
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "f(y) with y = x - 1 under x > 0 must prove, got: {outcome:?}"
    );
}

/// Review follow-up (match-arm shadowing): `if x > 0 { match Some(x + 1) {
/// Some(x) => f(x - 1) + 1, None => 0 } } else { 0 }` recurses on `f(x)`.
/// The edge sits under a match (Unsupported fragment), so it must be rejected
/// explicitly rather than reach the permissive Unsupported arm.
#[test]
fn test_analyze_logic_fn_recursion_rejects_match_binder_shadowing_parameter() {
    let body = PureExpr::Ite(
        Arc::new(gt(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: vec![int_add(x_var(), PureExpr::Int(1))],
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: int_add(
                        self_call("f", int_sub(x_var(), PureExpr::Int(1))),
                        PureExpr::Int(1),
                    ),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Int(0),
                },
            ],
        }),
        Arc::new(PureExpr::Int(0)),
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(
        analysis
            .errors
            .iter()
            .any(|error| error.message.contains("shadows parameter `x`")),
        "match-arm shadowing of the parameter must be rejected, got: {:?}",
        analysis.errors
    );
}

/// `match Some(<scrutinee_arg>) { Some(<binder>) => <arm>, None => 0 }` under
/// `x > 0`, else `0`.
fn guarded_some_match(scrutinee_arg: PureExpr, binder: &str, arm: PureExpr) -> PureExpr {
    PureExpr::Ite(
        Arc::new(gt(x_var(), PureExpr::Int(0))),
        Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: vec![scrutinee_arg],
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding(binder.to_string()))),
                    },
                    body: arm,
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Int(0),
                },
            ],
        }),
        Arc::new(PureExpr::Int(0)),
    )
}

/// Review v2 p1: `match Some(x + 1) { Some(y) => f(y - 1) + 1 }` recurses on
/// `f(x)`. No binder shadows a parameter, so this used to reach the permissive
/// Unsupported arm and was credited (`f(1) = f(1) + 1`). It must be rejected.
#[test]
fn test_analyze_logic_fn_recursion_rejects_match_scoped_non_decreasing_call() {
    let body = guarded_some_match(
        int_add(x_var(), PureExpr::Int(1)),
        "y",
        int_add(
            self_call("f", int_sub(int_var("y"), PureExpr::Int(1))),
            PureExpr::Int(1),
        ),
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(
        analysis.errors.iter().any(|e| e.full_path == "crate::f"),
        "a match-scoped call that does not decrease must be rejected, got: {:?}",
        analysis.errors
    );
}

/// Review v2 p2: `Some(y) => { let x = y; f(x - 1) + 1 }`: the let re-binds the
/// parameter name inside the arm. Rejected.
#[test]
fn test_analyze_logic_fn_recursion_rejects_match_let_rebinding_parameter() {
    let body = guarded_some_match(
        int_add(x_var(), PureExpr::Int(1)),
        "y",
        PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(int_var("y")),
            body: Arc::new(int_add(
                self_call("f", int_sub(x_var(), PureExpr::Int(1))),
                PureExpr::Int(1),
            )),
        },
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(
        analysis.errors.iter().any(|e| e.full_path == "crate::f"),
        "a let re-binding under a match arm must not hide a non-decreasing call, got: {:?}",
        analysis.errors
    );
}

/// Control: `match Some(x - 1) { Some(y) => f(y) + 1 }` under `x > 0` decreases:
/// the pattern fact `y == x - 1` is a literal consequence of the match.
#[test]
fn test_try_prove_self_variant_decrease_match_pattern_fact_proven() {
    let body = guarded_some_match(
        int_sub(x_var(), PureExpr::Int(1)),
        "y",
        int_add(self_call("f", int_var("y")), PureExpr::Int(1)),
    );
    let node = make_variant_x_node("f", "crate::f", Vec::new(), body);
    let outcome = variant_outcome(node.clone());
    assert!(
        matches!(outcome, SelfVariantDecrease::Proven),
        "f(y) with y == x - 1 under x > 0 must prove, got: {outcome:?}"
    );
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
}

/// The variant view renames match binders apart: the edge must not mention the
/// source binder `y`, and must carry the pattern fact.
#[test]
fn test_variant_proof_edges_rename_match_binders_and_state_pattern_fact() {
    let body = guarded_some_match(
        int_sub(x_var(), PureExpr::Int(1)),
        "y",
        self_call("f", int_var("y")),
    );
    let nodes = vec![make_variant_x_node("f", "crate::f", Vec::new(), body)];
    let lookup = build_logic_name_lookup(&nodes);
    let edges = collect_variant_proof_call_edges(&nodes, &lookup);
    let edge = edges
        .iter()
        .find(|e| !e.recovered_from_text_only)
        .expect("structured self edge");
    assert!(edge.unsupported_reason.is_none(), "{edge:?}");
    assert!(
        !edge.actual_args[0].free_vars().iter().any(|v| v == "y"),
        "binder must be renamed apart: {edge:?}"
    );
    assert_eq!(edge.path_conditions.len(), 2, "{edge:?}");
    // The legacy view is unchanged: match edges stay unsupported.
    let legacy = collect_parsed_logic_call_edges(&nodes, &lookup);
    assert!(legacy
        .iter()
        .filter(|e| !e.recovered_from_text_only)
        .all(|e| e.unsupported_reason.is_some()));
}

/// A length variant is a modelled term kind, so the decrease obligation is
/// OWED on it: `len(x)` measured against `len(x - 1)` is refuted, and the
/// function is rejected by the proof rather than by the grammar.
#[test]
fn test_analyze_logic_fn_recursion_rejects_length_variant_that_does_not_decrease() {
    let mut node = make_variant_x_node(
        "f",
        "crate::f",
        Vec::new(),
        PureExpr::Ite(
            Arc::new(gt(x_var(), PureExpr::Int(0))),
            Arc::new(self_call("f", int_sub(x_var(), PureExpr::Int(1)))),
            Arc::new(PureExpr::Int(0)),
        ),
    );
    node.raw_variants = vec!["x.len()".to_string()];
    node.parsed_variants = vec![PureExpr::MethodCall {
        receiver: Arc::new(x_var()),
        method: "len".to_string(),
        args: Vec::new(),
    }];
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(
        analysis
            .errors
            .iter()
            .any(|e| e.message.contains("does not strictly decrease")),
        "{:?}",
        analysis.errors
    );
}

/// A variant term whose result sort the encoder does not fix to `Int` has no
/// well-founded order to state the decrease over, so it is refused by the
/// grammar and never credited by a fallback.
#[test]
fn test_analyze_logic_fn_recursion_rejects_unmodelled_variant() {
    let mut node = make_variant_x_node(
        "f",
        "crate::f",
        Vec::new(),
        PureExpr::Ite(
            Arc::new(gt(x_var(), PureExpr::Int(0))),
            Arc::new(self_call("f", int_sub(x_var(), PureExpr::Int(1)))),
            Arc::new(PureExpr::Int(0)),
        ),
    );
    node.raw_variants = vec!["x.tail()".to_string()];
    node.parsed_variants = vec![PureExpr::MethodCall {
        receiver: Arc::new(x_var()),
        method: "tail".to_string(),
        args: Vec::new(),
    }];
    let analysis = analyze_logic_fn_recursion_nodes(&[node]);
    assert!(
        analysis
            .errors
            .iter()
            .any(|e| e.message.contains("could not be proven")),
        "{:?}",
        analysis.errors
    );
}
