// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use crate::{
    tests::helpers::{
        and, bool_expr, deref, eq, forall, int, ite, let_assume, let_bind, logic_fn_call,
        match_expr, method_call, var,
    },
    verify::{collect_ground_postcondition_mut_calls, collect_ground_resolve_calls},
    Pattern, PureExpr,
};

// --- ground collector quantifier filtering (#1489 follow-up) ---

#[test]
#[timeout(30000)]
fn collect_ground_postcondition_mut_calls_skips_quantified_terms() {
    let ground = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("args"), var("f2"), var("r")],
    );
    let quantified = forall(
        "st1",
        forall(
            "ret",
            method_call(
                var("f"),
                "postcondition_mut",
                vec![var("args"), var("st1"), var("ret")],
            ),
        ),
    );
    let requires = vec![quantified, ground];

    let calls = collect_ground_postcondition_mut_calls(&requires);

    assert_eq!(
        calls.len(),
        1,
        "quantified calls must not be treated as ground witnesses"
    );
    assert_eq!(calls[0].receiver, &var("f"));
    assert_eq!(calls[0].args, &[var("args"), var("f2"), var("r")]);
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_skips_quantified_terms() {
    let requires = vec![
        forall("st1", logic_fn_call("resolve", vec![var("st1")])),
        logic_fn_call("resolve", vec![var("f2")]),
    ];

    let calls = collect_ground_resolve_calls(&requires);

    assert_eq!(
        calls,
        vec![&var("f2")],
        "quantified resolve terms must not be treated as ground witnesses"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_skips_match_let_closure_bound_terms() {
    let requires = vec![
        match_expr(
            var("x"),
            vec![(
                Pattern::Binding("a".to_string()),
                logic_fn_call("resolve", vec![var("a")]),
            )],
        ),
        let_bind("b", int(0), logic_fn_call("resolve", vec![var("b")])),
        PureExpr::Closure {
            params: vec![("c".to_string(), None)],
            body: Arc::new(logic_fn_call("resolve", vec![var("c")])),
        },
        logic_fn_call("resolve", vec![var("free")]),
    ];

    let calls = collect_ground_resolve_calls(&requires);

    assert_eq!(
        calls.len(),
        1,
        "match/let/closure bound vars should not produce ground resolve terms"
    );
    assert_eq!(calls[0], &var("free"));
}

#[test]
#[timeout(30000)]
fn collect_ground_postcondition_mut_calls_skips_match_let_closure_bound_terms() {
    let requires = vec![
        match_expr(
            var("x"),
            vec![(
                Pattern::Binding("a".to_string()),
                method_call(var("a"), "postcondition_mut", vec![var("state")]),
            )],
        ),
        let_bind(
            "b",
            int(0),
            method_call(var("f"), "postcondition_mut", vec![var("b")]),
        ),
        PureExpr::Closure {
            params: vec![("c".to_string(), None)],
            body: Arc::new(method_call(var("c"), "postcondition_mut", vec![var("r")])),
        },
        method_call(var("free_f"), "postcondition_mut", vec![var("free_state")]),
    ];

    let calls = collect_ground_postcondition_mut_calls(&requires);

    assert_eq!(
        calls.len(),
        1,
        "match/let/closure bound vars should not produce ground postcondition_mut witnesses"
    );
    assert_eq!(calls[0].receiver, &var("free_f"));
    assert_eq!(calls[0].args, &[var("free_state")]);
}

// --- collect_ground_resolve_calls recursion coverage (#2007) ---

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_binop() {
    // resolve(f) nested inside BinOp(resolve(f), ==, Int(0))
    let requires = vec![eq(logic_fn_call("resolve", vec![var("f")]), int(0))];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls,
        vec![&var("f")],
        "resolve(f) nested inside BinOp should be collected"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_ite() {
    // if true then resolve(a) else resolve(b) — both should be collected
    let requires = vec![ite(
        bool_expr(true),
        logic_fn_call("resolve", vec![var("a")]),
        logic_fn_call("resolve", vec![var("b")]),
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(calls.len(), 2, "both branches of Ite should be traversed");
    assert_eq!(calls[0], &var("a"));
    assert_eq!(calls[1], &var("b"));
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_nested_in_and_chain() {
    // resolve(a) && resolve(b) && resolve(c) — all three collected
    let requires = vec![and(
        and(
            logic_fn_call("resolve", vec![var("a")]),
            logic_fn_call("resolve", vec![var("b")]),
        ),
        logic_fn_call("resolve", vec![var("c")]),
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls.len(),
        3,
        "all resolve calls in nested BinOp chain should be collected"
    );
    assert_eq!(calls[0], &var("a"));
    assert_eq!(calls[1], &var("b"));
    assert_eq!(calls[2], &var("c"));
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_match_scrutinee() {
    // match resolve(f) { ... } — resolve in scrutinee should be collected
    let requires = vec![match_expr(
        logic_fn_call("resolve", vec![var("f")]),
        vec![(Pattern::Wildcard, bool_expr(true))],
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls,
        vec![&var("f")],
        "resolve(f) in match scrutinee should be collected"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_let_value() {
    // let x = resolve(f); body — resolve in value should be collected
    let requires = vec![let_bind(
        "x",
        logic_fn_call("resolve", vec![var("f")]),
        bool_expr(true),
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls,
        vec![&var("f")],
        "resolve(f) in let value position should be collected"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_deref() {
    // Deref(resolve(f)) — resolve inside Deref wrapper should be collected
    let requires = vec![deref(logic_fn_call("resolve", vec![var("f")]))];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls,
        vec![&var("f")],
        "resolve(f) inside Deref should be collected"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_method_call() {
    // receiver.method(resolve(f)) — resolve in method call args
    let requires = vec![method_call(
        var("r"),
        "postcondition",
        vec![logic_fn_call("resolve", vec![var("f")])],
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls,
        vec![&var("f")],
        "resolve(f) in method call args should be collected"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_finds_resolve_inside_let_assume() {
    // LetAssume { assumption: resolve(f), body: ... }
    let requires = vec![let_assume(
        logic_fn_call("resolve", vec![var("f")]),
        bool_expr(true),
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert_eq!(
        calls,
        vec![&var("f")],
        "resolve(f) in LetAssume assumption should be collected"
    );
}

#[test]
#[timeout(30000)]
fn collect_ground_resolve_calls_quantified_inside_binop_still_skipped() {
    // forall st. (resolve(st) == 0) — resolve(st) is quantified even though inside BinOp
    let requires = vec![forall(
        "st",
        eq(logic_fn_call("resolve", vec![var("st")]), int(0)),
    )];
    let calls = collect_ground_resolve_calls(&requires);
    assert!(
        calls.is_empty(),
        "resolve(st) inside BinOp under forall should still be skipped"
    );
}
