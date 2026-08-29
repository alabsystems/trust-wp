// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for closure axiom AST detection functions (#1946 Phase 3).
//!
//! Coverage targets from `encoder/closure_axioms.rs`:
//! - `body_has_postcondition_mut_with_var`: recursive postcondition_mut detection
//!   with variable reference, including shadowing by quantifiers/let/closure
//! - `body_has_any_postcondition_mut`: simpler recursive detection ignoring
//!   which variable is referenced
//! - `closure_sort_tag` / `closure_sort_from_tag`: sort tag encoding/decoding
//!   roundtrip and edge cases

use std::sync::Arc;

use ntest::timeout;

use super::*;

// ── closure_sort_tag / closure_sort_from_tag tests ──────────────────

/// Bool sort roundtrips through tag encoding/decoding.
#[test]
#[timeout(30000)]
fn test_sort_tag_roundtrip_bool() {
    let tag = AYEncoder::closure_sort_tag(&Sort::Bool);
    assert_eq!(tag, "b");
    assert_eq!(AYEncoder::closure_sort_from_tag(&tag), Some(Sort::Bool));
}

/// Int sort roundtrips through tag encoding/decoding.
#[test]
#[timeout(30000)]
fn test_sort_tag_roundtrip_int() {
    let tag = AYEncoder::closure_sort_tag(&Sort::Int);
    assert_eq!(tag, "i");
    assert_eq!(AYEncoder::closure_sort_from_tag(&tag), Some(Sort::Int));
}

/// Uninterpreted sort (non-closure) uses the fallback "u" tag.
#[test]
#[timeout(30000)]
fn test_sort_tag_uninterpreted_fallback() {
    let sort = Sort::Uninterpreted("MyType".to_string());
    let tag = AYEncoder::closure_sort_tag(&sort);
    assert_eq!(tag, "u");
    // "u" decodes to Int (the universal SMT sort for uninterpreted types).
    assert_eq!(AYEncoder::closure_sort_from_tag(&tag), Some(Sort::Int));
}

/// ClosureEnv sort uses hex encoding and roundtrips correctly.
#[test]
#[timeout(30000)]
fn test_sort_tag_roundtrip_closure_env() {
    let sort = Sort::Uninterpreted("ClosureEnv_abc".to_string());
    let tag = AYEncoder::closure_sort_tag(&sort);
    assert!(
        tag.starts_with('c'),
        "closure env tag should start with 'c'"
    );
    let decoded = AYEncoder::closure_sort_from_tag(&tag);
    assert_eq!(decoded, Some(sort));
}

/// Invalid tag returns None.
#[test]
#[timeout(30000)]
fn test_sort_tag_from_invalid_returns_none() {
    assert_eq!(AYEncoder::closure_sort_from_tag(""), None);
    assert_eq!(AYEncoder::closure_sort_from_tag("z"), None);
    assert_eq!(AYEncoder::closure_sort_from_tag("bb"), None);
}

/// Odd-length hex after 'c' prefix is invalid.
#[test]
#[timeout(30000)]
fn test_sort_tag_closure_env_odd_hex_returns_none() {
    // 'c' followed by odd number of hex chars
    assert_eq!(AYEncoder::closure_sort_from_tag("c4"), None);
}

/// Non-hex characters after 'c' prefix are invalid.
#[test]
#[timeout(30000)]
fn test_sort_tag_closure_env_non_hex_returns_none() {
    // "zz" is not valid hex
    assert_eq!(AYEncoder::closure_sort_from_tag("czz"), None);
}

// ── body_has_postcondition_mut_with_var tests ────────────────────────

/// Direct postcondition_mut call with the target variable in args returns true.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_direct_match() {
    let body = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// postcondition_mut call that does NOT reference the target variable returns false.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_no_match() {
    let body = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(
        &body, "missing"
    ));
}

/// Recurses through BinOp(And) to find nested postcondition_mut.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_through_binop() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = and(bool_expr(true), inner);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Recurses through Ite branches.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_through_ite() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = ite(bool_expr(true), int(0), inner);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Recurses through Let binding.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_through_let() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = let_bind("mid", logic_fn_call("helper", vec![var("x")]), inner);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Let binding that shadows the target variable prevents detection in the body.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_shadowed_by_let() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    // Let binds "s" — shadows the target variable in the body.
    let body = let_bind("s", int(0), inner);
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Forall quantifier that shadows the target variable prevents detection.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_shadowed_by_forall() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = forall("s", inner);
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Exists quantifier that shadows the target variable prevents detection.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_shadowed_by_exists() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = exists("s", inner);
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Closure parameter that shadows the target variable prevents detection.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_shadowed_by_closure() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = PureExpr::Closure {
        params: vec![("s".to_string(), None)],
        body: Arc::new(inner),
    };
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Match arm with pattern that binds the target variable prevents detection.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_shadowed_by_match_pattern() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = match_expr(var("x"), vec![(Pattern::Binding("s".to_string()), inner)]);
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Recurses through LetAssume.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_through_let_assume() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = let_assume(bool_expr(true), inner);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Recurses through LetObligation.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_through_let_obligation() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = let_obligation(bool_expr(true), inner);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Recurses through LogicFnCall args.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_through_logic_fn_call() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = logic_fn_call("wrapper", vec![inner]);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

/// Leaf expressions (Bool, Int, Var) return false.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_leaf_returns_false() {
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(
        &bool_expr(true),
        "s"
    ));
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(
        &int(42),
        "s"
    ));
    assert!(!AYEncoder::body_has_postcondition_mut_with_var(
        &var("s"),
        "s"
    ));
}

/// Non-postcondition_mut MethodCall recurses into receiver and args.
#[test]
#[timeout(30000)]
fn test_body_has_pcm_with_var_non_pcm_method_recurses() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = method_call(var("x"), "some_method", vec![inner]);
    assert!(AYEncoder::body_has_postcondition_mut_with_var(&body, "s"));
}

// ── body_has_any_postcondition_mut tests ─────────────────────────────

/// Direct postcondition_mut call returns true.
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_direct() {
    let body = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    assert!(AYEncoder::body_has_any_postcondition_mut(&body));
}

/// Non-postcondition_mut MethodCall returns false if no nested pcm.
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_non_pcm_method_returns_false() {
    let body = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    assert!(!AYEncoder::body_has_any_postcondition_mut(&body));
}

/// Nested through quantifier — does NOT respect shadowing (unlike _with_var).
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_through_quantifier_no_shadow() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = exists("s", inner);
    // body_has_any_postcondition_mut ignores variable names entirely.
    assert!(AYEncoder::body_has_any_postcondition_mut(&body));
}

/// Nested through Closure body.
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_through_closure() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = PureExpr::Closure {
        params: vec![],
        body: Arc::new(inner),
    };
    assert!(AYEncoder::body_has_any_postcondition_mut(&body));
}

/// Leaf expressions return false.
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_leaf_returns_false() {
    assert!(!AYEncoder::body_has_any_postcondition_mut(&bool_expr(true)));
    assert!(!AYEncoder::body_has_any_postcondition_mut(&int(42)));
    assert!(!AYEncoder::body_has_any_postcondition_mut(&var("x")));
}

/// Nested through BinOp, Ite, Let, Match, LogicFnCall, LetAssume, LetObligation.
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_through_various_wrappers() {
    let pcm = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );

    // Through BinOp
    assert!(AYEncoder::body_has_any_postcondition_mut(&and(
        bool_expr(true),
        pcm.clone()
    )));

    // Through Ite
    assert!(AYEncoder::body_has_any_postcondition_mut(&ite(
        bool_expr(true),
        pcm.clone(),
        int(0)
    )));

    // Through Let
    assert!(AYEncoder::body_has_any_postcondition_mut(&let_bind(
        "x",
        int(0),
        pcm.clone()
    )));

    // Through Match
    assert!(AYEncoder::body_has_any_postcondition_mut(&match_expr(
        var("x"),
        vec![(Pattern::Wildcard, pcm.clone())]
    )));

    // Through LogicFnCall
    assert!(AYEncoder::body_has_any_postcondition_mut(&logic_fn_call(
        "f",
        vec![pcm.clone()]
    )));

    // Through LetAssume
    assert!(AYEncoder::body_has_any_postcondition_mut(&let_assume(
        bool_expr(true),
        pcm.clone()
    )));

    // Through LetObligation
    assert!(AYEncoder::body_has_any_postcondition_mut(&let_obligation(
        bool_expr(true),
        pcm
    )));
}

/// UnOp/Deref/Old/Final/View wrappers are traversed.
#[test]
#[timeout(30000)]
fn test_body_has_any_pcm_through_unary_wrappers() {
    let pcm = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );

    assert!(AYEncoder::body_has_any_postcondition_mut(&not(pcm.clone())));
    assert!(AYEncoder::body_has_any_postcondition_mut(&deref(
        pcm.clone()
    )));
    assert!(AYEncoder::body_has_any_postcondition_mut(&old(pcm.clone())));
    assert!(AYEncoder::body_has_any_postcondition_mut(&final_expr(
        pcm.clone()
    )));
    assert!(AYEncoder::body_has_any_postcondition_mut(&view(pcm)));
}

// ── scan_postcondition_context tests (#2694) ─────────────────────────

/// Empty requires and body_assumptions produce all-false flags.
#[test]
#[timeout(30000)]
fn test_scan_context_empty_returns_all_false() {
    let flags = AYEncoder::scan_postcondition_context(&[], &[]);
    assert!(!flags.has_any);
    assert!(!flags.has_mut);
    assert!(!flags.has_once);
}

/// A `precondition` call sets has_any but not has_mut or has_once.
#[test]
#[timeout(30000)]
fn test_scan_context_precondition_sets_has_any_only() {
    let expr = method_call(var("f"), "precondition", vec![var("a")]);
    let flags = AYEncoder::scan_postcondition_context(&[expr], &[]);
    assert!(flags.has_any, "precondition should set has_any");
    assert!(!flags.has_mut, "precondition should not set has_mut");
    assert!(!flags.has_once, "precondition should not set has_once");
}

/// A `postcondition` call sets has_any but not has_mut or has_once.
#[test]
#[timeout(30000)]
fn test_scan_context_postcondition_sets_has_any_only() {
    let expr = method_call(var("f"), "postcondition", vec![var("a"), var("r")]);
    let flags = AYEncoder::scan_postcondition_context(&[expr], &[]);
    assert!(flags.has_any, "postcondition should set has_any");
    assert!(!flags.has_mut, "postcondition should not set has_mut");
    assert!(!flags.has_once, "postcondition should not set has_once");
}

/// A `postcondition_mut` call sets both has_any and has_mut.
#[test]
#[timeout(30000)]
fn test_scan_context_postcondition_mut_sets_has_any_and_has_mut() {
    let expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let flags = AYEncoder::scan_postcondition_context(&[expr], &[]);
    assert!(flags.has_any, "postcondition_mut should set has_any");
    assert!(flags.has_mut, "postcondition_mut should set has_mut");
    assert!(!flags.has_once, "postcondition_mut should not set has_once");
}

/// A `postcondition_once` call sets both has_any and has_once.
#[test]
#[timeout(30000)]
fn test_scan_context_postcondition_once_sets_has_any_and_has_once() {
    let expr = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    let flags = AYEncoder::scan_postcondition_context(&[expr], &[]);
    assert!(flags.has_any, "postcondition_once should set has_any");
    assert!(!flags.has_mut, "postcondition_once should not set has_mut");
    assert!(flags.has_once, "postcondition_once should set has_once");
}

/// All three postcondition types in context saturate all flags.
#[test]
#[timeout(30000)]
fn test_scan_context_all_three_postcondition_types() {
    let pc = method_call(var("f"), "postcondition", vec![var("a"), var("r")]);
    let pm = method_call(
        var("g"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let po = method_call(var("h"), "postcondition_once", vec![var("a"), var("r")]);
    let flags = AYEncoder::scan_postcondition_context(&[pc, pm, po], &[]);
    assert!(flags.has_any);
    assert!(flags.has_mut);
    assert!(flags.has_once);
}

/// Non-postcondition method calls leave all flags false.
#[test]
#[timeout(30000)]
fn test_scan_context_non_postcondition_methods_returns_all_false() {
    let expr1 = method_call(var("f"), "len", vec![]);
    let expr2 = method_call(var("g"), "get", vec![var("k")]);
    let flags = AYEncoder::scan_postcondition_context(&[expr1, expr2], &[]);
    assert!(!flags.has_any);
    assert!(!flags.has_mut);
    assert!(!flags.has_once);
}

/// Postcondition calls in body_assumptions (not requires) are detected.
#[test]
#[timeout(30000)]
fn test_scan_context_detects_postcondition_in_body_assumptions() {
    let expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let flags = AYEncoder::scan_postcondition_context(&[], &[&expr]);
    assert!(flags.has_any);
    assert!(flags.has_mut);
}

/// Postcondition call nested inside an existential is detected.
#[test]
#[timeout(30000)]
fn test_scan_context_nested_in_existential() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("st"), var("r")],
    );
    let body = exists("st", inner);
    let flags = AYEncoder::scan_postcondition_context(&[body], &[]);
    assert!(flags.has_any);
    assert!(flags.has_mut);
}

/// Leaf expressions produce all-false flags.
#[test]
#[timeout(30000)]
fn test_scan_context_leaf_expressions_return_all_false() {
    let flags = AYEncoder::scan_postcondition_context(&[bool_expr(true), int(42), var("x")], &[]);
    assert!(!flags.has_any);
    assert!(!flags.has_mut);
    assert!(!flags.has_once);
}

/// Consolidated scan agrees with individual function results.
#[test]
#[timeout(30000)]
fn test_scan_context_agrees_with_individual_functions() {
    let expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let requires = &[expr];
    let body_assumptions: &[&PureExpr] = &[];

    let flags = AYEncoder::scan_postcondition_context(requires, body_assumptions);

    // Verify agreement with individual functions
    let any_individual = requires
        .iter()
        .any(|e| AYEncoder::body_has_any_closure_postcondition(e));
    let mut_individual = requires
        .iter()
        .any(|e| AYEncoder::body_has_any_postcondition_mut(e));
    let once_individual = requires
        .iter()
        .any(|e| AYEncoder::body_has_any_postcondition_once(e));

    assert_eq!(flags.has_any, any_individual, "has_any disagreement");
    assert_eq!(flags.has_mut, mut_individual, "has_mut disagreement");
    assert_eq!(flags.has_once, once_individual, "has_once disagreement");
}
