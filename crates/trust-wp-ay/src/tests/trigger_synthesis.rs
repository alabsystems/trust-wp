// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trigger synthesis unit tests.
//!
//! Extracted from `encoder/trigger.rs` inline test module (#1669).
//! Tests cover `synthesize_triggers`, `collect_nested_quantifier_vars`,
//! `expr_mentions_any_var`, `collect_trigger_candidates`, and related
//! helpers for E-matching trigger pattern generation.

use std::{collections::HashSet, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::{Pattern, PureExpr};

use crate::{
    encoder::{
        quantifier::QuantifierKind,
        trigger::{
            collect_nested_quantifier_vars, collect_trigger_candidates, expr_mentions_any_var,
            synthesize_triggers,
        },
    },
    tests::helpers::*,
};

mod basic_trigger_synthesis;

/// Trigger synthesis through NOT wrapper — the De Morgan path.
///
/// When `negate_existential_postcondition` rewrites `exists<a> P(a)` to
/// `forall<a> NOT P(a)`, the resulting body is `UnOp(Not, P(a))`.
/// `collect_trigger_candidates` must recurse through the NOT to find
/// trigger candidates inside P(a).
///
/// Re: #1018 trigger synthesis audit, De Morgan soundness verification.
#[test]
#[timeout(30000)]
fn test_synthesize_finds_trigger_through_not_wrapper() {
    // Body: NOT(f(i) > 0) — simulates De Morgan output
    let inner = gt(logic_fn_call("f", vec![var("i")]), int(0));
    let body = not(inner);
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(triggers.len(), 1, "should find trigger through NOT wrapper");
    assert_eq!(triggers[0].len(), 1);
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "f", "trigger should be f(i) found through NOT");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], var("i"));
        }
        _ => panic!(
            "expected LogicFnCall trigger f(i), got: {:?}",
            triggers[0][0]
        ),
    }
}

/// Multi-variable trigger synthesis through NOT wrapper.
///
/// De Morgan for consecutive existentials: `exists<a> exists<b> P(a,b)`
/// becomes `forall<a> forall<b> NOT P(a,b)`. After collapse, the
/// synthesizer receives `vars = ["a", "b"]` and `body = NOT P(a,b)`.
/// It must find triggers through the NOT that cover both variables.
///
/// Re: #1018, #1134 (multi-variable Bool expansion gap).
#[test]
#[timeout(30000)]
fn test_synthesize_multi_var_through_not_wrapper() {
    // Body: NOT(g(a, b) > 0) — simulates De Morgan of nested exists
    let inner = gt(logic_fn_call("g", vec![var("a"), var("b")]), int(0));
    let body = not(inner);
    let vars = vec!["a".to_string(), "b".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should find trigger through NOT covering both vars"
    );
    assert_eq!(triggers[0].len(), 1);
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "g", "trigger should be g(a,b) found through NOT");
            assert_eq!(args.len(), 2);
        }
        _ => panic!(
            "expected LogicFnCall trigger g(a,b), got: {:?}",
            triggers[0][0]
        ),
    }
}

/// Coverage check with duplicate variable names (#1140).
///
/// When `collect_nested_quantifier_vars` returns duplicate names (from
/// `forall<i> forall<i> f(i) > 0`), trigger synthesis must collapse them
/// onto one logical coverage slot. A candidate covering `"i"` still counts
/// as full coverage for the degenerate `["i", "i"]` binder list.
#[test]
#[timeout(30000)]
fn test_synthesize_duplicate_var_names_coverage() {
    // forall<i> forall<i> f(i) > 0 — same-name shadowing
    let body = gt(logic_fn_call("f", vec![var("i")]), int(0));
    let vars = vec!["i".to_string(), "i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "duplicate var names should still produce a trigger"
    );
    assert_eq!(triggers[0].len(), 1);
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, .. } => {
            assert_eq!(name, "f", "trigger should be f(i)");
        }
        _ => panic!("expected LogicFnCall trigger"),
    }
}

/// Pair coverage also respects duplicate-name collapse.
///
/// With `vars = ["i", "i", "j"]`, the trigger pair `{f(i), g(j)}` should
/// cover the two unique names `{i, j}` and synthesize a multi-trigger.
#[test]
#[timeout(30000)]
fn test_synthesize_pair_coverage_with_duplicate_var_names() {
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        gt(logic_fn_call("g", vec![var("j")]), int(0)),
    );
    let vars = vec!["i".to_string(), "i".to_string(), "j".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "duplicate-name binders should still synthesize one multi-trigger"
    );
    assert_eq!(
        triggers[0].len(),
        2,
        "pair should cover the unique names i and j"
    );
    let names: HashSet<_> = triggers[0]
        .iter()
        .filter_map(|trigger| match trigger {
            PureExpr::LogicFnCall { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(names.contains("f"), "multi-trigger should contain f(i)");
    assert!(names.contains("g"), "multi-trigger should contain g(j)");
}

/// Verify that partial-coverage single trigger does not falsely claim
/// full coverage for multi-variable quantifiers.
///
/// When `vars = ["i", "j"]` and the only trigger candidate covers just `"i"`,
/// the full-coverage check must fail (`{"i"} != {"i","j"}`). The fallback
/// path should emit a partial trigger (#1140).
///
/// Re: algorithm audit — trigger synthesis coverage boundary
#[test]
#[timeout(30000)]
fn test_synthesize_partial_coverage_not_falsely_full() {
    // forall<i, j> f(i) > 0 AND j > 0
    // f(i) covers only "i", not "j" — partial coverage
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        gt(var("j"), int(0)),
    );
    let vars = vec!["i".to_string(), "j".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should produce one trigger pattern (partial)"
    );
    // The trigger should be f(i) — the only candidate.
    // It covers ["i"] (len=1), not ["i", "j"] (len=2).
    assert_eq!(triggers[0].len(), 1, "single partial trigger");
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "f");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("expected LogicFnCall trigger, got {:?}", triggers[0][0]),
    }
}

/// Verify that pair coverage tracks the union of covered variable names.
///
/// When two candidates each cover one variable and together cover all vars,
/// the pair search must find the combined coverage. This test ensures the
/// O(n^2) pair search works correctly.
#[test]
#[timeout(30000)]
fn test_synthesize_pair_coverage_finds_complete_pair() {
    // forall<i, j> f(i) > 0 AND g(j) > 0
    // f(i) covers "i", g(j) covers "j" — together they cover ["i", "j"]
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        gt(logic_fn_call("g", vec![var("j")]), int(0)),
    );
    let vars = vec!["i".to_string(), "j".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should produce one multi-pattern trigger"
    );
    assert_eq!(
        triggers[0].len(),
        2,
        "multi-pattern should contain two terms"
    );
    // Both f(i) and g(j) should be in the pattern (order may vary by score)
    let names: HashSet<String> = triggers[0]
        .iter()
        .filter_map(|t| match t {
            PureExpr::LogicFnCall { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    assert!(
        names.contains("f") && names.contains("g"),
        "pair should contain f and g, got {:?}",
        names
    );
}

/// Inner-only candidates are excluded even though we descend into nested
/// quantifier bodies (#1118).
///
/// Given `f(i) > 0 AND forall<j> g(j) > 0` with bound var `i`:
/// - `f(i)` should be found (top-level, mentions `i`)
/// - `g(j)` should NOT be found (only references inner `j`, not outer `i`)
#[test]
#[timeout(30000)]
fn test_collect_trigger_candidates_excludes_inner_only_nested_quantifier_term() {
    // Body: f(i) > 0 AND forall<j> g(j) > 0
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        PureExpr::Forall {
            var: "j".to_string(),
            var_sort: None,
            body: Arc::new(gt(logic_fn_call("g", vec![var("j")]), int(0))),
            triggers: vec![],
        },
    );
    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    // Only f(i) should be collected — g(j) lives in the forall body but
    // references only inner `j`, not outer `i`.
    assert_eq!(
        candidates.len(),
        1,
        "should find exactly 1 candidate (f(i)), got {}",
        candidates.len()
    );
    match &candidates[0].expr {
        PureExpr::LogicFnCall { name, .. } => {
            assert_eq!(name, "f", "candidate should be f(i), got {name}");
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

/// After #1118, candidates inside nested quantifier bodies that reference
/// outer-scope variables ARE collected.
///
/// Given `f(i) > 0 AND exists<j> g(i) > j` with bound var `i`:
/// - `f(i)` should be found (top-level, mentions `i`)
/// - `g(i)` should ALSO be found (inside exists<j>, but mentions outer `i`)
#[test]
#[timeout(30000)]
fn test_collect_trigger_candidates_descends_into_exists_for_outer_vars() {
    let body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        PureExpr::Exists {
            var: "j".to_string(),
            var_sort: None,
            body: Arc::new(gt(logic_fn_call("g", vec![var("i")]), var("j"))),
            triggers: vec![],
        },
    );
    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        2,
        "should find 2 candidates (f(i) and g(i)), got {}",
        candidates.len()
    );
    let names: Vec<&str> = candidates
        .iter()
        .map(|c| match c.expr {
            PureExpr::LogicFnCall { ref name, .. } => name.as_str(),
            _ => panic!("expected LogicFnCall, got {:?}", c.expr),
        })
        .collect();
    assert!(names.contains(&"f"), "should contain f, got {names:?}");
    assert!(names.contains(&"g"), "should contain g, got {names:?}");
}

/// AC1 from #1118: `forall<i> exists<j> f(i, j)` produces f(i, j) as a
/// trigger candidate for the outer forall because it references outer var `i`.
#[test]
#[timeout(30000)]
fn test_nested_exists_candidate_with_both_vars_found_for_outer_1118() {
    // forall<i> exists<j> f(i, j) > 0
    let body = PureExpr::Exists {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(gt(logic_fn_call("f", vec![var("i"), var("j")]), int(0))),
        triggers: vec![],
    };
    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        1,
        "should find f(i, j) as trigger for outer var i, got {}",
        candidates.len()
    );
    match &candidates[0].expr {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "f", "candidate should be f(i, j), got {name}");
            assert_eq!(args.len(), 2, "f should have 2 args (i, j)");
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

/// AC2 from #1118: inner-only candidates (e.g., `g(j)`) are NOT added
/// as outer triggers when they don't reference any outer-scope variable.
#[test]
#[timeout(30000)]
fn test_inner_only_candidate_excluded_from_outer_triggers_1118() {
    // forall<i> exists<j> (f(i) > 0 AND g(j) > 0)
    let inner_body = and(
        gt(logic_fn_call("f", vec![var("i")]), int(0)),
        gt(logic_fn_call("g", vec![var("j")]), int(0)),
    );
    let body = PureExpr::Exists {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(inner_body),
        triggers: vec![],
    };
    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    // f(i) should be found (references outer `i`), g(j) should NOT (only inner `j`)
    assert_eq!(
        candidates.len(),
        1,
        "should find only f(i), not g(j), got {}",
        candidates.len()
    );
    match &candidates[0].expr {
        PureExpr::LogicFnCall { name, .. } => {
            assert_eq!(name, "f", "candidate should be f(i), got {name}");
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

/// Deref-wrapped MethodCall trigger candidate preserves the Deref wrapper.
///
/// Regression test for #1142: before the fix, `Deref(MethodCall(seq, "index_logic", [i]))`
/// would strip Deref and return the inner MethodCall as the candidate. The body encoder
/// pushes Deref into the receiver (producing `index_logic(seq_current, i)`), but the
/// unwrapped trigger encodes as `index_logic(seq, i)` — ay E-matching never fires.
///
/// After the fix, the candidate is `Deref(MethodCall(...))`, ensuring the trigger
/// and body encode to the same ay term.
#[test]
#[timeout(30000)]
fn deref_wrapped_method_call_preserves_wrapper_1142() {
    // Deref(seq.index_logic(i))
    let inner_mc = method_call(var("seq"), "index_logic", vec![var("i")]);
    let deref_mc = PureExpr::Deref(Arc::new(inner_mc));
    let body = gt(deref_mc, int(0));

    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        1,
        "should find exactly 1 candidate, got {}",
        candidates.len()
    );
    assert!(
        matches!(candidates[0].expr, PureExpr::Deref(_)),
        "candidate should be Deref(MethodCall(...)), got {:?}",
        candidates[0].expr
    );
}

/// Final-wrapped LogicFnCall trigger candidate preserves the Final wrapper.
///
/// Same structural fix as Deref case: `Final(f(i))` should produce a trigger
/// `Final(f(i))`, not the unwrapped `f(i)`.
///
/// Re: #1142
#[test]
#[timeout(30000)]
fn final_wrapped_logic_fn_call_preserves_wrapper_1142() {
    // Final(f(i))
    let inner_lfc = logic_fn_call("f", vec![var("i")]);
    let final_lfc = PureExpr::Final(Arc::new(inner_lfc));
    let body = gt(final_lfc, int(0));

    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        1,
        "should find exactly 1 candidate, got {}",
        candidates.len()
    );
    assert!(
        matches!(candidates[0].expr, PureExpr::Final(_)),
        "candidate should be Final(LogicFnCall(...)), got {:?}",
        candidates[0].expr
    );
}

/// View-wrapped MethodCall trigger candidate preserves the View wrapper.
///
/// Same structural fix as Deref/Final: `View(seq.index_logic(i))` should
/// produce a trigger `View(seq.index_logic(i))`.
///
/// Re: #1142
#[test]
#[timeout(30000)]
fn view_wrapped_method_call_preserves_wrapper_1142() {
    // View(seq.index_logic(i))
    let inner_mc = method_call(var("seq"), "index_logic", vec![var("i")]);
    let view_mc = PureExpr::View(Arc::new(inner_mc));
    let body = gt(view_mc, int(0));

    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        1,
        "should find exactly 1 candidate, got {}",
        candidates.len()
    );
    assert!(
        matches!(candidates[0].expr, PureExpr::View(_)),
        "candidate should be View(MethodCall(...)), got {:?}",
        candidates[0].expr
    );
}

/// Non-function Deref/Final/View inner expressions still recurse normally.
///
/// `Deref(BinOp(f(i), +, 1))` should find the inner `f(i)` as the candidate
/// (the Deref wraps a non-function expression, so standard recursion applies).
#[test]
#[timeout(30000)]
fn deref_wrapped_non_function_recurses_normally() {
    // Deref(f(i) + 1)
    let inner = binop(
        logic_fn_call("f", vec![var("i")]),
        trust_wp_core::formula::BinOp::Add,
        int(1),
    );
    let deref_expr = PureExpr::Deref(Arc::new(inner));
    let body = gt(deref_expr, int(0));

    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        1,
        "should find f(i) through Deref(BinOp), got {}",
        candidates.len()
    );
    assert!(
        matches!(candidates[0].expr, PureExpr::LogicFnCall { .. }),
        "candidate should be LogicFnCall, got {:?}",
        candidates[0].expr
    );
}

/// Closure parameter that shadows a quantifier variable must not produce
/// trigger coverage for the outer quantifier.
///
/// `forall<i> |i| f(i) > 0` — the closure param `i` shadows the forall
/// variable `i`. The `f(i)` inside the closure references the closure
/// parameter, not the quantifier variable. Synthesis should find NO
/// trigger candidate for the outer quantifier's `i`.
///
/// Re: #1018 trigger synthesis edge case audit.
#[test]
#[timeout(30000)]
fn test_synthesize_closure_param_shadows_quantifier_var() {
    // forall<i> |i| f(i) > 0
    // Closure param `i` shadows the quantifier-bound `i`.
    let closure_body = gt(logic_fn_call("f", vec![var("i")]), int(0));
    let body = PureExpr::Closure {
        params: vec![("i".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert!(
        triggers.is_empty(),
        "closure param shadowing quantifier var should produce no trigger, got {:?}",
        triggers
    );
}

/// Triple nested same-kind exists with a single function call covering
/// all three variables.
///
/// `exists<i> exists<j> exists<k> g(i, j, k) > 0`
/// `collect_nested_quantifier_vars` gathers [i, j, k], then
/// `synthesize_triggers` should find `g(i, j, k)` as a single trigger
/// covering all three variables.
///
/// Re: #1018 trigger synthesis edge case audit.
#[test]
#[timeout(30000)]
fn test_synthesize_triple_nested_exists_full_coverage() {
    // Body of the innermost exists: g(i, j, k) > 0
    let body = gt(
        logic_fn_call("g", vec![var("i"), var("j"), var("k")]),
        int(0),
    );
    let vars = vec!["i".to_string(), "j".to_string(), "k".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should synthesize exactly one trigger pattern for 3-var coverage"
    );
    assert_eq!(
        triggers[0].len(),
        1,
        "single function call covers all 3 vars"
    );
    match &triggers[0][0] {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "g");
            assert_eq!(args.len(), 3);
            assert_eq!(args[0], var("i"));
            assert_eq!(args[1], var("j"));
            assert_eq!(args[2], var("k"));
        }
        other => panic!("expected LogicFnCall trigger g(i,j,k), got: {:?}", other),
    }
}

/// `collect_nested_quantifier_vars` stops when inner quantifier has
/// user-provided triggers.
///
/// `exists<a> exists<b: triggers=[user_t]> f(a, b) > 0`
/// Only `a` should be collected (inner `b` has non-empty triggers).
/// Synthesis runs on the outer single-var `a` scope.
///
/// Re: #1018 trigger synthesis edge case audit.
#[test]
#[timeout(30000)]
fn test_collect_nested_vars_stops_at_user_triggered_inner() {
    // exists<b: triggers=[g(b)]> f(a, b) > 0
    let inner_body = gt(logic_fn_call("f", vec![var("a"), var("b")]), int(0));
    let inner_exists = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: None,
        body: Arc::new(inner_body),
        triggers: vec![vec![logic_fn_call("g", vec![var("b")])]],
    };
    // collect_nested_quantifier_vars starting from outer exists<a>
    let (vars, body) = collect_nested_quantifier_vars(QuantifierKind::Exists, "a", &inner_exists);
    assert_eq!(
        vars,
        vec!["a".to_string()],
        "should collect only 'a' — inner 'b' has user triggers"
    );
    // The returned body should be the inner exists (not unwrapped)
    assert!(
        matches!(body, PureExpr::Exists { var, triggers, .. } if var == "b" && !triggers.is_empty()),
        "body should be the user-triggered exists<b>, got: {:?}",
        body
    );
}

/// Greedy set-cover for 3-variable quantifiers (#1143).
///
/// `forall<i, j, k> f(i) > 0 AND g(j) > 0 AND h(k) > 0`
///
/// No single candidate covers all three variables. No pair covers all three.
/// The greedy set-cover should find the triple {f(i), g(j), h(k)} as a
/// multi-pattern trigger covering all bound variables.
#[test]
#[timeout(30000)]
fn test_synthesize_triple_trigger_greedy_set_cover() {
    let body = and(
        and(
            gt(logic_fn_call("f", vec![var("i")]), int(0)),
            gt(logic_fn_call("g", vec![var("j")]), int(0)),
        ),
        gt(logic_fn_call("h", vec![var("k")]), int(0)),
    );
    let vars = vec!["i".to_string(), "j".to_string(), "k".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should synthesize exactly one multi-pattern trigger"
    );
    assert_eq!(
        triggers[0].len(),
        3,
        "multi-pattern should contain three terms covering i, j, k"
    );
    // Verify all three variables are covered by the trigger set
    let trigger_names: Vec<&str> = triggers[0]
        .iter()
        .filter_map(|t| match t {
            PureExpr::LogicFnCall { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(trigger_names.contains(&"f"), "triggers should include f(i)");
    assert!(trigger_names.contains(&"g"), "triggers should include g(j)");
    assert!(trigger_names.contains(&"h"), "triggers should include h(k)");
}

/// Greedy set-cover prefers fewer triggers when a 2-candidate pair covers
/// 3 variables.
///
/// `forall<i, j, k> f(i, j) > 0 AND h(k) > 0`
///
/// f(i,j) covers {i, j}, h(k) covers {k}. The pair (f, h) covers all three.
/// The pair search should find this — the greedy path is not needed here.
#[test]
#[timeout(30000)]
fn test_synthesize_pair_covers_three_vars() {
    let body = and(
        gt(logic_fn_call("f", vec![var("i"), var("j")]), int(0)),
        gt(logic_fn_call("h", vec![var("k")]), int(0)),
    );
    let vars = vec!["i".to_string(), "j".to_string(), "k".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(triggers.len(), 1, "should find one multi-pattern trigger");
    assert_eq!(
        triggers[0].len(),
        2,
        "pair search should cover all 3 vars with 2 terms"
    );
}

/// Closure postcondition pattern: `forall<i> exists<st> f.postcondition_mut(i, st, res)`
/// must find `postcondition_mut(f, i, st, res)` as a trigger for the outer `forall<i>`.
///
/// After #1118, `collect_trigger_candidates` descends into the `exists<st>` body
/// with `st` shadowed. The `postcondition_mut` call references outer `i`, so it
/// IS collected as a candidate. This closes the trigger starvation gap from #1281.
///
/// Re: #1281, #1118
#[test]
#[timeout(30000)]
fn test_forall_exists_postcondition_mut_trigger_not_starved_1281() {
    // forall<i> exists<st> f.postcondition_mut(i, st, res) > 0
    // The outer forall binds `i`. The inner exists binds `st`.
    // postcondition_mut(f, i, st, res) mentions outer `i`, so it should be found.
    let pc_call = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("i"), var("st"), var("res")],
    );
    let exists_body = gt(pc_call, int(0));
    let body = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(exists_body),
        triggers: vec![],
    };
    let vars = vec!["i".to_string()];
    let mut candidates = Vec::new();
    collect_trigger_candidates(&body, &vars, &mut HashSet::new(), 0, &mut candidates);

    assert_eq!(
        candidates.len(),
        1,
        "should find postcondition_mut(f, i, st, res) as trigger for outer `i`, got {}",
        candidates.len()
    );
    match &candidates[0].expr {
        PureExpr::MethodCall { method, .. } => {
            assert_eq!(
                method, "postcondition_mut",
                "candidate should be postcondition_mut, got {method}"
            );
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

/// Full synthesis pipeline for the closure postcondition pattern from #1281.
///
/// `forall<i> exists<st> f.postcondition_mut(i, st, res)` should produce
/// a single-term trigger `[postcondition_mut(f, i, st, res)]` for the outer forall.
///
/// Re: #1281, #1118
#[test]
#[timeout(30000)]
fn test_synthesize_forall_exists_closure_postcondition_trigger_1281() {
    let pc_call = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("i"), var("st"), var("res")],
    );
    let body = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(gt(pc_call, int(0))),
        triggers: vec![],
    };
    let vars = vec!["i".to_string()];
    let triggers = synthesize_triggers(&vars, &body);
    assert_eq!(
        triggers.len(),
        1,
        "should synthesize exactly 1 trigger pattern for outer forall, got {}",
        triggers.len()
    );
    assert_eq!(
        triggers[0].len(),
        1,
        "trigger should be a single-term pattern, got {}",
        triggers[0].len()
    );
    match &triggers[0][0] {
        PureExpr::MethodCall { method, .. } => {
            assert_eq!(
                method, "postcondition_mut",
                "trigger term should be postcondition_mut, got {method}"
            );
        }
        other => panic!("expected MethodCall trigger term, got {other:?}"),
    }
}
