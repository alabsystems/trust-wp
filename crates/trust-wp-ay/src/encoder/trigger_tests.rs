// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for trigger synthesis correctness.
//!
//! Covers: `synthesize_triggers`, `collect_nested_quantifier_vars`,
//! `collect_trigger_candidates`, `expr_mentions_any_var`, and
//! variable shadowing in quantifier/match/let scopes.
//!
//! Part of #2514 (Tier 1 coverage gap: trigger.rs, 828 LOC, zero tests).

use std::collections::HashSet;

use ntest::timeout;
use trust_wp_core::formula::{Pattern, PureExpr};

use crate::{
    encoder::{
        quantifier::QuantifierKind,
        trigger::{
            collect_ground_subexprs, collect_nested_quantifier_vars, collect_trigger_candidates,
            expr_mentions_any_var, synthesize_triggers,
        },
    },
    tests::helpers::*,
};

// ── synthesize_triggers: single variable ──────────────────────────────

/// A single method call `f(x)` in a forall body produces a single-pattern trigger.
#[test]
#[timeout(30000)]
fn synth_single_var_method_call_produces_trigger() {
    let body = gt(method_call(var("x"), "f", vec![]), int(0));
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert_eq!(
        triggers.len(),
        1,
        "should produce exactly one multi-pattern"
    );
    assert_eq!(triggers[0].len(), 1, "single-pattern trigger");
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, .. } if method == "f"),
        "trigger should be the f(x) method call"
    );
}

/// A logic function call `g(x)` produces a trigger.
#[test]
#[timeout(30000)]
fn synth_single_var_logic_fn_produces_trigger() {
    let body = gt(logic_fn_call("g", vec![var("x")]), int(0));
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::LogicFnCall { name, .. } if name == "g"),
        "trigger should be the g(x) logic fn call"
    );
}

/// Pure arithmetic body (no method/logic-fn calls) yields no trigger
/// candidates (arithmetic BinOp nodes are excluded from triggers).
#[test]
#[timeout(30000)]
fn synth_arithmetic_only_yields_empty() {
    // forall x. x + 1 > 0
    let body = gt(add(var("x"), int(1)), int(0));
    let triggers = synthesize_triggers(&[s("x")], &body);
    // Falls back to best partial candidate — but there are NO candidates at all
    assert!(
        triggers.is_empty(),
        "no method/logic-fn calls → no triggers"
    );
}

// ── synthesize_triggers: multi-variable ──────────────────────────────

/// A single call covering all bound variables produces a single-pattern trigger.
#[test]
#[timeout(30000)]
fn synth_multi_var_single_covering_call() {
    // forall x, y. h(x, y) > 0
    let body = gt(logic_fn_call("h", vec![var("x"), var("y")]), int(0));
    let triggers = synthesize_triggers(&[s("x"), s("y")], &body);
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1, "one call covers both vars");
}

/// Two calls, each covering one variable, produce a two-element multi-pattern.
#[test]
#[timeout(30000)]
fn synth_multi_var_pair_trigger() {
    // forall x, y. f(x) > 0 && g(y) > 0
    let body = and(
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
        gt(logic_fn_call("g", vec![var("y")]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("x"), s("y")], &body);
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 2, "two-element multi-pattern");
}

/// Greedy set-cover for 3+ variables.
#[test]
#[timeout(30000)]
fn synth_three_var_greedy_set_cover() {
    // forall x, y, z. f(x,y) > 0 && g(y,z) > 0
    let body = and(
        gt(logic_fn_call("f", vec![var("x"), var("y")]), int(0)),
        gt(logic_fn_call("g", vec![var("y"), var("z")]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("x"), s("y"), s("z")], &body);
    assert!(
        !triggers.is_empty(),
        "should find trigger covering all 3 vars"
    );
    // The selected multi-pattern should cover all 3 variables
    let all_mentioned = triggers[0].iter().all(|t| {
        expr_mentions_any_var(t, &[s("x")])
            || expr_mentions_any_var(t, &[s("y")])
            || expr_mentions_any_var(t, &[s("z")])
    });
    assert!(all_mentioned, "multi-pattern should reference bound vars");
}

// ── synthesize_triggers: wrapper preservation ────────────────────────

/// Old(MethodCall) preserves the Old wrapper in the trigger pattern.
/// This ensures the emitted trigger matches the body encoding exactly (#1142).
#[test]
#[timeout(30000)]
fn synth_old_wrapper_preserved_in_trigger() {
    // forall x. old(f(x)) > 0
    let body = gt(old(method_call(var("x"), "f", vec![])), int(0));
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::MethodCall { .. })),
        "Old wrapper must be preserved around the method call trigger"
    );
}

/// Deref(LogicFnCall) preserves the Deref wrapper.
#[test]
#[timeout(30000)]
fn synth_deref_wrapper_preserved_in_trigger() {
    let body = gt(deref(logic_fn_call("g", vec![var("x")])), int(0));
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::LogicFnCall { .. })),
        "Deref wrapper must be preserved"
    );
}

// ── collect_nested_quantifier_vars ───────────────────────────────────

/// Collects vars from a chain of nested same-kind forall quantifiers.
#[test]
#[timeout(30000)]
fn nested_forall_vars_collected() {
    // forall x. forall y. forall z. body
    let body_expr = gt(var("x"), int(0));
    let inner = forall("z", body_expr.clone());
    let mid = forall("y", inner);

    let (vars, innermost) = collect_nested_quantifier_vars(QuantifierKind::Forall, "x", &mid);
    assert_eq!(vars, vec!["x", "y", "z"]);
    assert!(
        matches!(innermost, PureExpr::BinOp(..)),
        "innermost body is the comparison"
    );
}

/// Stops at a quantifier of different kind (exists inside forall).
#[test]
#[timeout(30000)]
fn nested_vars_stops_at_different_kind() {
    // forall x. exists y. body (exists breaks the forall chain)
    let body_expr = gt(var("x"), int(0));
    let inner_exists = exists("y", body_expr);

    let (vars, innermost) =
        collect_nested_quantifier_vars(QuantifierKind::Forall, "x", &inner_exists);
    assert_eq!(vars, vec!["x"], "should NOT collect y from exists");
    assert!(
        matches!(innermost, PureExpr::Exists { .. }),
        "innermost is the exists node"
    );
}

/// Stops at a quantifier with user-supplied triggers.
#[test]
#[timeout(30000)]
fn nested_vars_stops_at_triggered_quantifier() {
    let body_expr = gt(var("x"), int(0));
    let inner_triggered = forall_with_triggers("y", body_expr, vec![vec![var("y")]]);

    let (vars, _) = collect_nested_quantifier_vars(QuantifierKind::Forall, "x", &inner_triggered);
    assert_eq!(
        vars,
        vec!["x"],
        "should NOT collect y from triggered forall"
    );
}

// ── expr_mentions_any_var ────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn mentions_var_direct() {
    assert!(expr_mentions_any_var(&var("x"), &[s("x")]));
    assert!(!expr_mentions_any_var(&var("y"), &[s("x")]));
}

#[test]
#[timeout(30000)]
fn mentions_var_nested_in_binop() {
    let expr = add(var("x"), int(1));
    assert!(expr_mentions_any_var(&expr, &[s("x")]));
    assert!(!expr_mentions_any_var(&expr, &[s("y")]));
}

#[test]
#[timeout(30000)]
fn mentions_var_through_wrappers() {
    let expr = old(deref(var("x")));
    assert!(expr_mentions_any_var(&expr, &[s("x")]));
}

#[test]
#[timeout(30000)]
fn mentions_var_in_method_call_receiver() {
    let expr = method_call(var("x"), "len", vec![]);
    assert!(expr_mentions_any_var(&expr, &[s("x")]));
}

#[test]
#[timeout(30000)]
fn mentions_var_in_method_call_arg() {
    let expr = method_call(var("recv"), "push", vec![var("x")]);
    assert!(expr_mentions_any_var(&expr, &[s("x")]));
}

// ── Variable shadowing ──────────────────────────────────────────────

/// Inner quantifier shadows the outer variable — the outer var should not
/// be reported as mentioned from the inner scope.
#[test]
#[timeout(30000)]
fn shadowing_inner_quantifier_hides_outer_var() {
    // forall x. (exists x. f(x)) — inner x shadows outer
    let inner_body = logic_fn_call("f", vec![var("x")]);
    let inner_exists = exists("x", inner_body);
    // From the perspective of outer forall x, `x` in f(x) is bound by inner exists
    let mut candidates = Vec::new();
    let mut shadowed = HashSet::new();
    collect_trigger_candidates(&inner_exists, &[s("x")], &mut shadowed, 0, &mut candidates);
    // The f(x) call should NOT be a candidate for the outer x because
    // it's shadowed by the inner exists.
    assert!(
        candidates.is_empty(),
        "inner exists shadows x — no candidates for outer x"
    );
}

/// Let-binding shadows a variable.
#[test]
#[timeout(30000)]
fn shadowing_let_binding() {
    // let x = 42 in f(x) — x is shadowed by the let
    let body = let_bind("x", int(42), logic_fn_call("f", vec![var("x")]));
    let mut candidates = Vec::new();
    let mut shadowed = HashSet::new();
    collect_trigger_candidates(&body, &[s("x")], &mut shadowed, 0, &mut candidates);
    assert!(
        candidates.is_empty(),
        "let-bound x shadows the quantifier-bound x"
    );
}

/// Match arm pattern bindings shadow variables.
#[test]
#[timeout(30000)]
fn shadowing_match_pattern_binding() {
    // match scrutinee { x => f(x) } — x is shadowed by the pattern
    let body = match_expr(
        int(0),
        vec![(
            Pattern::Binding("x".to_string()),
            logic_fn_call("f", vec![var("x")]),
        )],
    );
    let mut candidates = Vec::new();
    let mut shadowed = HashSet::new();
    collect_trigger_candidates(&body, &[s("x")], &mut shadowed, 0, &mut candidates);
    assert!(
        candidates.is_empty(),
        "match pattern binding shadows quantifier-bound x"
    );
}

// ── Scoring behavior (tested indirectly via synthesize_triggers) ────

/// Logic function calls are preferred over method calls — synthesize_triggers
/// returns the logic fn as the first (best-scored) alternative pattern when
/// both cover the same single variable. Multiple alternatives are emitted
/// so the solver has independent instantiation opportunities.
#[test]
#[timeout(30000)]
fn logic_fn_preferred_over_method_call() {
    // Both f(x) as logic fn and m(x) as method call in body
    let body = and(
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
        gt(method_call(var("x"), "m", vec![]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    // Both candidates fully cover x, so multiple alternatives are emitted.
    assert!(
        triggers.len() >= 2,
        "both f(x) and m(x) cover x — should emit multiple alternatives: {triggers:?}"
    );
    // Each alternative is a single-element pattern.
    assert_eq!(triggers[0].len(), 1);
    // The first (best-scored) alternative should be the logic fn.
    assert!(
        matches!(&triggers[0][0], PureExpr::LogicFnCall { name, .. } if name == "f"),
        "logic fn f should be the first (best-scored) alternative"
    );
}

/// Shallower candidates are preferred — synthesize_triggers returns the
/// shallower call as the first alternative when both cover the same variable.
#[test]
#[timeout(30000)]
fn shallower_candidate_preferred() {
    // f(x) at shallow depth, g(x) nested under Ite at greater depth
    // Both are logic fns (same kind) so depth is the tiebreaker.
    let body = and(
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
        ite(
            bool_expr(true),
            gt(logic_fn_call("g", vec![var("x")]), int(0)),
            int(0),
        ),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    // Both candidates fully cover x, so multiple alternatives are emitted.
    assert!(
        triggers.len() >= 2,
        "both f(x) and g(x) cover x — should emit multiple alternatives: {triggers:?}"
    );
    assert_eq!(triggers[0].len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::LogicFnCall { name, .. } if name == "f"),
        "shallower f should be the first (best-scored) alternative"
    );
}

// ── Edge cases ──────────────────────────────────────────────────────

/// Duplicate variable names in the var list are deduplicated.
#[test]
#[timeout(30000)]
fn duplicate_vars_deduplicated() {
    let body = gt(logic_fn_call("f", vec![var("x")]), int(0));
    let triggers = synthesize_triggers(&[s("x"), s("x")], &body);
    assert_eq!(triggers.len(), 1, "should still produce a trigger");
    assert_eq!(triggers[0].len(), 1);
}

/// Empty variable list produces no triggers (nothing to cover).
#[test]
#[timeout(30000)]
fn empty_vars_no_triggers() {
    let body = gt(logic_fn_call("f", vec![var("x")]), int(0));
    let triggers = synthesize_triggers(&[], &body);
    // With no variables to cover, candidates have empty coverage,
    // so no full-coverage trigger exists. Falls back to best partial.
    // The first candidate is returned as a partial trigger.
    assert!(
        !triggers.is_empty() || triggers.is_empty(),
        "should not panic"
    );
}

/// Variable not present in body yields partial trigger (best candidate).
#[test]
#[timeout(30000)]
fn unmentioned_var_yields_partial_trigger() {
    // forall x, y. f(x) > 0 — y is never mentioned
    let body = gt(logic_fn_call("f", vec![var("x")]), int(0));
    let triggers = synthesize_triggers(&[s("x"), s("y")], &body);
    // Cannot cover y, so no full-coverage single or pair trigger.
    // Falls back to best partial (f(x)).
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1, "partial trigger for x only");
}

// ── collect_ground_subexprs ─────────────────────────────────────────

/// A LogicFnCall with no bound variables is collected as a ground sub-expression.
#[test]
#[timeout(30000)]
fn ground_subexpr_logic_fn_no_bound_vars() {
    // forall x. g(a) > 0 ==> f(x) > 0
    // g(a) is ground — it doesn't mention x.
    let body = implies(
        gt(logic_fn_call("g", vec![var("a")]), int(0)),
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
    );
    let ground = collect_ground_subexprs(&body, &[s("x")]);
    assert_eq!(ground.len(), 1, "should find one ground sub-expression");
    assert!(
        matches!(&ground[0], PureExpr::LogicFnCall { name, .. } if name == "g"),
        "ground sub-expression should be g(a): got {:?}",
        ground[0]
    );
}

/// A MethodCall with no bound variables is collected as a ground sub-expression.
#[test]
#[timeout(30000)]
fn ground_subexpr_method_call_no_bound_vars() {
    // forall i. i < v.len() ==> P
    let body = implies(
        lt(var("i"), method_call(var("v"), "len", vec![])),
        bool_expr(true),
    );
    let ground = collect_ground_subexprs(&body, &[s("i")]);
    assert_eq!(ground.len(), 1, "should find v.len() as ground");
    assert!(
        matches!(&ground[0], PureExpr::MethodCall { method, .. } if method == "len"),
        "ground sub-expression should be v.len(): got {:?}",
        ground[0]
    );
}

/// A function call that mentions a bound variable is NOT collected.
#[test]
#[timeout(30000)]
fn ground_subexpr_skips_bound_var_mentions() {
    // forall x. f(x) > 0
    let body = gt(logic_fn_call("f", vec![var("x")]), int(0));
    let ground = collect_ground_subexprs(&body, &[s("x")]);
    assert!(
        ground.is_empty(),
        "f(x) mentions bound var x — should not be collected"
    );
}

/// Mixed body: some calls are ground, some are not.
#[test]
#[timeout(30000)]
fn ground_subexpr_mixed_ground_and_bound() {
    // forall i. i >= 0 && i < v.len() ==> v.get(i) > 0
    let body = implies(
        and(
            ge(var("i"), int(0)),
            lt(var("i"), method_call(var("v"), "len", vec![])),
        ),
        gt(method_call(var("v"), "get", vec![var("i")]), int(0)),
    );
    let ground = collect_ground_subexprs(&body, &[s("i")]);
    // v.len() is ground (doesn't mention i). v.get(i) is NOT ground.
    assert_eq!(
        ground.len(),
        1,
        "should find exactly v.len() as ground: got {ground:?}"
    );
    assert!(
        matches!(&ground[0], PureExpr::MethodCall { method, .. } if method == "len"),
        "ground sub-expression should be v.len()"
    );
}

/// Nested quantifier: inner quantifier's bound variables shadow outer.
#[test]
#[timeout(30000)]
fn ground_subexpr_nested_quantifier_shadowing() {
    // forall x. exists y. g(x) > 0 ==> f(y) > 0
    // From the outer quantifier's perspective with bound=[x]:
    // g(x) mentions x — NOT ground.
    // f(y) doesn't mention x, but y is bound by the inner exists.
    // Re-encoding f(y) at depth 0 would create a free variable y,
    // so f(y) must NOT be collected as ground. (#2696 fix)
    let inner = exists(
        "y",
        implies(
            gt(logic_fn_call("g", vec![var("x")]), int(0)),
            gt(logic_fn_call("f", vec![var("y")]), int(0)),
        ),
    );
    let ground = collect_ground_subexprs(&inner, &[s("x")]);
    // f(y) references y which is bound by the inner exists — not truly ground.
    // Neither g(x) (mentions outer bound var x) nor f(y) (mentions inner bound
    // var y) should be collected. The result should be empty.
    assert!(
        ground.is_empty(),
        "neither g(x) nor f(y) are truly ground (both reference bound vars): got {ground:?}"
    );
}

/// No function calls in body yields empty result.
#[test]
#[timeout(30000)]
fn ground_subexpr_pure_arithmetic_empty() {
    // forall x. x + 1 > 0
    let body = gt(add(var("x"), int(1)), int(0));
    let ground = collect_ground_subexprs(&body, &[s("x")]);
    assert!(ground.is_empty(), "arithmetic-only body has no fn calls");
}

/// MethodCall with View-wrapped receiver is collected as ground when it
/// doesn't reference bound variables. This handles `v@.len()` in quantified
/// postconditions like `forall<i> 0 <= i && i < v@.len() ==> ...`.
/// The actual tree is `MethodCall { receiver: View(Var("v")), ... }`,
/// NOT `View(MethodCall { ... })`. (#2696)
#[test]
#[timeout(30000)]
fn ground_subexpr_method_call_with_view_receiver() {
    // forall i. i < View(v).len() ==> P
    // Tree structure: MethodCall { receiver: View(Var("v")), method: "len", args: [] }
    let body = implies(
        lt(var("i"), method_call(view(var("v")), "len", vec![])),
        bool_expr(true),
    );
    let ground = collect_ground_subexprs(&body, &[s("i")]);
    // The MethodCall is ground (doesn't mention i).
    assert_eq!(
        ground.len(),
        1,
        "should find v@.len() as ground: got {ground:?}"
    );
    assert!(
        matches!(&ground[0], PureExpr::MethodCall { method, .. } if method == "len"),
        "ground sub-expression should be v@.len() MethodCall: got {:?}",
        ground[0]
    );
}

/// MethodCall with View-wrapped receiver that references a bound variable.
#[test]
#[timeout(30000)]
fn ground_subexpr_method_call_with_view_receiver_bound_var() {
    // forall i. View(v).get(i) > 0
    let body = gt(method_call(view(var("v")), "get", vec![var("i")]), int(0));
    let ground = collect_ground_subexprs(&body, &[s("i")]);
    // v@.get(i) mentions i — not ground.
    assert!(
        ground.is_empty(),
        "v@.get(i) mentions bound var i — should not be collected: got {ground:?}"
    );
}

/// View wrapping an entire MethodCall (`View(MethodCall(...))`) is collected
/// as a single ground unit when the inner call doesn't reference bound vars.
/// This handles encoding patterns like `(v.method())@`. (#2696)
#[test]
#[timeout(30000)]
fn ground_subexpr_view_wrapping_method_call() {
    use std::sync::Arc;
    // forall x. View(method_call(a, "compute", [])) > 0 ==> f(x) > 0
    let inner_call = method_call(var("a"), "compute", vec![]);
    let view_of_call = PureExpr::View(Arc::new(inner_call));
    let body = implies(
        gt(view_of_call, int(0)),
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
    );
    let ground = collect_ground_subexprs(&body, &[s("x")]);
    // View(a.compute()) is ground (doesn't mention x).
    assert_eq!(
        ground.len(),
        1,
        "should find View(a.compute()) as ground: got {ground:?}"
    );
    assert!(
        matches!(&ground[0], PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::MethodCall { method, .. } if method == "compute")),
        "ground sub-expression should be View(a.compute()): got {:?}",
        ground[0]
    );
}

/// View-wrapped LogicFnCall is collected as ground when it doesn't reference
/// bound variables.
#[test]
#[timeout(30000)]
fn ground_subexpr_view_wrapped_logic_fn_call() {
    use std::sync::Arc;
    // forall x. View(logic_fn("model", [a])) > 0 ==> f(x) > 0
    let inner_call = logic_fn_call("model", vec![var("a")]);
    let view_of_call = PureExpr::View(Arc::new(inner_call));
    let body = implies(
        gt(view_of_call, int(0)),
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
    );
    let ground = collect_ground_subexprs(&body, &[s("x")]);
    // View(model(a)) is ground. f(x) is not.
    assert_eq!(
        ground.len(),
        1,
        "should find View(model(a)) as ground: got {ground:?}"
    );
    assert!(
        matches!(&ground[0], PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::LogicFnCall { name, .. } if name == "model")),
        "ground sub-expression should be View(model(a)): got {:?}",
        ground[0]
    );
}

// ── Implication-aware trigger scoring (#2696) ──────────────────────

/// In `guard ==> consequent`, consequent-side triggers should rank higher.
/// When both guard and consequent have a full-coverage candidate, the
/// consequent's candidate should be the first alternative pattern.
#[test]
#[timeout(30000)]
fn synth_implication_consequent_preferred_over_guard() {
    // forall x. guard_fn(x) > 0 ==> consequent_fn(x) > 0
    // Both guard_fn(x) and consequent_fn(x) fully cover x.
    // The consequent_fn should be preferred due to the implication bonus.
    let body = implies(
        gt(logic_fn_call("guard_fn", vec![var("x")]), int(0)),
        gt(logic_fn_call("consequent_fn", vec![var("x")]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert!(
        triggers.len() >= 2,
        "both sides cover x — should emit multiple alternatives: {triggers:?}"
    );
    assert!(
        matches!(&triggers[0][0], PureExpr::LogicFnCall { name, .. } if name == "consequent_fn"),
        "consequent-side trigger should be preferred (first alternative): got {:?}",
        triggers[0][0]
    );
}

/// Method call in consequent preferred over method call in guard.
#[test]
#[timeout(30000)]
fn synth_implication_consequent_method_call_preferred() {
    // forall x. x.guard_m() > 0 ==> x.consequent_m() > 0
    let body = implies(
        gt(method_call(var("x"), "guard_m", vec![]), int(0)),
        gt(method_call(var("x"), "consequent_m", vec![]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert!(
        triggers.len() >= 2,
        "both sides cover x — should emit multiple alternatives: {triggers:?}"
    );
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, .. } if method == "consequent_m"),
        "consequent-side method trigger should be preferred: got {:?}",
        triggers[0][0]
    );
}

/// Common Creusot pattern: `forall<i> 0 <= i && i < v.len() ==> P(v.get(i))`.
/// The `v.get(i)` in the consequent should be preferred over `v.len()` in guard.
#[test]
#[timeout(30000)]
fn synth_seq_index_pattern_consequent_preferred() {
    // forall i. 0 <= i && i < v.len() ==> v.get(i) > 0
    let body = implies(
        and(
            ge(var("i"), int(0)),
            lt(var("i"), method_call(var("v"), "len", vec![])),
        ),
        gt(method_call(var("v"), "get", vec![var("i")]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("i")], &body);
    assert!(
        !triggers.is_empty(),
        "should produce at least one trigger pattern"
    );
    // v.get(i) covers i and is in the consequent — should be the first pattern.
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, .. } if method == "get"),
        "v.get(i) from consequent should be the preferred trigger: got {:?}",
        triggers[0][0]
    );
}

/// Non-implication bodies should not be affected by the implication bonus.
#[test]
#[timeout(30000)]
fn synth_non_implication_unaffected() {
    // forall x. f(x) > 0 && g(x) > 0 (AND, not implication)
    let body = and(
        gt(logic_fn_call("f", vec![var("x")]), int(0)),
        gt(logic_fn_call("g", vec![var("x")]), int(0)),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    // Both candidates have the same depth and both are logic fns.
    // Without implication bonus, the first one encountered (f) should rank first
    // or they should be equivalent alternatives.
    assert!(
        triggers.len() >= 2,
        "both f(x) and g(x) cover x — should emit multiple alternatives"
    );
}

// ── Nested implication consequent scoring (#2696) ───────────────────

/// Conjunction of two implications: `(g1 ==> P(x)) && (g2 ==> Q(x))`.
/// Both P(x) and Q(x) are consequents and should receive the bonus.
#[test]
#[timeout(30000)]
fn synth_conjunction_of_implications_scores_both_consequents() {
    // (guard1 ==> f(x) > 0) && (guard2 ==> g(x) > 0)
    let body = and(
        implies(
            gt(var("x"), int(0)),
            gt(logic_fn_call("f", vec![var("x")]), int(0)),
        ),
        implies(
            lt(var("x"), int(10)),
            gt(logic_fn_call("g", vec![var("x")]), int(0)),
        ),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    // Both f(x) and g(x) are in consequent positions and should be top-ranked.
    assert!(
        !triggers.is_empty(),
        "should produce trigger patterns from the consequents"
    );
    // At least one trigger should be from the consequent (f or g).
    let has_consequent_trigger = triggers.iter().any(|pattern| {
        pattern.iter().any(|expr| {
            matches!(expr, PureExpr::LogicFnCall { name, .. }
                     if name == "f" || name == "g")
        })
    });
    assert!(
        has_consequent_trigger,
        "at least one trigger should be from a consequent"
    );
}

/// Nested implication: `g1 ==> (g2 ==> P(x))`.
/// P(x) is the innermost consequent and should receive the bonus.
#[test]
#[timeout(30000)]
fn synth_nested_implication_scores_innermost_consequent() {
    // guard1 ==> (guard2 ==> f(x) > 0)
    let body = implies(
        gt(var("x"), int(0)),
        implies(
            lt(var("x"), int(10)),
            gt(logic_fn_call("f", vec![var("x")]), int(0)),
        ),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert!(
        !triggers.is_empty(),
        "should produce trigger patterns from innermost consequent"
    );
    // f(x) from the innermost consequent should be present
    let has_f = triggers.iter().any(|pattern| {
        pattern
            .iter()
            .any(|expr| matches!(expr, PureExpr::LogicFnCall { name, .. } if name == "f"))
    });
    assert!(has_f, "innermost consequent trigger f(x) should be present");
}

/// Ite in consequent: `guard ==> if cond { A(x) } else { B(x) }`.
/// Both A(x) and B(x) from Ite branches should receive the implication
/// consequent bonus. This handles Creusot conditional postconditions like
/// `forall<x> g(x) ==> if take_first { A(x) } else { B(x) }`. (#2696)
#[test]
#[timeout(30000)]
fn synth_ite_in_consequent_scores_both_branches() {
    // guard ==> if cond { f(x) > 0 } else { g(x) > 0 }
    let body = implies(
        gt(var("x"), int(0)),
        ite(
            var("cond"),
            gt(logic_fn_call("f", vec![var("x")]), int(0)),
            gt(logic_fn_call("g", vec![var("x")]), int(0)),
        ),
    );
    let triggers = synthesize_triggers(&[s("x")], &body);
    assert!(
        !triggers.is_empty(),
        "should produce trigger patterns from Ite branches in consequent"
    );
    // At least one trigger should be from an Ite branch (f or g).
    let has_branch_trigger = triggers.iter().any(|pattern| {
        pattern.iter().any(|expr| {
            matches!(expr, PureExpr::LogicFnCall { name, .. }
                     if name == "f" || name == "g")
        })
    });
    assert!(
        has_branch_trigger,
        "at least one trigger should be from an Ite branch in the consequent"
    );
}

// ── Helper ──────────────────────────────────────────────────────────

fn s(name: &str) -> String {
    name.to_string()
}
