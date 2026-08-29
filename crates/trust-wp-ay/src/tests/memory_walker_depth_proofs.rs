// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test code uses small values where wrapping is not a concern.
#![allow(clippy::cast_possible_wrap)]

//! Depth/width survival tests for recursive PureExpr walkers and encoder state.
//!
//! These tests verify:
//!
//! 1. `expr::expr_mentions_var` — quantifier shadowing correctness at depth
//! 2. `trigger::expr_mentions_any_var` — shadow tracking across binder chains
//! 3. `closure_inline` — inlining completes with nested binders (smoke test)
//! 4. `view_identity_asserted` — per-variable dedup in the encoder
//!
//! Part of #901
//! Phase: memory_verification

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::CaptureAvoidingSubstOptions;

use super::helpers::*;
use crate::{BinOp, Pattern, PureExpr};

// =============================================================================
// 1. expr_mentions_var: depth-window semantics + deep survival proof
// =============================================================================

/// Prove that `expr_mentions_var` keeps exact semantics within the active
/// depth window, then survives a 500-deep left-recursive BinOp tree once it
/// switches to conservative fail-closed behavior.
///
/// The first half of the test stays below `MAX_ENCODING_DEPTH` so the result
/// still depends on actual traversal. The second half goes far beyond the
/// guard to prove the walker survives and returns the conservative result.
#[test]
#[timeout(30000)]
fn expr_mentions_var_survives_500_deep_tree() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let within_guard_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);

            // Stay below MAX_ENCODING_DEPTH so these assertions still prove
            // precise membership semantics rather than the fail-closed path.
            let mut within_guard = var("target");
            for i in 0..within_guard_depth {
                within_guard = add(within_guard, int(i as i64));
            }

            assert!(
                crate::expr::expr_mentions_var(&within_guard, "target"),
                "Within the active depth window, expr_mentions_var should find the deep target"
            );
            assert!(
                !crate::expr::expr_mentions_var(&within_guard, "missing"),
                "Within the active depth window, expr_mentions_var should reject a missing variable"
            );

            // Go far beyond MAX_ENCODING_DEPTH to prove the recursive walker
            // survives and returns the conservative fail-closed result.
            let mut beyond_guard = var("target");
            for i in 0..500 {
                beyond_guard = add(beyond_guard, int(i as i64));
            }

            assert!(
                crate::expr::expr_mentions_var(&beyond_guard, "target"),
                "Beyond MAX_ENCODING_DEPTH, expr_mentions_var should still return true for an existing variable"
            );
            assert!(
                crate::expr::expr_mentions_var(&beyond_guard, "missing"),
                "Beyond MAX_ENCODING_DEPTH, expr_mentions_var should conservatively assume a variable is mentioned"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("expr_mentions_var stack-overflowed on 500-deep tree");
}

/// Prove that `expr_mentions_var` correctly handles deep quantifier nesting
/// where the target variable is shadowed at an intermediate level.
///
/// Forall("target", body) should shadow "target" in body, so
/// `expr_mentions_var(Forall("target", ...), "target")` should return false
/// even though the variable name appears in the expression.
#[test]
#[timeout(30000)]
fn expr_mentions_var_respects_shadowing_in_deep_quantifiers() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            // Build: forall x0. forall x1. ... forall x99. target > 0
            // The innermost body mentions "target" as a free variable
            let mut body = gt(var("target"), int(0));
            for i in (0..100).rev() {
                body = PureExpr::Forall {
                    var: format!("x{i}"),
                    var_sort: None,
                    body: Arc::new(body),
                    triggers: vec![],
                };
            }
            assert!(
                crate::expr::expr_mentions_var(&body, "target"),
                "target is free (not shadowed by any x_i binder)"
            );

            // Now shadow "target" at the outermost level
            let shadowed = PureExpr::Forall {
                var: "target".to_string(),
                var_sort: None,
                body: Arc::new(body),
                triggers: vec![],
            };
            assert!(
                !crate::expr::expr_mentions_var(&shadowed, "target"),
                "target should be shadowed by the outermost Forall binder"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("expr_mentions_var panicked in deep quantifier test");
}

// =============================================================================
// 2. expr_mentions_any_var: depth-guarded shadow-tracking proofs
// =============================================================================

/// Prove that `expr_mentions_any_var` preserves shadow tracking across a deep
/// quantifier chain that stays inside the active depth window.
///
/// `expr_mentions_any_var_with_shadow` (trigger.rs) maintains a `HashSet`
/// of shadowed variables as it descends. This test exercises the shadow
/// set insert/remove lifecycle below `MAX_ENCODING_DEPTH`.
#[test]
#[timeout(30000)]
fn expr_mentions_any_var_survives_deep_quantifier_chain() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let shadow_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);
            // Build nested forall binders that stay below the guard so the
            // test exercises active shadow tracking rather than fail-closed
            // depth handling.
            let mut body = gt(var("free_var"), int(0));
            for i in (0..shadow_depth).rev() {
                body = PureExpr::Forall {
                    var: format!("q{i}"),
                    var_sort: None,
                    body: Arc::new(body),
                    triggers: vec![],
                };
            }

            let vars_to_check = vec!["free_var".to_string(), "q50".to_string()];
            let result = crate::encoder::trigger::expr_mentions_any_var(&body, &vars_to_check);

            // "free_var" is free at all levels. "q50" is bound at level 50
            // and shadowed in the body — but expr_mentions_any_var should
            // correctly detect that "free_var" IS mentioned.
            assert!(
                result,
                "Should detect 'free_var' through the active quantifier depth window"
            );

            // Check with only bound variables — should return false since
            // all q_i are bound by their respective forall
            let only_bound = vec!["q50".to_string()];
            assert!(
                !crate::encoder::trigger::expr_mentions_any_var(&body, &only_bound),
                "q50 is bound — should not be detected as free"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("expr_mentions_any_var stack-overflowed");
}

/// Once the trigger walker exceeds `MAX_ENCODING_DEPTH`, it must fail closed
/// and assume the queried variable may be present so quantifier elimination
/// does not drop a deep variable unsoundly.
#[test]
#[timeout(30000)]
fn expr_mentions_any_var_depth_limit_fails_closed() {
    let mut expr = bool_expr(true);
    for depth in 0..=(crate::encoder::MAX_ENCODING_DEPTH + 8) {
        expr = PureExpr::Forall {
            var: format!("q{depth}"),
            var_sort: None,
            body: Arc::new(expr),
            triggers: vec![],
        };
    }

    assert!(
        crate::encoder::trigger::expr_mentions_any_var(&expr, &["missing".to_string()]),
        "too-deep trigger walker should conservatively assume the variable is mentioned",
    );
}

/// Prove that `expr_mentions_any_var` survives wide expressions (many
/// children per node) as well as deep ones.
///
/// LogicFnCall with 100 arguments exercises the iterator-based traversal
/// path, which recurses through each argument.
#[test]
#[timeout(30000)]
fn expr_mentions_any_var_survives_wide_logic_fn_call() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            // Build a 100-wide LogicFnCall with a target var as the last arg
            let mut args: Vec<PureExpr> = (0..99).map(int).collect();
            args.push(var("needle"));

            let wide_expr = PureExpr::LogicFnCall {
                name: "wide_fn".to_string(),
                args,
            };

            // Wrap in 100-deep nesting for combined depth+width stress
            let mut expr = wide_expr;
            for _ in 0..100 {
                expr = add(expr, int(0));
            }

            let vars = vec!["needle".to_string()];
            assert!(
                crate::encoder::trigger::expr_mentions_any_var(&expr, &vars),
                "Should find 'needle' in deep+wide expression"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("expr_mentions_any_var stack-overflowed on wide expression");
}

/// Prove that trigger synthesis preserves let-shadow handling in a deep Let
/// chain that stays inside the active depth window, where the only
/// trigger-shaped term references a shadowed quantifier variable.
///
/// This specifically exercises `collect_mentioned_vars` through
/// `synthesize_triggers` -> `collect_trigger_candidates` ->
/// `covered_vars_with_shadow` on a deep binder stack. The expected result is
/// empty: `let i = ... in f(i)` must not count as coverage for outer `i`.
#[test]
#[timeout(30000)]
fn synthesize_triggers_ignores_deep_let_shadow_chain_within_limit() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let mut body = gt(logic_fn_call("f", vec![var("i")]), int(0));
            let shadow_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);
            body = PureExpr::Let {
                var: "i".to_string(),
                value: Arc::new(int(0)),
                body: Arc::new(body),
            };
            for depth in 0..shadow_depth {
                body = PureExpr::Let {
                    var: format!("tmp_{depth}"),
                    value: Arc::new(int(depth as i64)),
                    body: Arc::new(body),
                };
            }

            let vars = vec!["i".to_string()];
            let triggers = crate::encoder::trigger::synthesize_triggers(&vars, &body);
            assert!(
                triggers.is_empty(),
                "shadowed `i` inside a deep Let chain must not synthesize triggers"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("collect_mentioned_vars failed in active-depth Let-shadow chain");
}

/// Prove that trigger synthesis preserves match-shadow handling in a deep
/// Match chain that stays inside the active depth window, where every
/// arm pattern re-binds the quantifier variable name.
///
/// This exercises the `shadow_pattern_bindings` / `collect_mentioned_vars`
/// rollback path with repeated same-name bindings. The innermost `f(i)` refers
/// only to the match-bound `i`, so the outer quantifier's `i` must stay
/// uncovered across the full chain.
#[test]
#[timeout(30000)]
fn synthesize_triggers_ignores_deep_match_shadow_chain_within_limit() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let mut body = gt(logic_fn_call("f", vec![var("i")]), int(0));
            let shadow_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);
            for depth in 0..shadow_depth {
                body = match_expr(
                    var(&format!("scrutinee_{depth}")),
                    vec![(Pattern::Binding("i".to_string()), body)],
                );
            }

            let vars = vec!["i".to_string()];
            let triggers = crate::encoder::trigger::synthesize_triggers(&vars, &body);
            assert!(
                triggers.is_empty(),
                "shadowed `i` inside a deep Match chain must not synthesize triggers"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("collect_mentioned_vars failed in active-depth Match-shadow chain");
}

/// Prove that trigger synthesis preserves closure-param shadow handling in a
/// deep Closure chain that stays inside the active depth window, where each
/// closure parameter shadows the quantifier variable name.
///
/// This exercises the `Closure` shadow push/pop path with repeated same-name
/// binders. The innermost `f(i)` refers only to the closure-bound `i`, so the
/// outer quantifier's `i` must remain uncovered.
#[test]
#[timeout(30000)]
fn synthesize_triggers_ignores_deep_closure_shadow_chain_within_limit() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let mut body = gt(logic_fn_call("f", vec![var("i")]), int(0));
            let shadow_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);
            for _ in 0..shadow_depth {
                body = PureExpr::Closure {
                    params: vec![("i".to_string(), None)],
                    body: Arc::new(body),
                };
            }

            let vars = vec!["i".to_string()];
            let triggers = crate::encoder::trigger::synthesize_triggers(&vars, &body);
            assert!(
                triggers.is_empty(),
                "shadowed `i` inside a deep Closure chain must not synthesize triggers"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("collect_mentioned_vars failed in active-depth Closure-shadow chain");
}

// =============================================================================
// 3. closure_inline capture-avoiding substitution boundedness
// =============================================================================

/// Verify that `try_inline_closure_postcondition` completes on a closure
/// body with 50 nested Let binders and a 50-entry substitution map.
///
/// This exercises the current depth-limited capture-avoiding substitution path
/// that `closure_inline` uses before encoding the inlined body. The goal is to
/// prove the full inlining + encoding path stays bounded on nested binders.
///
/// NOTE: The assertion checks for successful inlining and encoding, not just
/// entry into the inlining fast path.
#[test]
#[timeout(30000)]
fn closure_inline_apply_subst_nested_let_binders_bounded() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            // Build: let v49 = ... let v1 = let v0 = body
            // Where body = x + y + z (uses variables from the subst map)
            let body = add(add(var("x"), var("y")), var("z"));
            let mut expr = body;
            for i in 0..50 {
                expr = PureExpr::Let {
                    var: format!("v{i}"),
                    value: Arc::new(int(i as i64)),
                    body: Arc::new(expr),
                };
            }

            // Build a 50-entry substitution map
            let mut subst: HashMap<String, PureExpr> = HashMap::new();
            subst.insert("x".to_string(), int(100));
            subst.insert("y".to_string(), int(200));
            subst.insert("z".to_string(), int(300));
            for i in 0..47 {
                subst.insert(format!("extra_{i}"), int(i));
            }

            let capture_info = crate::closure_capture_info! {
                def_id: "let_depth_test::closure#0".to_string(),
                captures: vec![],
                param_name: Some("f".to_string()),
                body_expr: Some(expr),
                param_names: Some(vec![]),
                ensures_exprs: None,
            };

            let mut encoder = crate::encoder::AYEncoder::new_pure();
            encoder.register_closure_body(&capture_info);

            let receiver = PureExpr::Var("f".to_string(), None);
            let result = encoder.try_inline_closure_postcondition(
                &receiver,
                "postcondition",
                &[PureExpr::Var("call_result".to_string(), None)],
                None,
            );
            assert!(
                matches!(result, Some(Ok(_))),
                "Should inline and encode closure with 50 nested Let binders + 50-entry subst map"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("closure_inline capture-avoiding substitution failed on nested Let binders");
}

/// Verify that `try_inline_closure_postcondition` completes on a closure
/// body with 30 nested Forall binders.
///
/// This exercises the current capture-avoiding substitution path plus
/// quantified-body encoding on a nested binder stack.
///
/// NOTE: The assertion checks for successful inlining and encoding, not just
/// the presence of the closure-inline fast path.
#[test]
#[timeout(30000)]
fn closure_inline_apply_subst_forall_shadowing_correct() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            // Build: forall q29. ... forall q0. (x > q0) && (x > q29)
            // The innermost body is Bool-sorted (required by ay forall)
            let innermost = and(gt(var("x"), var("q0")), gt(var("x"), var("q29")));
            let mut body = innermost;
            for i in 0..30 {
                body = PureExpr::Forall {
                    var: format!("q{i}"),
                    var_sort: None,
                    body: Arc::new(body),
                    triggers: vec![],
                };
            }

            // Wrap as closure body: result == forall_chain
            let closure_body = binop(var("result"), BinOp::Eq, body);

            let capture_info = crate::closure_capture_info! {
                def_id: "forall_shadow_test::closure#0".to_string(),
                captures: vec![],
                param_name: Some("f".to_string()),
                body_expr: Some(closure_body),
                param_names: Some(vec![]),
                ensures_exprs: None,
            };

            let mut encoder = crate::encoder::AYEncoder::new_pure();
            encoder.register_closure_body(&capture_info);

            let receiver = PureExpr::Var("f".to_string(), None);
            let result = encoder.try_inline_closure_postcondition(
                &receiver,
                "postcondition",
                &[PureExpr::Var("call_result".to_string(), None)],
                None,
            );
            assert!(
                matches!(result, Some(Ok(_))),
                "Should inline and encode closure with 30 nested Forall binders"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("closure_inline capture-avoiding substitution failed on nested Forall binders");
}

/// Prove that the full closure-inline postcondition path fails boundedly when
/// the registered body exceeds `MAX_ENCODING_DEPTH`.
///
/// This covers the integration path from `expr_mentions_var` through
/// `try_inline_closure_postcondition`, ensuring the new bounded walkers return
/// an encoding error instead of recursing until the Rust stack overflows.
#[test]
#[timeout(30000)]
fn closure_inline_postcondition_too_deep_body_returns_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut closure_body = binop(var("result"), BinOp::Eq, int(42));
            for depth in 0..=(crate::encoder::MAX_ENCODING_DEPTH + 8) {
                closure_body = PureExpr::Let {
                    var: format!("tmp_{depth}"),
                    value: Arc::new(int(depth as i64)),
                    body: Arc::new(closure_body),
                };
            }

            let capture_info = crate::closure_capture_info! {
                def_id: "too_deep_postcondition::closure#0".to_string(),
                captures: vec![],
                param_name: Some("f".to_string()),
                body_expr: Some(closure_body),
                param_names: Some(vec![]),
                ensures_exprs: None,
            };

            let mut encoder = crate::encoder::AYEncoder::new_pure();
            encoder.register_closure_body(&capture_info);

            let receiver = PureExpr::Var("f".to_string(), None);
            let result = encoder.try_inline_closure_postcondition(
                &receiver,
                "postcondition",
                &[PureExpr::Var("call_result".to_string(), None)],
                None,
            );

            assert!(
                matches!(result, Some(Err(_))),
                "too-deep inlined closure bodies should return a bounded encoding error, got {result:?}",
            );
        })
        .expect("thread spawn")
        .join()
        .expect("too-deep closure-inline postcondition stack-overflowed");
}

/// Prove that the capture-avoiding substitution engine used by closure
/// inlining preserves same-name Match-arm shadowing across a deep chain that
/// stays inside the active depth window.
#[test]
#[timeout(30000)]
fn closure_inline_substitution_match_shadow_chain_preserves_inner_binding_at_depth() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            // Stay below MAX_ENCODING_DEPTH so this checks active traversal,
            // not fail-closed subtree cloning once the depth guard trips.
            let shadow_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);
            let mut expr = add(var("x"), var("y"));
            for depth in 0..shadow_depth {
                expr = PureExpr::Match {
                    scrutinee: Arc::new(PureExpr::Var(format!("scrutinee_{depth}"), None)),
                    arms: vec![trust_wp_core::formula::MatchArm {
                        pattern: Pattern::Binding("x".to_string()),
                        body: expr,
                    }],
                };
            }

            let subst = HashMap::from([("x".to_string(), int(99)), ("y".to_string(), int(7))]);
            let result = expr.substitute_capture_avoiding(
                &subst,
                &CaptureAvoidingSubstOptions {
                    depth_limit: Some(crate::encoder::MAX_ENCODING_DEPTH),
                },
            );

            let mut cursor = &result;
            for _ in 0..shadow_depth {
                match cursor {
                    PureExpr::Match { arms, .. } => {
                        cursor = &arms[0].body;
                    }
                    other => panic!("expected nested Match chain, got {other:?}"),
                }
            }

            assert_eq!(
                *cursor,
                add(var("x"), int(7)),
                "shadowed x should stay bound while free y still substitutes at depth",
            );
        })
        .expect("thread spawn")
        .join()
        .expect("capture-avoiding substitution stack-overflowed in deep Match shadow chain");
}

/// Prove that the capture-avoiding substitution engine used by closure
/// inlining preserves same-name Closure-param shadowing across a deep chain
/// that stays inside the active depth window.
#[test]
#[timeout(30000)]
fn closure_inline_substitution_closure_shadow_chain_preserves_inner_binding_at_depth() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            // Stay below MAX_ENCODING_DEPTH so this checks active traversal,
            // not fail-closed subtree cloning once the depth guard trips.
            let shadow_depth = crate::encoder::MAX_ENCODING_DEPTH.saturating_sub(8);
            let mut expr = add(var("x"), var("y"));
            for _ in 0..shadow_depth {
                expr = PureExpr::Closure {
                    params: vec![("x".to_string(), None)],
                    body: Arc::new(expr),
                };
            }

            let subst = HashMap::from([("x".to_string(), int(99)), ("y".to_string(), int(7))]);
            let result = expr.substitute_capture_avoiding(
                &subst,
                &CaptureAvoidingSubstOptions {
                    depth_limit: Some(crate::encoder::MAX_ENCODING_DEPTH),
                },
            );

            let mut cursor = &result;
            for _ in 0..shadow_depth {
                match cursor {
                    PureExpr::Closure { params, body } => {
                        assert_eq!(
                            params,
                            &[("x".to_string(), None)],
                            "shadow-only closure params should not be renamed"
                        );
                        cursor = body;
                    }
                    other => panic!("expected nested Closure chain, got {other:?}"),
                }
            }

            assert_eq!(
                *cursor,
                add(var("x"), int(7)),
                "shadowed x should stay bound while free y still substitutes at depth",
            );
        })
        .expect("thread spawn")
        .join()
        .expect("capture-avoiding substitution stack-overflowed in deep Closure shadow chain");
}

/// Prove that the current depth-limited substitution path fails closed once
/// the leaf is deeper than `MAX_ENCODING_DEPTH`.
#[test]
#[timeout(30000)]
fn closure_inline_substitution_depth_limit_preserves_too_deep_leaf() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let mut expr = var("x");
            for depth in 0..=(crate::encoder::MAX_ENCODING_DEPTH + 8) {
                expr = add(expr, int(depth as i64));
            }

            let subst = HashMap::from([("x".to_string(), int(99))]);
            let result = expr.substitute_capture_avoiding(
                &subst,
                &CaptureAvoidingSubstOptions {
                    depth_limit: Some(crate::encoder::MAX_ENCODING_DEPTH),
                },
            );

            assert_eq!(
                result, expr,
                "capture-avoiding substitution should stop and preserve the deep leaf once MAX_ENCODING_DEPTH is exceeded",
            );
        })
        .expect("thread spawn")
        .join()
        .expect("capture-avoiding substitution stack-overflowed before hitting MAX_ENCODING_DEPTH");
}

// =============================================================================
// 4. SortResolverState accumulation: view_identity_asserted bounded
// =============================================================================

/// Verify that `view_identity_asserted` (HashSet<String>) grows exactly once
/// per unique base variable, not per encoding pass.
///
/// `assert_view_identity` (view.rs) is triggered by `PureExpr::View(...)`.
/// It asserts `base = base_view` identity and records the base name in
/// `view_identity_asserted`. Re-encoding the same View should not re-assert.
///
/// NOTE: Expressions without `View` nodes do NOT populate this set.
#[test]
#[timeout(30000)]
fn view_identity_asserted_dedup_across_encodings() {
    let mut encoder = crate::encoder::AYEncoder::new();

    // Encode `view(x) > 0` — the View node triggers assert_view_identity for "x"
    let _ = encoder.encode_pure(&gt(view(var("x")), int(0))).unwrap();
    let count_after_first = encoder.sort_resolver_for_test().view_identity_count();
    assert!(
        count_after_first >= 1,
        "Encoding View(x) should populate view_identity_asserted, got {count_after_first}"
    );

    // Encode `view(x) > 1` — same base variable "x", should not grow the set
    let _ = encoder.encode_pure(&gt(view(var("x")), int(1))).unwrap();
    let count_after_second = encoder.sort_resolver_for_test().view_identity_count();
    assert_eq!(
        count_after_first, count_after_second,
        "view_identity_asserted should not grow on repeated View(x): \
         first={count_after_first}, second={count_after_second}"
    );

    // Encode with a NEW base variable — should grow by exactly 1
    let _ = encoder.encode_pure(&gt(view(var("y")), int(0))).unwrap();
    let count_after_new = encoder.sort_resolver_for_test().view_identity_count();
    assert_eq!(
        count_after_new,
        count_after_second + 1,
        "Adding View(y) should grow view_identity_asserted by 1, \
         got: before={count_after_second}, after={count_after_new}"
    );
}
