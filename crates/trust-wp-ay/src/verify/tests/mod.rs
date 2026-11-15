// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::{expr_requires_result_bool, result_match_datatype_from_postcondition};
use crate::{
    encoder::{match_enc::MatchDatatypeKind, AYEncoder},
    tests::helpers::{
        add, and, binop, bool_expr, deref, eq, exists, forall, gt, int, ite, let_bind,
        logic_fn_call, match_expr, method_call, not, old, var, view,
    },
    BinOp, Pattern, PureExpr,
};

mod existential_negation;
mod expr_transforms;
mod ground_collectors;
mod hard_timeout_and_retry;
mod loop_verification_result;
mod mode_overrides;
mod negated_postcondition_encoding;
mod provenance;
mod refutation_authority;
mod result_inference;
mod structural_induction_m0;
mod unknown_reason;
mod unsoundness_demotion;

fn resolve_verified(_: &mut AYEncoder) -> super::VerificationResult {
    super::VerificationResult::Verified(None)
}

fn resolve_verified_with_worker_thread_unsoundness(_: &mut AYEncoder) -> super::VerificationResult {
    crate::encoder::unsoundness::increment(
        crate::encoder::unsoundness::UnsoundnessCategory::SortFallbackToInt,
    );
    super::VerificationResult::Verified(None)
}

// --- assert_standard_axioms error propagation (#1631) ---

/// `assert_standard_axioms` returns `Ok(())` on a clean encoder with no
/// requires (the common loop verification path). This test ensures the
/// function signature returns `Result` — if it silently swallowed errors,
/// this test would fail to compile.
#[test]
#[timeout(30000)]
fn assert_standard_axioms_succeeds_on_clean_encoder() {
    use super::assert_standard_axioms;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let result = assert_standard_axioms(&mut encoder, &[], &[]);
    assert!(
        result.is_ok(),
        "assert_standard_axioms should succeed on a clean encoder: {:?}",
        result.err()
    );
}

/// `assert_standard_axioms` returns `Ok(())` when requires contain
/// expressions without postcondition_once calls (no eager instantiation
/// needed). This is the common function verification path.
#[test]
#[timeout(30000)]
fn assert_standard_axioms_succeeds_with_simple_requires() {
    use super::assert_standard_axioms;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let requires = vec![gt(var("x"), int(0))];
    // Pre-encode to register vars
    let _ = encoder.encode_pure(&requires[0]);
    let result = assert_standard_axioms(&mut encoder, &requires, &[]);
    assert!(
        result.is_ok(),
        "assert_standard_axioms should succeed with simple requires: {:?}",
        result.err()
    );
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_finds_ground_and_existential_assumptions() {
    let first = method_call(
        var("f"),
        "postcondition_once",
        vec![var("a"), var("call_0")],
    );
    let second = exists(
        "f3",
        and(
            method_call(
                var("g"),
                "postcondition_mut",
                vec![var("b"), var("f3"), var("result")],
            ),
            logic_fn_call("resolve", vec![var("f3")]),
        ),
    );
    let body = PureExpr::LetAssume {
        assumption: Arc::new(first.clone()),
        body: Arc::new(PureExpr::Let {
            var: "tmp".to_string(),
            value: Arc::new(int(0)),
            body: Arc::new(PureExpr::LetAssume {
                assumption: Arc::new(second.clone()),
                body: Arc::new(var("call_1")),
            }),
        }),
    };

    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&first, &second]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_visits_both_ite_branches() {
    let first = method_call(
        var("f"),
        "postcondition_once",
        vec![var("a"), var("call_0")],
    );
    let second = exists(
        "f3",
        and(
            method_call(
                var("g"),
                "postcondition_mut",
                vec![var("b"), var("f3"), var("result")],
            ),
            logic_fn_call("resolve", vec![var("f3")]),
        ),
    );
    let body = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(int(0)),
        body: Arc::new(ite(
            bool_expr(true),
            PureExpr::LetAssume {
                assumption: Arc::new(first.clone()),
                body: Arc::new(var("call_0")),
            },
            PureExpr::LetAssume {
                assumption: Arc::new(second.clone()),
                body: Arc::new(var("call_1")),
            },
        )),
    };

    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&first, &second]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_traverses_match_arms() {
    let assumption = method_call(var("f"), "postcondition_once", vec![var("a")]);
    let body = match_expr(
        var("opt"),
        vec![(
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("x".to_string()))),
            },
            PureExpr::LetAssume {
                assumption: Arc::new(assumption.clone()),
                body: Arc::new(var("x")),
            },
        )],
    );
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&assumption]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_traverses_binop() {
    let assumption = bool_expr(true);
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::LetAssume {
            assumption: Arc::new(assumption.clone()),
            body: Arc::new(var("x")),
        }),
        BinOp::Add,
        Arc::new(int(1)),
    );
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&assumption]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_traverses_closure_body() {
    let assumption = method_call(var("f"), "postcondition_once", vec![var("a")]);
    let body = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::LetAssume {
            assumption: Arc::new(assumption.clone()),
            body: Arc::new(var("x")),
        }),
    };
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&assumption]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_skips_let_obligation() {
    // LetObligation should NOT be collected, only recursed into
    let obligation = bool_expr(true);
    let inner_assumption = method_call(var("f"), "postcondition_once", vec![var("a")]);
    let body = PureExpr::LetObligation {
        obligation: Arc::new(obligation),
        body: Arc::new(PureExpr::LetAssume {
            assumption: Arc::new(inner_assumption.clone()),
            body: Arc::new(var("result")),
        }),
    };
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    // Only the inner LetAssume assumption, not the LetObligation
    assert_eq!(collected, vec![&inner_assumption]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_traverses_quantifier_body() {
    let assumption = method_call(var("f"), "postcondition_once", vec![var("a")]);
    let body = forall(
        "x",
        PureExpr::LetAssume {
            assumption: Arc::new(assumption.clone()),
            body: Arc::new(var("x")),
        },
    );
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&assumption]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_traverses_unop_and_wrappers() {
    let assumption = bool_expr(true);
    let body = not(PureExpr::LetAssume {
        assumption: Arc::new(assumption.clone()),
        body: Arc::new(bool_expr(false)),
    });
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert_eq!(collected, vec![&assumption]);
}

#[test]
#[timeout(30000)]
fn collect_body_let_assume_assumptions_empty_on_no_let_assume() {
    let body = add(var("x"), int(1));
    let collected = super::solver_tail::collect_body_let_assume_assumptions(&body);
    assert!(collected.is_empty());
}

#[test]
#[timeout(30000)]
fn is_ay_panic_rejects_debug_prefix_false_positive() {
    assert!(!super::is_ay_panic("debug: enabled"));
    assert!(!super::is_ay_panic("Debug: tracing something"));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_bug_prefix() {
    assert!(super::is_ay_panic("BUG: mk_eq sort mismatch"));
    assert!(super::is_ay_panic("bug: internal error"));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_sort_mismatch_variant_name() {
    assert!(super::is_ay_panic(
        "SortMismatch { expected: Bool, got: Int }"
    ));
}

// --- is_ay_panic boundary tests ---

#[test]
#[timeout(30000)]
fn is_ay_panic_rejects_empty_string() {
    assert!(!super::is_ay_panic(""));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_rejects_unrelated_message() {
    assert!(!super::is_ay_panic("timeout after 60s"));
    assert!(!super::is_ay_panic("unknown sort"));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_rejects_fatal_prefix() {
    // "FATAL:" is not a recognized ay panic pattern
    assert!(!super::is_ay_panic("FATAL: internal inconsistency"));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_conflict_verification() {
    assert!(super::is_ay_panic("conflict verification failed"));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_farkas_verification() {
    assert!(super::is_ay_panic("farkas semantic verification failed"));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_expects_bool_got() {
    assert!(super::is_ay_panic("expects Bool, got Int"));
}

// --- is_ay_panic ay internal assertion panic tests (#2687) ---

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_val_at_prefetch_panic() {
    // ay-prefetch debug_assert! panic: val_at bounds check failure
    assert!(super::is_ay_panic(
        "val_at: index 62 out of bounds for vals of length 20"
    ));
}

#[test]
#[timeout(30000)]
fn is_ay_panic_accepts_tseitin_mapping_panic() {
    // ay-dpll .expect() panic: Tseitin variable mapping assertion
    assert!(super::is_ay_panic(
        "Tseitin should always map incremental refinement atoms"
    ));
    assert!(super::is_ay_panic("Tseitin should always map split atoms"));
}

// --- expr_requires_result_bool fallthrough tests ---
//
// The `_ => false` catchall covers MethodCall, LogicFnCall, Match, Let,
// Closure. Forall/Exists recurse into the body (#2624). Each catchall
// variant should return false even when it contains `result` — the
// function only detects Bool sort via direct `result` use, Not,
// BinOp(And/Or/Implies/Eq/Ne), Ite, or Forall/Exists body recursion.

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_method_call_returns_false() {
    let expr = method_call(var("result"), "len", vec![]);
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_logic_fn_call_returns_false() {
    let expr = logic_fn_call("Some", vec![var("result")]);
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_forall_int_body_returns_false() {
    // forall<x> x == result — `x` infers to Int, so result is NOT Bool
    let expr = forall("x", eq(var("x"), var("result")));
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_exists_int_body_returns_false() {
    // exists<x> x == result — `x` infers to Int, so result is NOT Bool
    let expr = exists("x", eq(var("x"), var("result")));
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_forall_bool_body_returns_true() {
    // forall<x> result == (x > 0) — (x > 0) is Bool, so result IS Bool (#2624)
    let expr = forall("x", eq(var("result"), gt(var("x"), int(0))));
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_exists_bool_body_returns_true() {
    // exists<x> result == (x > 0) — (x > 0) is Bool, so result IS Bool (#2624)
    let expr = exists("x", eq(var("result"), gt(var("x"), int(0))));
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_forall_implies_result_is_true() {
    // forall<x> (x > 0) ==> result — result used directly in implies body
    let expr = forall(
        "x",
        binop(gt(var("x"), int(0)), BinOp::Implies, var("result")),
    );
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_match_returns_false() {
    let expr = match_expr(var("result"), vec![(Pattern::Wildcard, bool_expr(true))]);
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_let_returns_false() {
    let expr = let_bind("x", var("result"), bool_expr(true));
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_closure_returns_false() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("result")),
    };
    assert!(!expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_bare_result_is_true() {
    assert!(expr_requires_result_bool(&var("result")));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_not_result_is_true() {
    let expr = not(var("result"));
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_result_eq_true_is_true() {
    let expr = eq(var("result"), bool_expr(true));
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_result_and_other_is_true() {
    // `result && x` — And recurses, finds bare `result`
    let expr = and(var("result"), var("x"));
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_ite_result_in_condition() {
    // `if result then 1 else 0` — result in condition = Bool
    let expr = ite(var("result"), int(1), int(0));
    assert!(expr_requires_result_bool(&expr));
}

#[test]
#[timeout(30000)]
fn expr_requires_result_bool_gt_result_is_false() {
    // `result > 0` — comparison operators return false (result is Int here)
    let expr = gt(var("result"), int(0));
    assert!(!expr_requires_result_bool(&expr));
}

/// Wrapper nodes preserve a bare `result` Bool signal for result inference.
#[test]
#[timeout(30000)]
fn expr_requires_result_bool_wrapper_preserves_bool_signal() {
    assert!(expr_requires_result_bool(&deref(var("result"))));
    assert!(expr_requires_result_bool(&view(var("result"))));
    assert!(expr_requires_result_bool(&old(var("result"))));
}

/// Result requires Bool when deeply nested inside Or/Implies connectors.
#[test]
#[timeout(30000)]
fn expr_requires_result_bool_nested_or_implies() {
    let deep = binop(var("result"), BinOp::Eq, bool_expr(true));
    assert!(expr_requires_result_bool(&binop(
        var("x"),
        BinOp::Or,
        deep.clone()
    )));
    assert!(expr_requires_result_bool(&binop(
        var("x"),
        BinOp::Implies,
        deep
    )));
}

// --- result_match_datatype_from_postcondition constructor equality tests ---

#[test]
#[timeout(30000)]
fn result_match_datatype_from_constructor_eq_some() {
    // `result == Some(v)` should infer OptionInt
    let ensures = vec![eq(var("result"), logic_fn_call("Some", vec![var("v")]))];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_datatype_ignores_nested_result_mentions() {
    let ensures = vec![eq(
        method_call(var("wrap"), "f", vec![var("result")]),
        logic_fn_call("Some", vec![var("v")]),
    )];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

#[test]
#[timeout(30000)]
fn result_match_datatype_from_constructor_eq_ok() {
    // `result == Ok(v)` should infer ResultIntInt
    let ensures = vec![eq(var("result"), logic_fn_call("Ok", vec![var("v")]))];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_datatype_from_constructor_eq_none_var() {
    // `result == None` (None as bare Var) should infer OptionInt
    let ensures = vec![eq(var("result"), var("None"))];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn result_match_datatype_from_constructor_conflict_returns_none() {
    // `result == Some(v) && result == Ok(w)` — conflicting datatypes → None
    let ensures = vec![
        eq(var("result"), logic_fn_call("Some", vec![var("v")])),
        eq(var("result"), logic_fn_call("Ok", vec![var("w")])),
    ];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

#[test]
#[timeout(30000)]
fn result_match_datatype_from_no_constructor_returns_none() {
    // `result > 0` — no constructor pattern
    let ensures = vec![gt(var("result"), int(0))];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

/// Unknown constructor name returns None.
#[test]
#[timeout(30000)]
fn result_match_datatype_from_constructor_unknown() {
    let ensures = vec![eq(
        var("result"),
        logic_fn_call("MyVariant", vec![var("v")]),
    )];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

// --- normalize_deref_final ---
// Coverage gap: zero direct tests for the Deref/Final normalization that
// bridges call-site MIR wrappers to ensures-body bare variables. (#1927)

#[test]
#[timeout(30000)]
fn normalize_deref_final_strips_deref_from_var() {
    use super::normalize_deref_final;

    // Deref(Var("x")) -> Var("x"): by-value dereference identity
    let expr = deref(var("x"));
    let result = normalize_deref_final(&expr);
    assert_eq!(result, var("x"), "Deref(Var) should normalize to bare Var");
}

#[test]
#[timeout(30000)]
fn normalize_deref_final_appends_final_suffix() {
    use super::normalize_deref_final;

    // Final(Var("f")) -> Var("f_final"): terminal state naming
    let expr = PureExpr::Final(Arc::new(var("f")));
    let result = normalize_deref_final(&expr);
    assert_eq!(
        result,
        var("f_final"),
        "Final(Var) should normalize to Var with _final suffix"
    );
}

#[test]
#[timeout(30000)]
fn normalize_deref_final_double_final_chains() {
    use super::normalize_deref_final;

    // Final(Final(Var("f"))) -> Var("f_final_final")
    let expr = PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(var("f")))));
    let result = normalize_deref_final(&expr);
    assert_eq!(
        result,
        var("f_final_final"),
        "nested Final should chain _final suffixes"
    );
}

#[test]
#[timeout(30000)]
fn normalize_deref_final_deref_then_final() {
    use super::normalize_deref_final;

    // Final(Deref(Var("x"))) -> Var("x_final")
    // MIR pattern: ^(*self) = ^self for by-value params
    let expr = PureExpr::Final(Arc::new(deref(var("x"))));
    let result = normalize_deref_final(&expr);
    assert_eq!(
        result,
        var("x_final"),
        "Final(Deref(Var)) should strip Deref then apply _final"
    );
}

#[test]
#[timeout(30000)]
fn normalize_deref_final_preserves_method_call_structure() {
    use super::normalize_deref_final;

    // postcondition_mut(Deref(Var("f")), [Final(Var("f"))])
    //   -> postcondition_mut(Var("f"), [Var("f_final")])
    let expr = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![PureExpr::Final(Arc::new(var("f")))],
    );
    let result = normalize_deref_final(&expr);
    let expected = method_call(var("f"), "postcondition_mut", vec![var("f_final")]);
    assert_eq!(
        result, expected,
        "normalization should recurse into MethodCall receiver and args"
    );
}

#[test]
#[timeout(30000)]
fn normalize_deref_final_leaves_pass_through() {
    use super::normalize_deref_final;

    assert_eq!(normalize_deref_final(&var("x")), var("x"));
    assert_eq!(normalize_deref_final(&int(42)), int(42));
    assert_eq!(normalize_deref_final(&bool_expr(true)), bool_expr(true));
}

// --- flatten_ghost_implications ---
// Coverage gap: re-exported for tests but never tested. Contains 4 phases
// of non-trivial logic including constant propagation. (#1927)

#[test]
#[timeout(30000)]
fn flatten_ghost_implications_phase1_bool_var_collected() {
    use super::flatten_ghost_implications;

    // Ghost context: [Var("b")]
    // Phase 1 collects "b" as true. Phase 3 with implication b => (x > 0)
    // should assert x > 0.
    let ghost_exprs = vec![
        var("b"),
        PureExpr::BinOp(
            Arc::new(var("b")),
            BinOp::Implies,
            Arc::new(gt(var("x"), int(0))),
        ),
    ];

    let mut encoder = AYEncoder::new();
    let result = flatten_ghost_implications(&mut encoder, &ghost_exprs);
    assert!(result.is_ok(), "should not error: {result:?}");
    // The encoder should have asserted gt(x, 0) from Phase 3.
    // We can't inspect the internal assertions directly, but the function
    // completing without error and the encoder being valid is the test.
}

#[test]
#[timeout(30000)]
fn flatten_ghost_implications_phase2_equality_propagation() {
    use super::flatten_ghost_implications;

    // Ghost context: [Var("a"), Eq(Var("b"), Var("a"))]
    // Phase 2: b == a where a is directly asserted, so b becomes true.
    // Phase 3: b => (y == 1) should assert y == 1.
    let ghost_exprs = vec![
        var("a"),
        eq(var("b"), var("a")),
        PureExpr::BinOp(
            Arc::new(var("b")),
            BinOp::Implies,
            Arc::new(eq(var("y"), int(1))),
        ),
    ];

    let mut encoder = AYEncoder::new();
    let result = flatten_ghost_implications(&mut encoder, &ghost_exprs);
    assert!(
        result.is_ok(),
        "equality propagation should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn flatten_ghost_implications_phase4_constant_propagation() {
    use super::flatten_ghost_implications;

    // Ghost context: [f(a) == 0, f(b) == f(a) + 1]
    // Phase 4: const_map { f(a) => 0 }, substitute in second eq to get f(b) == 0 + 1.
    let fa = logic_fn_call("f", vec![var("a")]);
    let fb = logic_fn_call("f", vec![var("b")]);
    let ghost_exprs = vec![eq(fa.clone(), int(0)), eq(fb.clone(), add(fa, int(1)))];

    let mut encoder = AYEncoder::new();
    let result = flatten_ghost_implications(&mut encoder, &ghost_exprs);
    assert!(
        result.is_ok(),
        "constant propagation should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn flatten_ghost_implications_empty_is_noop() {
    use super::flatten_ghost_implications;

    let ghost_exprs = vec![];
    let mut encoder = AYEncoder::new();
    let result = flatten_ghost_implications(&mut encoder, &ghost_exprs);
    assert!(result.is_ok(), "empty ghost exprs should be ok: {result:?}");
}

#[test]
#[timeout(30000)]
fn flatten_ghost_implications_no_implications_no_crash() {
    use super::flatten_ghost_implications;

    // Ghost context with equalities but no implications
    let ghost_exprs = vec![eq(var("x"), int(5)), eq(var("y"), int(10))];

    let mut encoder = AYEncoder::new();
    let result = flatten_ghost_implications(&mut encoder, &ghost_exprs);
    assert!(result.is_ok(), "no implications should be ok: {result:?}");
}
