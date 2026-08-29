// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for eager negated existential instantiation helpers (#1217).
//!
//! These tests enforce that eager instantiation reaches nested expression forms,
//! builds complete witness bindings, and performs bound-variable substitution
//! through all compound `PureExpr` variants.

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::{BinOp, Pattern, PureExpr};

use crate::{
    encoder::AYEncoder,
    tests::helpers::*,
    verify::{assert_eager_negated_existential_instantiations, normalize_deref_final},
};

/// Helper: build `exists<var> body` with no triggers.
fn mk_exists(var_name: &str, body: PureExpr) -> PureExpr {
    PureExpr::Exists {
        var: var_name.to_string(),
        var_sort: None,
        body: Arc::new(body),
        triggers: vec![],
    }
}

/// Helper: build a postcondition_mut method call pattern.
fn postcondition_mut(receiver: PureExpr, arg: PureExpr) -> PureExpr {
    method_call(receiver, "postcondition_mut", vec![arg])
}

/// Helper: build a requires clause with a postcondition_mut ground call.
fn ground_postcondition_mut(receiver: &str, arg: &str) -> PureExpr {
    postcondition_mut(var(receiver), var(arg))
}

/// Run eager existential instantiation after asserting `requires`, then return SAT status.
fn run_eager_sat_status(ensures: &[PureExpr], requires: &[PureExpr]) -> SolveResult {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    for req in requires {
        let t = encoder.encode_pure(req).unwrap();
        encoder.assert_term(t);
    }
    let result =
        assert_eager_negated_existential_instantiations(&mut encoder, ensures, requires, &[]);
    assert!(
        result.is_ok(),
        "eager instantiation should not error, got: {result:?}"
    );
    encoder.check_sat()
}

// ---- Baseline: direct postcondition_mut in body works ----

/// When the existential body directly contains a postcondition_mut call,
/// eager instantiation should assert `NOT body[witness]`, contradicting requires.
#[test]
#[timeout(30000)]
fn eager_instantiation_fires_for_direct_postcondition_mut() {
    let ensures = vec![mk_exists("st", postcondition_mut(var("st"), var("result")))];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "direct postcondition_mut should trigger eager contradiction"
    );
}

/// When postcondition_mut is in a BinOp conjunction, eager instantiation fires.
#[test]
#[timeout(30000)]
fn eager_instantiation_fires_for_binop_conjunction() {
    let body = PureExpr::BinOp(
        Arc::new(postcondition_mut(var("st"), var("result"))),
        BinOp::And,
        Arc::new(gt(var("result"), int(0))),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        gt(var("result"), int(0)),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "BinOp traversal should preserve eager contradiction"
    );
}

// ---- Postcondition traversal through compound forms ----

/// postcondition_mut inside Ite condition must be found by body traversal.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_ite_condition() {
    let body = ite(
        postcondition_mut(var("st"), var("result")),
        bool_expr(true),
        bool_expr(false),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Ite condition traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside Deref wrapper must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_deref() {
    let body = deref(postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![postcondition_mut(deref(var("f")), deref(var("result")))];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Deref traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside Final wrapper must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_final() {
    let body = final_expr(postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        postcondition_mut(final_expr(var("f")), final_expr(var("result"))),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Final traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside View wrapper must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_view() {
    let body = view(postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "View traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside Old wrapper must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_old() {
    let body = old(postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![old(postcondition_mut(var("f"), var("result")))];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Old traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside LetAssume body must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_let_assume() {
    let body = let_assume(bool_expr(true), postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "LetAssume traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside LetObligation body must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_let_obligation() {
    let body = let_obligation(bool_expr(true), postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "LetObligation traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside Let body must be found.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_let_bind() {
    let body = let_bind("tmp", int(0), postcondition_mut(var("st"), var("result")));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Let traversal should trigger eager contradiction"
    );
}

/// postcondition_mut inside Ite branches under AND must still be reached.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_postcondition_mut_in_ite_within_and() {
    let ite_expr = ite(
        bool_expr(true),
        postcondition_mut(var("st"), var("result")),
        bool_expr(false),
    );
    let body = PureExpr::BinOp(Arc::new(bool_expr(true)), BinOp::And, Arc::new(ite_expr));
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Ite nested under And should still trigger eager contradiction"
    );
}

// ---- Non-existential ensures are correctly skipped ----

/// Non-existential postconditions are correctly skipped by eager instantiation.
#[test]
#[timeout(30000)]
fn eager_instantiation_skips_non_existential_ensures() {
    let ensures = vec![gt(var("result"), int(0))];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::Sat,
        "non-existential ensures should be ignored by eager path"
    );
}

/// Empty ensures slice is correctly handled.
#[test]
#[timeout(30000)]
fn eager_instantiation_handles_empty_ensures() {
    let ensures: Vec<PureExpr> = vec![];
    let requires = vec![ground_postcondition_mut("f", "result")];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::Sat,
        "empty ensures should leave solver satisfiable"
    );
}

/// Empty requires slice means no ground terms — eager instantiation is skipped.
#[test]
#[timeout(30000)]
fn eager_instantiation_skips_with_empty_requires() {
    let ensures = vec![mk_exists("st", postcondition_mut(var("st"), var("result")))];
    let requires: Vec<PureExpr> = vec![];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::Sat,
        "without ground requires, eager instantiation should not fire"
    );
}

// ---- Substitution through compound variants ----

/// `substitute_vars_in_expr` must recurse into Let bodies with shadow handling.
#[test]
#[timeout(30000)]
fn eager_instantiation_substitutes_bound_var_in_let_body() {
    let body = and(
        postcondition_mut(var("st"), var("result")),
        let_bind("tmp", var("st"), eq(var("tmp"), var("f"))),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        ne(var("st"), var("f")),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Let body must receive bound-var substitution"
    );
}

/// `substitute_vars_in_expr` must recurse into Match scrutinee/arms.
#[test]
#[timeout(30000)]
fn eager_instantiation_substitutes_bound_var_in_match_body() {
    let body = and(
        postcondition_mut(var("st"), var("result")),
        match_expr(
            var("st"),
            vec![(Pattern::Wildcard, eq(var("st"), var("f")))],
        ),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        ne(var("st"), var("f")),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Match arm bodies must receive bound-var substitution"
    );
}

/// `substitute_vars_in_expr` must recurse into LetAssume body.
#[test]
#[timeout(30000)]
fn eager_instantiation_substitutes_bound_var_in_let_assume_body() {
    let body = and(
        postcondition_mut(var("st"), var("result")),
        let_assume(bool_expr(true), eq(var("st"), var("f"))),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        ne(var("st"), var("f")),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "LetAssume body must receive bound-var substitution"
    );
}

/// `substitute_vars_in_expr` must recurse into Forall bodies.
#[test]
#[timeout(30000)]
fn eager_instantiation_substitutes_bound_var_in_forall_body() {
    let body = and(
        postcondition_mut(var("st"), var("result")),
        forall("x", eq(var("st"), var("f"))),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        ne(var("st"), var("f")),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Forall body must receive bound-var substitution"
    );
}

// ---- Resolve collection coverage ----

/// `collect_resolve_calls_recursive` must traverse Ite branches.
#[test]
#[timeout(30000)]
fn eager_instantiation_collects_resolve_in_ite_branches() {
    let body = and(
        and(
            postcondition_mut(var("f"), var("result")),
            ite(
                bool_expr(true),
                resolve_call(var("st")),
                resolve_call(var("st")),
            ),
        ),
        eq(var("st"), var("f")),
    );
    let ensures = vec![mk_exists("st", body)];
    let requires = vec![
        ground_postcondition_mut("f", "result"),
        resolve_call(var("f")),
    ];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "resolve() inside Ite branches must contribute to witness binding"
    );
}

/// `normalize_deref_final` + ground call collection must handle Ite preconditions.
#[test]
#[timeout(30000)]
fn eager_instantiation_normalizes_deref_inside_ite_precondition() {
    let ground_call = postcondition_mut(deref(var("f")), var("result"));
    let requires = vec![ite(bool_expr(true), ground_call, bool_expr(false))];
    let ensures = vec![mk_exists("st", postcondition_mut(var("st"), var("result")))];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "Ite-wrapped Deref ground calls should normalize and match witnesses"
    );
}

/// Ground `resolve()` collection must recurse into Exists preconditions.
#[test]
#[timeout(30000)]
fn eager_instantiation_collects_resolve_inside_skolemized_existential() {
    let skolem_body = and(
        postcondition_mut(var("f"), var("result")),
        resolve_call(var("f")),
    );
    let requires = vec![PureExpr::Exists {
        var: "f2".to_string(),
        var_sort: None,
        body: Arc::new(skolem_body),
        triggers: vec![],
    }];
    let body = and(
        and(
            postcondition_mut(var("f"), var("result")),
            resolve_call(var("st")),
        ),
        eq(var("st"), var("f")),
    );
    let ensures = vec![mk_exists("st", body)];
    assert_eq!(
        run_eager_sat_status(&ensures, &requires),
        SolveResult::unsat(),
        "resolve() inside Exists preconditions should be usable for witness binding"
    );
}

// ---- normalize_deref_final compound variant coverage (#1221) ----

/// Verifies normalize_deref_final recurses into Ite branches to flatten Deref.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_ite() {
    // Ite(true, Deref(Var("f")), Var("g"))
    let expr = ite(bool_expr(true), deref(var("f")), var("g"));
    let normalized = normalize_deref_final(&expr);
    // After normalization: Ite(true, Var("f"), Var("g")) — Deref stripped
    let expected = ite(bool_expr(true), var("f"), var("g"));
    assert_eq!(
        normalized, expected,
        "Deref inside Ite then-branch should be flattened"
    );
}

/// Verifies normalize_deref_final recurses into Ite to rename Final.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_renames_final_inside_ite() {
    // Ite(true, Final(Var("f")), Var("g"))
    let expr = ite(bool_expr(true), final_expr(var("f")), var("g"));
    let normalized = normalize_deref_final(&expr);
    // After normalization: Ite(true, Var("f_final"), Var("g"))
    let expected = ite(bool_expr(true), var("f_final"), var("g"));
    assert_eq!(
        normalized, expected,
        "Final(Var) inside Ite should become Var(_final)"
    );
}

/// Verifies normalize_deref_final recurses into Let value and body.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_let() {
    // Let("x", Deref(Var("f")), Final(Var("g")))
    let expr = let_bind("x", deref(var("f")), final_expr(var("g")));
    let normalized = normalize_deref_final(&expr);
    let expected = let_bind("x", var("f"), var("g_final"));
    assert_eq!(
        normalized, expected,
        "Deref/Final inside Let should be normalized"
    );
}

/// Verifies normalize_deref_final recurses into Forall body.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_forall() {
    // forall<x> Deref(Var("f")) > x
    let expr = forall("x", gt(deref(var("f")), var("x")));
    let normalized = normalize_deref_final(&expr);
    let expected = forall("x", gt(var("f"), var("x")));
    assert_eq!(
        normalized, expected,
        "Deref inside Forall body should be flattened"
    );
}

/// Verifies normalize_deref_final recurses into LetAssume.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_let_assume() {
    // LetAssume(Deref(Var("f")) > 0, Final(Var("g")))
    let expr = let_assume(gt(deref(var("f")), int(0)), final_expr(var("g")));
    let normalized = normalize_deref_final(&expr);
    let expected = let_assume(gt(var("f"), int(0)), var("g_final"));
    assert_eq!(
        normalized, expected,
        "Deref/Final inside LetAssume should be normalized"
    );
}

/// Verifies normalize_deref_final recurses into Exists body and triggers.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_exists() {
    // exists<x> Deref(Var("f")) > x
    let expr = exists("x", gt(deref(var("f")), var("x")));
    let normalized = normalize_deref_final(&expr);
    let expected = exists("x", gt(var("f"), var("x")));
    assert_eq!(
        normalized, expected,
        "Deref inside Exists body should be flattened"
    );
}

/// Verifies normalize_deref_final recurses into LetObligation.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_let_obligation() {
    // LetObligation(Deref(Var("f")) > 0, Final(Var("g")))
    let expr = let_obligation(gt(deref(var("f")), int(0)), final_expr(var("g")));
    let normalized = normalize_deref_final(&expr);
    let expected = let_obligation(gt(var("f"), int(0)), var("g_final"));
    assert_eq!(
        normalized, expected,
        "Deref/Final inside LetObligation should be normalized"
    );
}

/// Verifies normalize_deref_final recurses into Match scrutinee and arm bodies.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_match() {
    use trust_wp_core::formula::Pattern;
    // Match(Deref(Var("f")), [Wildcard => Final(Var("g"))])
    let expr = match_expr(
        deref(var("f")),
        vec![(Pattern::Wildcard, final_expr(var("g")))],
    );
    let normalized = normalize_deref_final(&expr);
    let expected = match_expr(var("f"), vec![(Pattern::Wildcard, var("g_final"))]);
    assert_eq!(
        normalized, expected,
        "Deref/Final inside Match should be normalized"
    );
}

/// Verifies normalize_deref_final recurses into Closure body.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_flattens_deref_inside_closure() {
    // Closure(|x| Deref(Var("f")) + Final(Var("g")))
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(deref(var("f"))),
            BinOp::Add,
            Arc::new(final_expr(var("g"))),
        )),
    };
    let normalized = normalize_deref_final(&expr);
    let expected = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("f")),
            BinOp::Add,
            Arc::new(var("g_final")),
        )),
    };
    assert_eq!(
        normalized, expected,
        "Deref/Final inside Closure body should be normalized"
    );
}

/// Verifies normalize_deref_final handles nested Final(Final(Var)).
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_double_final() {
    // Final(Final(Var("f"))) -> Var("f_final_final")
    let expr = final_expr(final_expr(var("f")));
    let normalized = normalize_deref_final(&expr);
    assert_eq!(
        normalized,
        var("f_final_final"),
        "double Final should append _final twice"
    );
}

/// Verifies normalize_deref_final strips Deref from nested Final(Deref(Var)).
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_final_deref_composition() {
    // Final(Deref(Var("f"))) -> Final(Var("f")) -> Var("f_final")
    let expr = final_expr(deref(var("f")));
    let normalized = normalize_deref_final(&expr);
    assert_eq!(
        normalized,
        var("f_final"),
        "Final(Deref(Var)) should become Var(_final) after Deref strip"
    );
}

/// Verifies normalize_deref_final recurses into LogicFnCall args.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_in_logic_fn_call() {
    let expr = logic_fn_call("resolve", vec![final_expr(var("f"))]);
    let normalized = normalize_deref_final(&expr);
    let expected = logic_fn_call("resolve", vec![var("f_final")]);
    assert_eq!(
        normalized, expected,
        "Final inside LogicFnCall args should be normalized"
    );
}

/// Verifies normalize_deref_final recurses into UnOp inner.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_in_unop() {
    let expr = not(deref(var("f")));
    let normalized = normalize_deref_final(&expr);
    let expected = not(var("f"));
    assert_eq!(normalized, expected, "Deref inside UnOp should be stripped");
}

/// Verifies normalize_deref_final preserves leaves unchanged.
#[test]
#[timeout(30000)]
fn test_normalize_deref_final_leaves_unchanged() {
    assert_eq!(normalize_deref_final(&var("x")), var("x"));
    assert_eq!(normalize_deref_final(&int(42)), int(42));
    assert_eq!(normalize_deref_final(&bool_expr(true)), bool_expr(true));
}
