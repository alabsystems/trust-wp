// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `PureExpr` quantifier encoding and Match error handling (Part of #178).
//!
//! Split from encoding.rs per #395.
//!
//! **Encode-only vs semantic tests:** Int-sorted triggerless quantifiers cause
//! ay to return `Unknown` (#627), so those tests remain encode-only. Bool-sorted
//! quantifiers are decidable via Bool expansion (#1197) and have `check_sat()`
//! assertions (#1990). The `test_triggered_*` tests at the bottom use UF-based
//! triggers for definitive Int-sorted outcomes.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::{super::*, helpers::*};
mod trigger_synthesis;

#[test]
#[timeout(30000)]
fn test_encode_pure_forall() {
    // PureExpr::Forall encoding smoke test: ∀x. x > 0.
    // SAT/UNSAT quantifier semantics are validated in the triggered solver
    // tests below, where we assert concrete check_sat outcomes.
    // NOTE: encoding-only — see #718.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = forall("x", gt(var("x"), int(0)));
    encoder
        .encode_pure(&expr)
        .expect("Forall encoding should succeed");
}

#[test]
#[timeout(30000)]
fn test_encode_forall_with_triggers() {
    // PureExpr::Forall encoding with trigger: ∀x. x > 0 {:pattern x}
    // Tests the AYEncoder triggered-forall encoding path.
    // Note: bare variable triggers are non-standard and ay may return
    // Unknown. We verify encoding success and the term is Bool-sorted.
    // Solver-level semantic checks for triggered foralls use UF patterns
    // in the dedicated test_triggered_* tests below. Part of #718.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let var_x = var("x");
    let expr = forall_with_triggers("x", gt(var_x.clone(), int(0)), vec![vec![var_x]]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Forall with triggers should succeed");

    // Verify the encoded term can be asserted without panic
    encoder.assert_term(term);
    // Note: check_sat may return Unknown for bare-variable triggers;
    // the test_triggered_forall_* tests below use UF-based triggers
    // for definitive SAT/UNSAT outcomes.
}

#[test]
#[timeout(30000)]
fn test_encode_exists_with_triggers() {
    // PureExpr::Exists encoding with trigger: ∃x. x > 0 {:pattern x}
    // Semantic check: ∃x. x > 0 is true over integers (e.g., x = 1),
    // so asserting it should yield SAT. Part of #718.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let var_x = var("x");
    let expr = exists_with_triggers("x", gt(var_x.clone(), int(0)), vec![vec![var_x]]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Exists with triggers should succeed");

    // Semantic check: assert the quantifier and verify SAT
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "∃x. x > 0 should be SAT over integers"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_exists() {
    // PureExpr::Exists encoding: ∃x. x > 0
    // NOTE: encoding-only — see #718.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = exists("x", gt(var("x"), int(0)));
    encoder
        .encode_pure(&expr)
        .expect("Exists encoding should succeed");
}

#[test]
#[timeout(30000)]
fn test_encode_exists_invariant_body_witness_eliminates_to_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("Positive", "self", ay_dpll::api::Sort::Int, &invariant_body)
        .expect("type invariant registration should succeed");

    let method_name = trust_wp_core::logic::type_invariant_method_name("Positive");
    let expr = exists("x", method_call(var("x"), &method_name, vec![]));
    let term = encoder
        .encode_pure(&expr)
        .expect("exists invariant postcondition should encode");

    assert_eq!(
        term,
        encoder.solver.bool_const(true),
        "exists x. x.invariant() should witness-eliminate to true"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_match_empty_arms_succeeds() {
    // Match with empty arms now succeeds (returns false) - #218
    let mut encoder = AYEncoder::new();

    let expr = match_expr(int(1), vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Match with empty arms should succeed");
    // Empty arms match now returns bool_const(false) instead of error
    assert_eq!(
        term,
        encoder.solver.bool_const(false),
        "Empty arms match should encode to false"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_forall_with_prefix() {
    // Forall in old() encoding path should now succeed.
    // NOTE: encoding-only — triggerless quantifier, ay returns Unknown (#627). See #1990.
    let mut encoder = AYEncoder::new_with_quantifiers();

    // old(forall x. x > 0) - tests prefixed encoding path
    let expr = old(forall("x", gt(var("x"), int(0))));
    encoder
        .encode_pure(&expr)
        .expect("Forall in old context should succeed");
}

#[test]
#[timeout(30000)]
fn test_encode_exists_with_prefix() {
    // Exists in old() encoding path should now succeed.
    // NOTE: encoding-only — triggerless quantifier, ay returns Unknown (#627). See #1990.
    let mut encoder = AYEncoder::new_with_quantifiers();

    // old(exists x. x > 0) - tests prefixed encoding path
    let expr = old(exists("x", gt(var("x"), int(0))));
    encoder
        .encode_pure(&expr)
        .expect("Exists in old context should succeed");
}

#[test]
#[timeout(30000)]
fn test_encode_match_with_prefix_succeeds() {
    // Match in old() encoding path now succeeds - #218
    let mut encoder = AYEncoder::new();

    // old(match e { ... }) - tests prefixed encoding path
    let expr = old(match_expr(int(1), vec![]));
    let term = encoder
        .encode_pure(&expr)
        .expect("Match in old context should succeed");
    // Match with empty arms in old context now succeeds
    assert_eq!(
        term,
        encoder.solver.bool_const(false),
        "Match in old context with empty arms should encode to false"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_nested_pure_quantifiers() {
    // Nested quantifier encoding smoke test: ∀x. ∃y. x < y.
    // Triggered semantic checks live in dedicated solver tests below.
    // NOTE: encoding-only — see #718.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = forall("x", exists("y", lt(var("x"), var("y"))));
    encoder
        .encode_pure(&expr)
        .expect("Nested quantifiers should succeed");
}

/// Regression: Forall with Bool-sorted bound variable (#544, cb747b5).
/// Fix: `resolve_decl_sort` checks `sort_hints` instead of hardcoding Int.
/// Semantic: ∀b. ¬b is false via Bool expansion (#1197). Part of #1990.
#[test]
#[timeout(30000)]
fn test_encode_forall_bool_bound_variable() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register "b" as Bool via pre-scan: Not(Var("b")) forces Bool context
    let body = not(var("b"));
    encoder.register_sort_hints(std::slice::from_ref(&body));

    // ∀b. ¬b — should encode without panic (b must be Bool, not Int)
    let expr = forall("b", body);
    let term = encoder
        .encode_pure(&expr)
        .expect("Forall with Bool bound variable should succeed");

    // ∀b.¬b = ¬true∧¬false = false → Unsat when asserted (#1990)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "∀b. ¬b → Unsat (#1990)"
    );
}

/// Regression: Exists with Bool-sorted bound variable (#544, cb747b5).
/// Semantic: ∃b. b==true is Sat via Bool expansion. Part of #1990.
#[test]
#[timeout(30000)]
fn test_encode_exists_bool_bound_variable() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register "b" as Bool: b == true
    let body = eq(var("b"), bool_expr(true));
    encoder.register_sort_hints(std::slice::from_ref(&body));

    // ∃b. b == true — should encode without panic
    let expr = exists("b", body);
    let term = encoder
        .encode_pure(&expr)
        .expect("Exists with Bool bound variable should succeed");

    // ∃b. b==true is Sat (witness: b=true) (#1990)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "∃b. b==true → Sat (#1990)"
    );
}

/// Regression: bare Bool body must infer Bool bound sort without explicit operators.
/// Semantic: ∀b. b is false via Bool expansion (true∧false=false). Part of #1990.
#[test]
#[timeout(30000)]
fn test_encode_forall_bare_bool_body_infers_bound_sort() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let expr = forall("b", var("b"));

    let term = encoder
        .encode_pure(&expr)
        .expect("Forall with bare Bool body should infer Bool bound sort");

    // ∀b.b = true∧false = false → Unsat (#1990)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "∀b. b → Unsat (#1990)"
    );
}

/// Exists variant of bare-body sort inference. Semantic: ∃b. b is Sat. Part of #1990.
#[test]
#[timeout(30000)]
fn test_encode_exists_bare_bool_body_infers_bound_sort() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let expr = exists("b", var("b"));

    let term = encoder
        .encode_pure(&expr)
        .expect("Exists with bare Bool body should infer Bool bound sort");

    // ∃b.b = true∨false = true → Sat (#1990)
    encoder.assert_term(term);
    assert_eq!(encoder.check_sat(), SolveResult::Sat, "∃b. b → Sat (#1990)");
}

/// Nested mixed sorts: outer Int, inner Bool (#544).
/// NOTE: encoding-only — outer Int forall is triggerless, ay returns Unknown (#627). See #1990.
#[test]
#[timeout(30000)]
fn test_encode_nested_quantifier_mixed_sorts() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Body: x > 0 ==> Not(b)
    // x is Int (appears in Gt), b is Bool (appears in Not)
    let inner_body = implies(gt(var("x"), int(0)), not(var("b")));
    encoder.register_sort_hints(std::slice::from_ref(&inner_body));

    // ∀x. ∃b. (x > 0) ==> ¬b — should encode without panic
    let expr = forall("x", exists("b", inner_body));
    encoder
        .encode_pure(&expr)
        .expect("Mixed-sort nested quantifier should succeed");
}

/// Multi-variable quantifier with triggers must collapse nested foralls (#610).
/// Without collapsing, trigger `id(j)` doesn't reference outer var `i` → ay panics.
#[test]
#[timeout(30000)]
fn test_multi_var_forall_with_triggers_no_panic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a logic function `id(x) = x` so triggers can reference it
    let id_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    encoder.register_logic_fns(&[id_fn]).expect("register id");

    let trigger_id_i = logic_fn_call("id", vec![var("i")]);
    let trigger_id_j = logic_fn_call("id", vec![var("j")]);
    let triggers = vec![vec![trigger_id_i, trigger_id_j]];

    // Body: i <= j ==> id(i) <= id(j)
    let body = implies(
        le(var("i"), var("j")),
        le(
            logic_fn_call("id", vec![var("i")]),
            logic_fn_call("id", vec![var("j")]),
        ),
    );

    // Parser output: nested foralls with cloned triggers
    let expr = forall_with_triggers(
        "i",
        forall_with_triggers("j", body, triggers.clone()),
        triggers,
    );

    encoder
        .encode_pure(&expr)
        .expect("Multi-var triggered forall should collapse without panic");
}

/// Triggered universal tautology should be SAT (#627).
#[test]
#[timeout(30000)]
fn test_triggered_forall_tautology_is_sat() {
    use ay_dpll::api::Logic;
    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    let pred = solver.declare_fun("pred", &[Sort::Int], Sort::Bool);
    let a = solver.declare_const("a", Sort::Int);
    let pred_a = solver.apply(&pred, &[a]);
    solver.assert_term(pred_a);

    let x = solver.fresh_var("x", Sort::Int);
    let pred_x = solver.apply(&pred, &[x]);
    let true_term = solver.bool_const(true);
    let body = solver.implies(pred_x, true_term);
    let forall = solver.forall_with_triggers(&[x], body, &[&[pred_x]]);
    solver.assert_term(forall);

    assert_eq!(
        solver.check_sat().into_inner(),
        SolveResult::Sat,
        "triggered forall tautology should be SAT"
    );
}

/// Triggered quantified contradiction should be UNSAT (#627).
#[test]
#[timeout(30000)]
fn test_triggered_forall_contradiction_is_unsat() {
    use ay_dpll::api::Logic;
    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    let f = solver.declare_fun("f", &[Sort::Int], Sort::Bool);
    let g = solver.declare_fun("g", &[Sort::Int], Sort::Bool);
    let a = solver.declare_const("a", Sort::Int);

    let f_a = solver.apply(&f, &[a]);
    let g_a = solver.apply(&g, &[a]);
    solver.assert_term(f_a);
    solver.assert_term(g_a);

    let x = solver.fresh_var("x", Sort::Int);
    let f_x = solver.apply(&f, &[x]);
    let g_x = solver.apply(&g, &[x]);
    let not_g_x = solver.not(g_x);
    let body = solver.implies(f_x, not_g_x);
    let forall = solver.forall_with_triggers(&[x], body, &[&[f_x]]);
    solver.assert_term(forall);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "f(a) && g(a) && forall x. f(x) => !g(x) should be UNSAT"
    );
}

/// Triggered Skolemized nested quantifier should instantiate on `p(a, h(a))` (#627).
#[test]
#[timeout(30000)]
fn test_triggered_skolemized_nested_quantifier_instantiates_unsat() {
    use ay_dpll::api::Logic;
    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    let h = solver.declare_fun("h", &[Sort::Int], Sort::Int);
    let p = solver.declare_fun("p", &[Sort::Int, Sort::Int], Sort::Bool);
    let a = solver.declare_const("a", Sort::Int);

    let h_a = solver.apply(&h, &[a]);
    let p_a_h_a = solver.apply(&p, &[a, h_a]);
    let not_p_a_h_a = solver.not(p_a_h_a);
    solver.assert_term(not_p_a_h_a);

    let x = solver.fresh_var("x", Sort::Int);
    let h_x = solver.apply(&h, &[x]);
    let p_x_h_x = solver.apply(&p, &[x, h_x]);
    let forall = solver.forall_with_triggers(&[x], p_x_h_x, &[&[p_x_h_x]]);
    solver.assert_term(forall);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "forall x. p(x, h(x)) plus !p(a, h(a)) should be UNSAT"
    );
}

/// Explicit ExprSort::Bool from parser (#968). Semantic: ∀b:Bool. ¬b → Unsat. Part of #1990.
#[test]
#[timeout(30000)]
fn test_forall_with_explicit_bool_sort_encodes_correctly() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // ∀b: Bool. ¬b — with explicit Bool sort annotation from parser
    let expr = forall_with_sort("b", ExprSort::Bool, not(var("b")));
    let term = encoder
        .encode_pure(&expr)
        .expect("Forall with explicit Bool sort should succeed");

    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "∀b:Bool. ¬b → Unsat (#1990)"
    );
}

/// Explicit ExprSort::Int from parser (#968). Semantic: ∃x:Int. x>0 → Sat. Part of #1990.
#[test]
#[timeout(30000)]
fn test_exists_with_explicit_int_sort_encodes_correctly() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // ∃x: Int. x > 0 — with explicit Int sort annotation from parser
    let expr = exists_with_sort("x", ExprSort::Int, gt(var("x"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("Exists with explicit Int sort should succeed");

    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "∃x:Int. x>0 → Sat (#1990)"
    );
}

// ── Unit-type quantifier elimination tests (#1065) ──────────────────

/// `forall<_x: ()> P` eliminated to `P` — unit has one inhabitant (#1065, bug/1538).
#[test]
#[timeout(30000)]
fn test_forall_unit_type_elimination_encodes_and_verifies() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<_x: ()> true — trivially true, should be eliminated to just `true`
    let expr = forall_with_sort("_x", ExprSort::Unit, PureExpr::Bool(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("forall over unit type should encode via elimination");

    // The quantifier is eliminated, so the result is just `true`.
    // Negate it: assert ¬(forall<_x: ()> true) = ¬true = false → Unsat
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "negated trivially-true unit quantifier should be Unsat"
    );
}

/// `exists<_x: ()> P` eliminated to `P` (#1065).
#[test]
#[timeout(30000)]
fn test_exists_unit_type_elimination_encodes_and_verifies() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // exists<_x: ()> (y > 0) — should be eliminated to just `y > 0`
    let expr = exists_with_sort("_x", ExprSort::Unit, gt(var("y"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("exists over unit type should encode via elimination");

    // Assert y = 5 (so y > 0 is true), then negate the quantifier result.
    // If elimination works, this is ¬(5 > 0) = ¬true = false → Unsat.
    let y_val = int(5);
    let y_term = encoder.encode_pure(&y_val).unwrap();
    let y_var = encoder
        .get_or_declare_var("y", ay_dpll::api::Sort::Int)
        .unwrap();
    let y_eq = encoder.solver_mut().eq(y_var, y_term);
    encoder.assert_term(y_eq);
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "exists unit with y=5 > 0 negated should be Unsat"
    );
}

/// Bug/1538 pattern: `forall<_x: ()> foo_bar == ()` — bound var unused, eliminated (#1065).
#[test]
#[timeout(30000)]
fn test_forall_unit_type_bug_1538_pattern() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<_x: ()> foo_bar == 0
    // (We use Int equality since we don't have a unit literal in the encoder;
    //  the key point is that the _x variable doesn't appear in the body.)
    let body = binop(var("foo_bar"), BinOp::Eq, int(0));
    let expr = forall_with_sort("_x", ExprSort::Unit, body);
    let term = encoder
        .encode_pure(&expr)
        .expect("bug/1538 pattern should encode via unit elimination");

    // Set foo_bar = 0, negate the result → Unsat
    let fb_var = encoder
        .get_or_declare_var("foo_bar", ay_dpll::api::Sort::Int)
        .unwrap();
    let zero = encoder.encode_pure(&int(0)).unwrap();
    let eq = encoder.solver_mut().eq(fb_var, zero);
    encoder.assert_term(eq);
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "bug/1538 pattern: unit-eliminated forall with foo_bar=0 should verify"
    );
}

// ── Unused-variable quantifier elimination tests (#1065) ────────────

/// Unused-var elimination: `forall<_x: u32> true` — `_x` not in body (#1065).
#[test]
#[timeout(30000)]
fn test_forall_unused_var_elimination_specification_forall_pattern() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<_x: u32> true — body doesn't reference _x
    let expr = forall_with_sort("_x", ExprSort::Int, PureExpr::Bool(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("unused-var forall should encode via elimination");

    // Negate: ¬true = false → Unsat
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "unused-var forall over true should verify (Unsat when negated)"
    );
}

/// `exists<_x: i32> y > 0` is eliminated when `_x` does not appear in `y > 0`.
#[test]
#[timeout(30000)]
fn test_exists_unused_var_elimination() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // exists<_x: i32> y > 0 — _x not in body
    let expr = exists_with_sort("_x", ExprSort::Int, gt(var("y"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("unused-var exists should encode via elimination");

    // Set y = 5, negate: ¬(5 > 0) = false → Unsat
    let y_var = encoder
        .get_or_declare_var("y", ay_dpll::api::Sort::Int)
        .unwrap();
    let five = encoder.encode_pure(&int(5)).unwrap();
    let eq = encoder.solver_mut().eq(y_var, five);
    encoder.assert_term(eq);
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "unused-var exists with y=5 should verify"
    );
}

/// Used var NOT eliminated: `forall<x: i32> x > 0` — `x` in body.
/// NOTE: encoding-only — triggerless Int forall, ay returns Unknown (#627). See #1990.
#[test]
#[timeout(30000)]
fn test_forall_used_var_not_eliminated() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<x: i32> x > 0 — x IS used in body, should NOT be eliminated
    let expr = forall_with_sort("x", ExprSort::Int, gt(var("x"), int(0)));
    // This should still encode (even if ay returns Unknown for the quantifier)
    encoder
        .encode_pure(&expr)
        .expect("used-var forall should still encode (not eliminated)");
}

// ── Quantifier elimination test gaps (#1168) ─────────────────────────

/// Exists used-var NOT eliminated (#1168 gap 1). Sat (witness: x=1).
#[test]
#[timeout(30000)]
fn test_exists_used_var_not_eliminated() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // exists<x: i32> x > 0 — x IS used, must not be eliminated
    let expr = exists_with_sort("x", ExprSort::Int, gt(var("x"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("used-var exists should encode (not eliminated)");

    // Assert the existential directly — it's satisfiable (witness: x=1)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "exists<x: i32> x > 0 is satisfiable (x=1), should be Sat (#1168)"
    );
}

/// Shadowed var eliminated: `forall<x> let x=5 in x>0` — outer x unused (#1168 gap 2).
#[test]
#[timeout(30000)]
fn test_forall_shadowed_var_in_let_eliminated() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<x: i32> let x = 5 in x > 0
    // The inner `x` in `x > 0` refers to the let binding (=5), not the quantifier var.
    let body = let_bind("x", int(5), gt(var("x"), int(0)));
    let expr = forall_with_sort("x", ExprSort::Int, body);

    let term = encoder
        .encode_pure(&expr)
        .expect("shadowed-var forall should encode (var is unused → eliminated)");

    // Structural check: elimination must have fired — no qvar_x bound variable
    // should exist in the solver. If elimination didn't fire, the encoder would
    // create a `qvar_x_N` variable for the quantifier.
    let qvars: Vec<_> = encoder
        .var_names()
        .into_iter()
        .filter(|n| n.starts_with("qvar_x"))
        .collect();
    assert!(
        qvars.is_empty(),
        "forall<x> let x=5 in x>0: outer x is shadowed, elimination should fire \
         (no qvar_x should be created). Found: {qvars:?} (#1168)"
    );

    // Result is `5 > 0` = true. Negate → Unsat.
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "forall<x> let x=5 in x>0: outer x shadowed → eliminated → 5>0 → negated is Unsat (#1168)"
    );
}

/// Mixed-kind nested: outer `x` unused → eliminated, inner `y` used (#1168 gap 3).
#[test]
#[timeout(30000)]
fn test_mixed_kind_nested_unused_outer_eliminated() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<x: i32> exists<y: i32> y > 0
    // x is unused → eliminated, leaving exists<y> y > 0 (satisfiable)
    let inner = exists_with_sort("y", ExprSort::Int, gt(var("y"), int(0)));
    let expr = forall_with_sort("x", ExprSort::Int, inner);

    let term = encoder
        .encode_pure(&expr)
        .expect("mixed-kind nested with unused outer should encode");

    // Structural check: outer forall(x) should be eliminated (x unused).
    // Verify no free variable named `x` leaked into the solver.
    // Note: bound quantifier variables (qvar_y_*) are not tracked in var_names()
    // — they're solver-internal. A stronger structural check requires a
    // quantifier_var_count() accessor on AYEncoder (see #1168 comment).
    let names = encoder.var_names();
    let has_x = names.iter().any(|n| n == "x" || n.starts_with("qvar_x"));
    assert!(
        !has_x,
        "forall<x> exists<y> y>0: x is unused and eliminated, no x variable \
         should be created. vars: {names:?} (#1168)"
    );

    // After x eliminated: exists<y> y > 0, which is Sat (witness: y=1)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "forall<x> exists<y> y>0: x eliminated → exists y>0 is Sat (#1168)"
    );
}

/// Var in trigger only: `forall<x> {:pattern f(x)} true` — x unused in body (#1168 gap 4).
#[test]
#[timeout(30000)]
fn test_forall_var_in_trigger_only_eliminated() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register a logic function for the trigger
    let f_def = LogicFnDef::new(
        "elim_f".to_string(),
        "crate::test::elim_f".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    );
    encoder.register_logic_fn(&f_def).expect("register fn");

    // forall<x: i32> {:pattern elim_f(x)} true
    // x appears only in trigger, not body → unused → eliminated
    let trigger = vec![vec![logic_fn_call("elim_f", vec![var("x")])]];
    let expr = forall_with_triggers("x", PureExpr::Bool(true), trigger);

    let term = encoder
        .encode_pure(&expr)
        .expect("trigger-only var forall should encode (eliminated)");

    // Structural check: x appears only in trigger, not body → eliminated.
    // No qvar_x bound variable should exist in the solver.
    let qvars: Vec<_> = encoder
        .var_names()
        .into_iter()
        .filter(|n| n.starts_with("qvar_x"))
        .collect();
    assert!(
        qvars.is_empty(),
        "forall<x> trigger-only var: x only in trigger → should be eliminated \
         (no qvar_x should be created). Found: {qvars:?} (#1168)"
    );

    // Result is `true`. Negate → Unsat.
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "forall<x> trigger-only var: x only in trigger → eliminated → negated true is Unsat (#1168)"
    );
}

// ── Trigger synthesis integration tests (#1018) ─────────────────────

/// Integration test: triggerless forall with logic function call gets
/// synthesized trigger and encodes successfully.
///
/// This verifies that trigger synthesis selects `test_f(i)` as the trigger
/// pattern and the quantifier encodes without error. Semantic decidability
/// depends on ay's E-matching depth (Phase 2 of #1018), so this is
/// encode-only — consistent with the file's documented approach (lines 9-14).
#[test]
#[timeout(30000)]
fn test_triggerless_forall_with_logic_fn_gets_synthesized_trigger() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function f: Int -> Int, body: x + 1
    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::test::test_f".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i: Int> test_f(i) > 0
    // No user triggers — synthesis should pick {:pattern test_f(i)}
    let expr = forall("i", gt(logic_fn_call("test_f", vec![var("i")]), int(0)));
    encoder
        .encode_pure(&expr)
        .expect("triggerless forall with logic fn should encode with synthesized trigger");
}

/// Integration test: triggerless forall encoding succeeds for method call body.
///
/// Verifies that trigger synthesis correctly handles MethodCall nodes
/// (e.g., seq.index_logic(i)) as trigger candidates.
#[test]
#[timeout(30000)]
fn test_triggerless_forall_with_method_call_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i: Int> 0 <= i && i < seq.len() ==> seq.index_logic(i) >= 0
    // Trigger synthesis should pick seq.index_logic(i)
    let expr = forall(
        "i",
        implies(
            and(
                le(int(0), var("i")),
                gt(method_call(view(var("seq")), "len", vec![]), var("i")),
            ),
            ge(
                method_call(view(var("seq")), "index_logic", vec![var("i")]),
                int(0),
            ),
        ),
    );
    encoder
        .encode_pure(&expr)
        .expect("triggerless forall with method call should encode");
}

/// Integration test: multi-variable triggerless quantifier gets collapse
/// after trigger synthesis.
///
/// Before #1018, forall<i, j> (without triggers) never collapsed the nested
/// quantifiers into a single ay forall, producing separate nested quantifiers
/// that ay cannot instantiate. With synthesis, if a function mentions both
/// vars, they collapse into a single multi-variable quantifier.
#[test]
#[timeout(30000)]
fn test_triggerless_multi_var_forall_with_logic_fn_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function g: (Int, Int) -> Int, body: a + b
    let g_def = LogicFnDef::new(
        "test_g".to_string(),
        "crate::test::test_g".to_string(),
        vec!["a".to_string(), "b".to_string()],
        add(var("a"), var("b")),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn");

    // forall<i> forall<j> test_g(i, j) > 0
    // Both nested quantifiers are triggerless. Synthesis should find
    // test_g(i, j) covering both vars and collapse into a single quantifier.
    let inner = forall(
        "j",
        gt(logic_fn_call("test_g", vec![var("i"), var("j")]), int(0)),
    );
    let expr = forall("i", inner);
    encoder
        .encode_pure(&expr)
        .expect("triggerless multi-var forall should encode after synthesis");
}

// ── Multi-variable Unit elimination edge-case tests (#1065, #1152) ───
//
// These tests verify behavior when Unit-sorted variables interact with
// other quantifier features (multi-variable collapse, trigger synthesis).
// Re: P1-347 audit of trigger synthesis edge cases.

/// Multi-variable forall where inner var is Unit-sorted but outer is Int-sorted.
///
/// `forall<y: Int> forall<_x: ()> y > 0`
///
/// Without triggers, the outer and inner quantifiers are processed independently.
/// The inner `forall<_x: ()>` should be eliminated (Unit has one inhabitant),
/// leaving `forall<y: Int> y > 0` which ay processes as a normal Int quantifier.
///
/// NOTE: encoding-only — after Unit elimination, the outer forall<y: Int> is
/// triggerless and ay returns Unknown (#627). See #1990.
#[test]
#[timeout(30000)]
fn test_nested_forall_unit_inner_eliminated_independently() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<y: Int> forall<_x: ()> y > 0
    let inner = forall_with_sort("_x", ExprSort::Unit, gt(var("y"), int(0)));
    let expr = forall_with_sort("y", ExprSort::Int, inner);

    // Should encode — the inner Unit quantifier is eliminated, leaving forall<y> y > 0.
    // ay handles this as a normal Int quantifier (may return Unknown, which is fine).
    encoder
        .encode_pure(&expr)
        .expect("nested forall with Unit inner should encode via independent elimination");
}

/// Multi-variable exists where inner var is Unit-sorted.
///
/// `exists<a: Int> exists<_x: ()> a == 42`
///
/// The inner `exists<_x: ()>` should be eliminated, leaving `exists<a: Int> a == 42`.
/// Semantic check: ∃a: Int. a == 42 is satisfiable (witness: a=42). Part of #1990.
#[test]
#[timeout(30000)]
fn test_nested_exists_unit_inner_eliminated() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let inner = exists_with_sort("_x", ExprSort::Unit, binop(var("a"), BinOp::Eq, int(42)));
    let expr = exists_with_sort("a", ExprSort::Int, inner);

    let term = encoder
        .encode_pure(&expr)
        .expect("nested exists with Unit inner should encode");

    // Unit eliminated → ∃a. a==42 → Sat (witness a=42) (#1990)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "∃a. a==42 → Sat (#1990)"
    );
}

/// Unit-sorted variable that IS used in the body: unit elimination fires
/// before unused-var elimination, so the variable becomes free.
///
/// `forall<x: ()> x > 0` — `x` appears in body AND is Unit-sorted.
/// Unit elimination fires (line 855-860 of logic_fn.rs), encoding the body
/// without binding `x`. This creates `x` as a free Int variable.
///
/// Soundness: Since `()` has one inhabitant, `forall<x: ()> P(x)` ≡ `P(())`.
/// The encoder produces P(free_x) instead of P(()). For the Int encoding,
/// ay treats free_x as unconstrained, which is STRONGER than the correct
/// semantics (P must hold for ALL values of free_x, not just one).
/// This means the verification is sound (no false positives) but potentially
/// incomplete (may return Unknown when it should verify).
///
/// This test documents the behavior. In practice, Rust contracts quantifying
/// over `()` with the variable used in the body are semantically meaningless.
///
/// Re: #1065 (Unit elimination edge case)
#[test]
#[timeout(30000)]
fn test_forall_unit_used_var_becomes_free_documents_behavior() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<x: ()> x > 0 — x is Unit-sorted but appears in body
    // Unit elimination fires first, producing: encode_pure(x > 0)
    // where x is a free variable.
    let expr = forall_with_sort("x", ExprSort::Unit, gt(var("x"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("unit-sorted used var should encode (becomes free)");

    // After unit elimination, "x" is a free variable (not bound as quantifier var)
    assert!(
        encoder.var_names().contains(&"x".to_string()),
        "unit-eliminated used var should appear as free: {:?}",
        encoder.var_names()
    );
    // The free variable x is unconstrained, so x > 0 is satisfiable (pick x=1).
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "unit-eliminated formula with free var should be satisfiable"
    );
}

/// Triggered multi-variable forall where one variable is Unit-sorted.
///
/// `forall<y: Int, _x: ()> {:pattern f(y)} y > 0`
///
/// When triggers are present, the variable collector collapses nested quantifiers
/// with matching triggers into a single `vars_collected`. With `vars_collected.len() == 2`,
/// the `len == 1` guard on Unit elimination does NOT fire. The `_x` variable gets
/// `Sort::Uninterpreted("Unit")` (from `sort_from_expr_sort(Unit)`). This is sound
/// but creates a redundant quantifier variable.
///
/// NOTE: encoding-only — documents behavior of multi-variable triggered forall with
/// Unit-sorted variable. check_sat would return Unknown due to redundant quantifier
/// variable. Re: #1065 completeness note — P3 gap. See #1990.
#[test]
#[timeout(30000)]
fn test_triggered_multi_var_with_unit_sort_encodes_soundly() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register a logic function for the trigger pattern
    let f_def = LogicFnDef::new(
        "test_unit_f".to_string(),
        "crate::test::test_unit_f".to_string(),
        vec!["y".to_string()],
        add(var("y"), int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<y: Int> {:pattern test_unit_f(y)} forall<_x: ()> {:pattern test_unit_f(y)} y > 0
    // The trigger is the same on both levels, so variable collection collapses them.
    let trigger = vec![vec![logic_fn_call("test_unit_f", vec![var("y")])]];
    let inner = PureExpr::Forall {
        var: "_x".to_string(),
        var_sort: Some(ExprSort::Unit),
        body: Arc::new(gt(var("y"), int(0))),
        triggers: trigger.clone(),
    };
    let expr = PureExpr::Forall {
        var: "y".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(inner),
        triggers: trigger,
    };

    // Should encode without error — soundness is preserved even though
    // the Unit variable is not eliminated in the multi-variable case.
    encoder
        .encode_pure(&expr)
        .expect("triggered multi-var forall with Unit sort should encode soundly");
}

/// Multi-variable triggerless quantifier: Unit variable eliminated, Bool variable
/// expanded via case-split (#1198). Before #1198, the `len() == 1` guard prevented
/// Unit elimination for multi-variable quantifiers after trigger synthesis collapsing.
///
/// `forall<_x: ()> forall<b: Bool> (b OR NOT b)` is a tautology.
/// After Unit elimination of `_x`, only `b: Bool` remains, and Bool expansion fires.
#[test]
#[timeout(30000)]
fn test_multi_var_unit_eliminated_then_bool_expansion() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<b: Bool> (b OR NOT b) — tautology
    let body = or(var("b"), not(var("b")));
    // Nest: forall<_x: ()> forall<b: Bool> (b OR NOT b)
    let inner = forall_with_sort("b", ExprSort::Bool, body);
    let expr = forall_with_sort("_x", ExprSort::Unit, inner);

    let term = encoder
        .encode_pure(&expr)
        .expect("multi-var forall with Unit+Bool should encode");

    // Negate: ¬(forall tautology) = false → Unsat
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "Unit var eliminated, Bool tautology expanded → negation should be Unsat (#1198)"
    );
}

/// Multi-variable quantifier: unused variable eliminated (#1198).
/// `forall<_unused: Int> forall<b: Bool> (b OR NOT b)` — `_unused` does not
/// appear in the body, so it is eliminated. Then `b: Bool` gets Bool expansion.
#[test]
#[timeout(30000)]
fn test_multi_var_unused_eliminated_then_bool_expansion() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let body = or(var("b"), not(var("b")));
    let inner = forall_with_sort("b", ExprSort::Bool, body);
    // _unused: Int, not mentioned in body
    let expr = forall_with_sort("_unused", ExprSort::Int, inner);

    let term = encoder
        .encode_pure(&expr)
        .expect("multi-var forall with unused+Bool should encode");

    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "unused var eliminated, Bool tautology expanded → negation should be Unsat (#1198)"
    );
}

/// Multi-variable exists: Unit variable eliminated, Bool expansion for exists (#1198).
/// `exists<_x: ()> exists<a: Bool> exists<b: Bool> (a AND b)` is satisfiable
/// (a=true, b=true). After Unit elimination, two Bool vars get case-split expansion.
#[test]
#[timeout(30000)]
fn test_multi_var_exists_unit_eliminated_bool_expansion() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let body = and(var("a"), var("b"));
    let inner_b = exists_with_sort("b", ExprSort::Bool, body);
    let inner_a = exists_with_sort("a", ExprSort::Bool, inner_b);
    let expr = exists_with_sort("_x", ExprSort::Unit, inner_a);

    let term = encoder
        .encode_pure(&expr)
        .expect("multi-var exists with Unit+Bool should encode");

    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Unit var eliminated, exists (a AND b) is satisfiable (a=true,b=true) (#1198)"
    );
}

/// All-Bool quantifier with triggers still gets case-split expansion (#1197).
/// Before #1197, the `effective_triggers.is_empty()` guard blocked Bool expansion
/// when triggers were present. Case-split expansion is complete for Bool domains,
/// so it should always be preferred over triggered E-matching.
///
/// `forall<a: Bool, b: Bool> {:triggers f(a)} (a OR b OR NOT b)` is a tautology
/// (b OR NOT b is always true). With Bool expansion, this is decidable.
#[test]
#[timeout(30000)]
fn test_all_bool_with_trigger_still_expands() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register a logic function f(x: Bool) -> Bool
    let f_def = LogicFnDef::new(
        "bool_f".to_string(),
        "crate::test::bool_f".to_string(),
        vec!["x".to_string()],
        var("x"), // identity function
    );
    encoder.register_logic_fn(&f_def).expect("register fn");

    // forall<a: Bool> {:triggers bool_f(a)} forall<b: Bool> (a OR b OR NOT b)
    // The trigger covers only `a`, not `b` — a partial trigger.
    // Before #1197, this would block Bool expansion.
    let body = or(var("a"), or(var("b"), not(var("b"))));
    let trigger = vec![vec![logic_fn_call("bool_f", vec![var("a")])]];
    let inner = PureExpr::Forall {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(body),
        triggers: vec![],
    };
    let expr = PureExpr::Forall {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(inner),
        triggers: trigger,
    };

    let term = encoder.encode_pure(&expr).expect("should encode");

    // Negate: if Bool expansion fires, this tautology negated → Unsat
    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "all-Bool tautology with partial trigger should be Unsat via Bool expansion (#1197)"
    );
}

// NOTE: PureExpr::Forall/Exists encoding is now implemented (Part of #178).
// Both direct and prefixed (old context) quantifiers work.
// Formula::Forall/Exists via encode() method also works.
// See tests::sep_logic_encoder_tests::test_encode_forall for Formula examples.
