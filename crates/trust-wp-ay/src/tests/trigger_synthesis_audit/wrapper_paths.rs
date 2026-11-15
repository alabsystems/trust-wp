// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `old`, `deref`, `view`, `final`, `let_assume`, `let_obligation`, `match`,
//! and method-call wrapper traversal tests for trigger synthesis.
//!
//! Re: #1018 (trigger synthesis), #1122 (Old variable collapse),
//! #1142 (Deref/Final-wrapped trigger candidates), #1649 (Old wrapper preservation)

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::logic::LogicFnDef;

use super::{
    super::helpers::{
        binop, exists, forall, forall_with_sort, ge, gt, int, le, logic_fn_call, method_call, not,
        old, var,
    },
    fixtures::{assert_synthesized_triggers, synthesized_trigger},
};
use crate::{AYEncoder, BinOp, PureExpr};

// =============================================================================
// Old wrapper traversal (#1122)
// =============================================================================

/// Trigger synthesis through `Old` wrapper: `forall<i> old(test_f(i)) > 0`.
///
/// The `collect_trigger_candidates` recurses through `Old` (line 1481-1487).
/// test_f(i) inside Old should be found as a trigger candidate.
///
/// Regression test for #1122: Old(Var(v)) for quantifier-bound v must
/// collapse to the bound variable, not create a free `old_v` variable.
///
/// The fix adds quantifier-bound variable detection to the Var handler,
/// so `old_` prefix is omitted when the variable is quantifier-bound.
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_old_wrapper_no_var_leak() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i> old(test_f(i)) > 0
    let old_call = PureExpr::Old(Arc::new(logic_fn_call("test_f", vec![var("i")])));
    let expr = forall("i", gt(old_call, int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through Old wrapper should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![PureExpr::Old(Arc::new(logic_fn_call(
                "test_f",
                vec![var("i")],
            )))]],
        )],
    );

    // After #1122 fix: no `old_i` free variable should leak.
    // The quantifier-bound `i` inside Old() collapses to the bound variable.
    assert!(
        !encoder.var_names().contains(&"old_i".to_string()),
        "Old prefix must NOT create disconnected free variable old_i: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // With the fix, the quantifier binds correctly and the formula should
    // be Sat (forall<i> test_f(i) > 0 is satisfiable when test_f returns i+1
    // and i+1 > 0 is not universally true, so ay returns Sat/Unknown).
    assert!(
        result != SolveResult::unsat(),
        "formula should not be Unsat after Old prefix fix, got {:?}",
        result
    );
}

/// Regression test for #1122: Old(Var(v)) for a FREE variable must still
/// produce `old_v` (the fix only collapses quantifier-bound variables).
#[test]
#[timeout(30000)]
fn old_prefix_preserved_for_free_variables() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // old(x) where x is a free variable — should create old_x
    let expr = PureExpr::Old(Arc::new(var("x")));
    let _term = encoder
        .encode_pure(&expr)
        .expect("old(free_var) should encode");

    assert!(
        encoder.var_names().contains(&"old_x".to_string()),
        "Old prefix must be preserved for free variables: {:?}",
        encoder.var_names()
    );
}

/// Regression test for #1122: Old(Var(v)) inside a quantifier where v is
/// the quantifier-bound variable must collapse to the bound variable.
#[test]
#[timeout(30000)]
fn old_prefix_collapses_for_quantifier_bound_var() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i> old(i) > 0 — old(i) should use the bound `i`, not create `old_i`
    let expr = forall("i", gt(PureExpr::Old(Arc::new(var("i"))), int(0)));
    let _term = encoder
        .encode_pure(&expr)
        .expect("old(bound_var) should encode");

    assert!(
        !encoder.var_names().contains(&"old_i".to_string()),
        "Old(Var(bound)) must collapse — no old_i should exist: {:?}",
        encoder.var_names()
    );
}

// =============================================================================
// ITE, Let, and Match wrapper traversal
// =============================================================================

/// Trigger synthesis through `Ite` branches: function calls inside
/// if-then-else should be found as trigger candidates.
///
/// `forall<i> if i > 0 then test_f(i) > 0 else test_f(i) < 10`
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_ite_branches() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i> if (i > 0) then (test_f(i) > 0) else (test_f(i) < 10)
    let cond = gt(var("i"), int(0));
    let then_br = gt(logic_fn_call("test_f", vec![var("i")]), int(0));
    let else_br = binop(logic_fn_call("test_f", vec![var("i")]), BinOp::Lt, int(10));
    let body = PureExpr::Ite(Arc::new(cond), Arc::new(then_br), Arc::new(else_br));
    let expr = forall("i", body);
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through Ite should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "bound var should not leak: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "forall<i> ite(i>0, test_f(i)>0, test_f(i)<10) should be satisfiable, got {:?}",
        result
    );
}

/// Trigger synthesis through `Let` binding value:
/// `forall<i> let x = test_f(i) in x > 0`.
///
/// The function call test_f(i) is in the let value, which is traversed
/// by collect_trigger_candidates (line 1506).
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_let_value() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i> let x = test_f(i) in x > 0
    let let_expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(logic_fn_call("test_f", vec![var("i")])),
        body: Arc::new(gt(var("x"), int(0))),
    };
    let expr = forall("i", let_expr);
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through Let value should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty() || !encoder.var_names().contains(&"i".to_string()),
        "bound var i should not leak: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "forall<i> let x = test_f(i) in x > 0 should be satisfiable, got {:?}",
        result
    );
}

/// Trigger synthesis through `Match` arm body:
/// `forall<i> match opt { _ => test_f(i) > 0 }`.
///
/// The function call test_f(i) is inside a match arm body, traversed by
/// collect_trigger_candidates (line 1497-1504) with arm-binding shadowing.
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_match_arm() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i> match opt { _ => test_f(i) > 0 }
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(var("opt")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: gt(logic_fn_call("test_f", vec![var("i")]), int(0)),
        }],
    };
    let expr = forall("i", match_expr);
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through match arm should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        !encoder.var_names().contains(&"i".to_string()),
        "bound var i should not leak: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "forall<i> match wildcard arm should be satisfiable, got {:?}",
        result
    );
}

// =============================================================================
// Deref, View, Final wrapper traversal (#1142)
// =============================================================================

/// Trigger synthesis through Deref wrapper: `forall<i> *seq.index_logic(i) >= 0`.
///
/// The method call `seq.index_logic(i)` is inside a Deref wrapper. After #1142
/// fix, trigger synthesis preserves the Deref wrapper on the candidate, so the
/// synthesized trigger is `Deref(seq.index_logic(i))` — matching the body's
/// encoding which pushes Deref into the receiver.
///
/// Re: #1142 (Deref/Final-wrapped trigger candidates)
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_deref_wrapper_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i> *(seq.index_logic(i)) >= 0
    let derefed = PureExpr::Deref(Arc::new(method_call(
        var("seq"),
        "index_logic",
        vec![var("i")],
    )));
    let expr = forall("i", ge(derefed, int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through Deref wrapper should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![PureExpr::Deref(Arc::new(method_call(
                var("seq"),
                "index_logic",
                vec![var("i")],
            )))]],
        )],
    );
    // Bound variable should not leak
    assert!(
        !encoder.var_names().contains(&"i".to_string()),
        "bound variable `i` should not leak through Deref: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // forall<i> *(seq.index_logic(i)) >= 0 — Sat or Unknown (model-dependent)
    assert!(
        result != SolveResult::unsat(),
        "Deref-wrapped trigger formula should not be Unsat: {:?}",
        result
    );
}

/// Trigger synthesis through View wrapper: `forall<i> view(seq).index_logic(i) >= 0`.
///
/// The View wrapper around the receiver should not block trigger candidate
/// collection from the outer MethodCall node.
///
/// Re: #1142 (wrapper-based trigger candidates)
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_view_receiver_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i> view(seq).index_logic(i) >= 0
    let view_receiver = PureExpr::View(Arc::new(var("seq")));
    let expr = forall(
        "i",
        ge(
            method_call(view_receiver, "index_logic", vec![var("i")]),
            int(0),
        ),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis with View receiver should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![method_call(
                PureExpr::View(Arc::new(var("seq"))),
                "index_logic",
                vec![var("i")],
            )]],
        )],
    );
    assert!(
        !encoder.var_names().contains(&"i".to_string()),
        "bound variable `i` should not leak with View receiver: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "View-receiver trigger formula should not be Unsat: {:?}",
        result
    );
}

// =============================================================================
// LetAssume and LetObligation wrapper traversal (#1089)
// =============================================================================

/// Trigger synthesis through LetAssume: trigger candidates should be found
/// in both the assumption and the continuation body.
///
/// `forall<i> assume test_f(i) > 0; test_g(i) > 0`
///
/// Both test_f(i) and test_g(i) are valid candidates (both cover i).
/// The synthesis should pick one (test_f preferred at shallower depth if equal).
///
/// Re: #1089 (untested LetAssume edge case)
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_let_assume_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    let g_def = LogicFnDef::new(
        "test_g".to_string(),
        "crate::audit::test_g".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(2)),
    );
    encoder.register_logic_fn(&f_def).expect("register f");
    encoder.register_logic_fn(&g_def).expect("register g");

    // forall<i> assume test_f(i) > 0; test_g(i) > 0
    let assume_body = PureExpr::LetAssume {
        assumption: Arc::new(gt(logic_fn_call("test_f", vec![var("i")]), int(0))),
        body: Arc::new(gt(logic_fn_call("test_g", vec![var("i")]), int(0))),
    };
    let expr = forall("i", assume_body);
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through LetAssume should encode");
    // Both test_f(i) and test_g(i) fully cover i, so alternative trigger
    // patterns are emitted for each. test_f(i) is preferred (better score)
    // and test_g(i) is a secondary alternative.
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![
                vec![logic_fn_call("test_f", vec![var("i")])],
                vec![logic_fn_call("test_g", vec![var("i")])],
            ],
        )],
    );
    assert!(
        !encoder.var_names().contains(&"i".to_string()),
        "bound variable `i` should not leak through LetAssume: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // forall<i> (assume f(i)>0; g(i)>0) — Sat when both hold
    assert!(
        result != SolveResult::unsat(),
        "LetAssume trigger formula should not be Unsat: {:?}",
        result
    );
}

/// Trigger synthesis through LetObligation: candidates found in both
/// the obligation and the continuation body.
///
/// `forall<i> obligation test_f(i) > 0; test_f(i) + 1 > 0`
///
/// Re: #1089 (untested LetObligation edge case)
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_let_obligation_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder.register_logic_fn(&f_def).expect("register f");

    // forall<i> obligation test_f(i) > 0; test_f(i) + 1 > 0
    let obligation_body = PureExpr::LetObligation {
        obligation: Arc::new(gt(logic_fn_call("test_f", vec![var("i")]), int(0))),
        body: Arc::new(gt(
            binop(logic_fn_call("test_f", vec![var("i")]), BinOp::Add, int(1)),
            int(0),
        )),
    };
    let expr = forall("i", obligation_body);
    let term = encoder
        .encode_pure(&expr)
        .expect("trigger synthesis through LetObligation should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        !encoder.var_names().contains(&"i".to_string()),
        "bound variable `i` should not leak through LetObligation: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "LetObligation trigger formula should not be Unsat: {:?}",
        result
    );
}

// =============================================================================
// Method call and existential trigger traversal
// =============================================================================

/// Method call trigger synthesis works for existential quantifiers.
#[test]
#[timeout(30000)]
fn triggerless_exists_with_method_call_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // exists<i: Int> seq.index_logic(i) >= 0
    let expr = exists(
        "i",
        ge(
            method_call(var("seq"), "index_logic", vec![var("i")]),
            int(0),
        ),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("triggerless exists with method call should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![method_call(var("seq"), "index_logic", vec![var("i")])]],
        )],
    );
    // `seq` is a free variable (not a quantifier-bound var), so it SHOULD
    // appear in var_names. Only `i` should be bound (and thus absent).
    let names = encoder.var_names();
    assert!(
        !names.contains(&"i".to_string()),
        "bound variable `i` should not leak as free: {:?}",
        names
    );
    // Assert and check sat: exists<i> seq.index_logic(i) >= 0 is satisfiable
    // when index_logic returns a non-negative value for some i.
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "exists<i> seq.index_logic(i) >= 0 should be satisfiable, got {:?}",
        result
    );
}

/// Trigger synthesis through `Final` wrapper: `forall<i> final(test_f(i)) > 0`.
///
/// After #1142 fix, `collect_trigger_candidates` preserves the `Final` wrapper
/// on the candidate, so the trigger is `Final(test_f(i))` — not the unwrapped
/// `test_f(i)`. This ensures ay E-matching fires correctly.
///
/// Re: #1018 — edge case gap: `Final` wrapper had no dedicated test, unlike
/// `Old`, `Deref`, and `View` which all have dedicated tests.
#[test]
#[timeout(30000)]
fn trigger_synthesis_through_final_wrapper_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i: Int> final(test_f(i)) > 0: an unannotated written binder's
    // final value is refused (D-127), a value binder's is the binder.
    let expr = forall_with_sort(
        "i",
        trust_wp_core::formula::ExprSort::Int,
        gt(
            PureExpr::Final(Arc::new(logic_fn_call("test_f", vec![var("i")]))),
            int(0),
        ),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("triggerless forall with Final wrapper should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![PureExpr::Final(Arc::new(logic_fn_call(
                "test_f",
                vec![var("i")],
            )))]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "Final-wrapped bound var should not leak: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "forall<i> final(test_f(i)) > 0 should be satisfiable, got {:?}",
        result
    );
}

// =============================================================================
// Old wrapper preservation for instantiation (#1649)
// =============================================================================

/// Trigger synthesis for `Old(MethodCall)` should preserve the `Old` wrapper
/// in the trigger candidate, analogous to how `Deref(MethodCall)` preserves
/// the `Deref` wrapper (#1142).
///
/// `collect_trigger_candidates` treats `Old(inner)` as transparent (always
/// recurses, line 496 of trigger.rs) while `Deref/Final/View` wrappers are
/// preserved when they wrap MethodCall/LogicFnCall. This asymmetry is NOT a
/// bug because the #1122 variable-collapse mechanism (pure_encoding.rs:118-136)
/// ensures `Old(Var(i))` for quantifier-bound `i` collapses to `i`, making
/// the trigger and body encode to the same ay term regardless of wrapping.
///
/// This test verifies that `Old(LogicFnCall)` quantifiers actually instantiate
/// on ground terms — not just that they encode. The formula is ONLY UNSAT
/// if the quantifier triggers fire correctly.
///
/// Re: #1649 (strengthened from tautological SAT check in P1 530)
#[test]
#[timeout(30000)]
fn old_wrapping_logic_fn_call_quantifier_instantiates() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic fn: test_f(x) = x + 1
    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // Assert: forall<i> old(test_f(i)) > 0
    // With defining axiom test_f(x) = x+1, old(test_f(i)) collapses to
    // test_f(i) = i+1 for bound i (#1122 collapse). The quantifier states
    // that for all i, i+1 > 0.
    let old_body = gt(old(logic_fn_call("test_f", vec![var("i")])), int(0));
    let old_expr = forall("i", old_body);
    let old_term = encoder
        .encode_pure(&old_expr)
        .expect("Old(LogicFnCall) quantifier should encode");
    encoder.assert_term(old_term);

    // No free variable leak from Old wrapper (#1122)
    assert!(
        !encoder.var_names().contains(&"old_i".to_string()),
        "Old(LogicFnCall) quantifier should not leak old_i: {:?}",
        encoder.var_names()
    );

    // Assert ground contradicting fact: test_f(5) <= 0
    // Since test_f(5) = 6, this contradicts the forall.
    // ONLY UNSAT if the quantifier instantiates on test_f(5).
    let ground_neg = not(gt(logic_fn_call("test_f", vec![int(5)]), int(0)));
    let ground_term = encoder
        .encode_pure(&ground_neg)
        .expect("ground negation should encode");
    encoder.assert_term(ground_term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "Old(LogicFnCall) quantifier must instantiate on ground term and refute contradiction: got {result:?}"
    );
}

/// Verify that Old(LogicFnCall) and bare LogicFnCall encode to identical
/// ay terms inside a quantifier body. The #1122 variable-collapse mechanism
/// ensures `Old(Var(i))` for bound `i` resolves to the same bound variable
/// as `Var(i)`, so `old(f(i)) == f(i)` should be a tautology that the solver
/// can prove UNSAT when negated.
///
/// This is the inverse of the above test: instead of checking instantiation
/// against a ground term, we check that old() is semantically transparent
/// for quantifier-bound variables by asserting the NEGATION of the equality
/// and checking UNSAT.
///
/// Re: #1649 (strengthened from tautological SAT check in P1 530)
#[test]
#[timeout(30000)]
fn old_logic_fn_call_equals_bare_call_for_bound_vars() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register: test_f(x) = x + 1
    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // Assert: exists<i> old(test_f(i)) != test_f(i)
    // If Old is handled correctly (#1122), old(test_f(i)) and test_f(i) encode
    // identically for bound i. So there exists no i where they differ → UNSAT.
    let body = not(binop(
        old(logic_fn_call("test_f", vec![var("i")])),
        BinOp::Eq,
        logic_fn_call("test_f", vec![var("i")]),
    ));
    let quant = exists("i", body);
    let term = encoder
        .encode_pure(&quant)
        .expect("exists<i> old(f(i)) != f(i) should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "old(f(i)) must equal f(i) for quantifier-bound i (#1122 collapse): got {result:?}"
    );
}

/// Verify that Old(MethodCall) trigger synthesis preserves the Old wrapper,
/// producing a trigger that matches the body's encoding. Without the fix (#1649),
/// Old was grouped with UnOp — stripped before recursion — so the trigger for
/// `old(v.deep_model())` was `method_deep_model(v)` instead of
/// `method_deep_model(old_v)`, causing E-matching mismatch.
///
/// The test encodes `forall<i> old(v.get(i)) > 0` where `v` is free and `i`
/// is bound. The body encodes `method_get(old_v, qvar_i) > 0`, and the trigger
/// must be `method_get(old_v, qvar_i)` (not `method_get(v, qvar_i)`) for
/// instantiation to fire on the ground term `method_get(old_v, 5)`.
///
/// Re: #1649 — Old(MethodCall) trigger wrapper preservation
#[test]
#[timeout(30000)]
fn old_wrapping_method_call_trigger_preserves_wrapper() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Declare `old_v` as an Int variable to ensure old(Var("v")) resolves
    // to a concrete variable distinct from `v`.
    encoder
        .get_or_declare_var("old_v", ay_dpll::api::Sort::Int)
        .expect("declare old_v");

    // Assert: forall<i> old(v.get(i)) > 0
    // `v` is free, `i` is bound. The `get` method encodes as a UF:
    //   method_get_2_ii(old_v, qvar_i) > 0
    // Trigger should be method_get_2_ii(old_v, qvar_i) — not method_get_2_ii(v, qvar_i).
    let body = gt(old(method_call(var("v"), "get", vec![var("i")])), int(0));
    let quant = forall("i", body);
    let quant_term = encoder
        .encode_pure(&quant)
        .expect("forall<i> old(v.get(i)) > 0 should encode");
    encoder.assert_term(quant_term);

    // Assert ground contradicting fact: old(v.get(5)) <= 0
    // Encodes as: method_get_2_ii(old_v, 5) <= 0
    // If the trigger is correct (old_v, qvar_i), E-matching fires on this
    // ground term with i=5, yielding method_get_2_ii(old_v, 5) > 0 which
    // contradicts the assertion → Unsat.
    let ground_neg = le(old(method_call(var("v"), "get", vec![int(5)])), int(0));
    let ground_term = encoder
        .encode_pure(&ground_neg)
        .expect("old(v.get(5)) <= 0 should encode");
    encoder.assert_term(ground_term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "Old(MethodCall) trigger must preserve Old wrapper for E-matching (#1649): got {result:?}"
    );
}
