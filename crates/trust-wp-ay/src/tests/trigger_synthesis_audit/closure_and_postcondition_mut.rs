// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure spec and postcondition_mut interaction tests.
//!
//! Tests eager instantiation for postcondition_mut, Fn→FnMut hierarchy gaps,
//! closure body encoding blocked by #985, postcondition_mut traversal through
//! quantifier boundaries, and user quantifier + axiom trigger interaction.
//!
//! Re: #970 (closure spec), #985 (closure encoding), #1018 (trigger synthesis)

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::logic::LogicFnDef;

use super::super::helpers::{
    and, binop, exists, forall, gt, int, logic_fn_call, method_call, not, var,
};
use crate::{AYEncoder, BinOp, PureExpr};

/// Eager instantiation for existential postcondition only fires for
/// `postcondition_mut` method calls, NOT for `postcondition_once` or
/// `postcondition`. This documents the gap at verify/mod.rs:335 where
/// `body_has_postcondition_mut_method_call` only matches "postcondition_mut".
///
/// Uses the encoder-level API (not verify_function) to isolate the eager
/// instantiation path from the full verification pipeline.
///
/// Re: #970 (closure spec), #1018 (trigger synthesis)
#[test]
#[timeout(30000)]
fn eager_instantiation_skips_postcondition_once_body() {
    use crate::verify::assert_eager_negated_existential_instantiations;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Ground precondition: f.postcondition_once(args, res)
    let ground_pre = method_call(
        var("f"),
        "postcondition_once",
        vec![var("args"), var("res")],
    );
    let pre_term = encoder
        .encode_pure(&ground_pre)
        .expect("encode precondition");
    encoder.assert_term(pre_term);

    // Existential postcondition: exists<st> f.postcondition_once(args, st, res)
    let post = exists(
        "st",
        method_call(
            var("f"),
            "postcondition_once",
            vec![var("args"), var("st"), var("res")],
        ),
    );

    // Eager instantiation should NOT fire because it only checks for postcondition_mut.
    let requires = vec![ground_pre.clone()];
    let ensures = vec![post];
    let result =
        assert_eager_negated_existential_instantiations(&mut encoder, &ensures, &requires, &[]);
    result.unwrap_or_else(|err| panic!("should not error: {err:?}"));

    // If eager instantiation had fired, it would assert NOT body[witness],
    // which combined with the ground precondition would produce Unsat.
    // Since it DOESN'T fire for postcondition_once, the solver stays Sat.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "eager instantiation should NOT fire for postcondition_once body — \
         gap: body_has_postcondition_mut_method_call only matches 'postcondition_mut'"
    );
}

/// Missing Fn→FnMut hierarchy axiom: `postcondition` and `postcondition_mut`
/// are unrelated uninterpreted symbols — no axiom connects them.
///
/// The axiom system has `fn_mut_once_law` connecting FnMut→FnOnce, but
/// no `fn_fn_mut_law` connecting Fn→FnMut.
///
/// Uses encoder-level API to demonstrate that asserting one method's
/// output cannot derive the other's.
///
/// Re: #970 (closure spec), gap identified in P1 audit
#[test]
#[timeout(30000)]
fn fn_hierarchy_axiom_gap_fn_to_fnmut() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Assert f.postcondition(args, res) as ground truth (Fn trait)
    let fn_post = method_call(var("f"), "postcondition", vec![var("args"), var("res")]);
    let fn_term = encoder
        .encode_pure(&fn_post)
        .expect("encode fn postcondition");
    encoder.assert_term(fn_term);

    // Assert NOT f.postcondition_mut(args, st, res) — negating FnMut postcondition
    let neg_fnmut_expr = not(method_call(
        var("f"),
        "postcondition_mut",
        vec![var("args"), var("st"), var("res")],
    ));
    let neg_fnmut_term = encoder
        .encode_pure(&neg_fnmut_expr)
        .expect("encode NOT fnmut postcondition");
    encoder.assert_term(neg_fnmut_term);

    // If Fn→FnMut axiom existed, this would be Unsat (contradiction).
    // Without it, postcondition and postcondition_mut are independent symbols,
    // so both can hold simultaneously → Sat.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "postcondition and NOT postcondition_mut should be consistent — \
         no Fn→FnMut hierarchy axiom exists to bridge them"
    );
}

// =============================================================================
// Trigger synthesis with closure captures (mixed bound + free variables)
// =============================================================================

/// Trigger synthesis with mixed bound + free (captured) variables in closure body.
///
/// Pattern: `forall<i> (|x| f(captured_var, i) > 0)` — closure body references
/// both quantifier-bound `i` and free `captured_var`. Trigger synthesis would
/// find `f(captured_var, i)` covering `i`, but encoding fails because
/// `PureExpr::Closure` returns `Unsupported` (#985).
///
/// This documents the gap: trigger synthesis can find valid candidates inside
/// closure bodies, but the encoder blocks at the Closure node level. When #985
/// is resolved, update this test to verify successful encoding + solver behavior.
///
/// Re: #1018 (trigger synthesis), #970 (closure specs), #985 (closure encoding)
#[test]
#[timeout(30000)]
fn trigger_synthesis_closure_body_mixed_bound_and_free_vars_blocked_by_985() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f2".to_string(),
        "crate::audit::test_f2".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i> |x| f2(captured_var, i) > 0
    let closure_body = gt(
        logic_fn_call("test_f2", vec![var("captured_var"), var("i")]),
        int(0),
    );
    let closure = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let expr = forall("i", closure);

    // Closures in logic context now encode conservatively (#985).
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "closure in forall body should encode conservatively (#985): {result:?}"
    );
}

/// Trigger synthesis when closure param shadows a free variable but NOT
/// the quantifier-bound variable.
///
/// Pattern: `forall<i> |captured_var| f2(captured_var, i) > 0`
/// The closure rebinds `captured_var` as a param, while `i` is bound by forall.
/// Closures in logic context now encode conservatively (#985): parameterized
/// closures become fresh unconstrained Bool constants, so the forall body
/// is a vacuous predicate. This prevents hard errors while tracking the
/// approximation via UnsupportedConstructSkip.
///
/// Re: #1018 (trigger synthesis), #985 (closure encoding)
#[test]
#[timeout(30000)]
fn trigger_synthesis_closure_param_shadows_free_not_bound_blocked_by_985() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f2".to_string(),
        "crate::audit::test_f2".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<i> |captured_var| f2(captured_var, i) > 0
    let closure_body = gt(
        logic_fn_call("test_f2", vec![var("captured_var"), var("i")]),
        int(0),
    );
    let closure = PureExpr::Closure {
        params: vec![("captured_var".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let expr = forall("i", closure);

    // Closures in logic context now encode conservatively (#985).
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "closure with shadowing param in forall should encode conservatively (#985): {result:?}"
    );
}

// =============================================================================
// body_has_any_postcondition_mut traversal through quantifier boundaries
// =============================================================================

/// `body_has_any_postcondition_mut` descends through Forall/Exists boundaries.
///
/// This documents the behavior at axioms.rs:598-599: when checking whether
/// an expression contains `postcondition_mut`, the function does NOT stop at
/// nested quantifier boundaries. An `exists<j>` wrapping a `postcondition_mut`
/// call will still return `true`, even if `j` is unrelated to the mut chain.
///
/// This is correct for its current use case (deciding whether to try
/// Skolemization at all), but could cause unnecessary Skolemization of
/// intermediate existentials whose bound variables are unrelated to the
/// postcondition_mut chain.
///
/// Re: #970 (closure spec), audit finding from P1-400
#[test]
#[timeout(30000)]
fn body_has_any_postcondition_mut_traverses_quantifier_boundaries() {
    use crate::encoder::AYEncoder;

    // Base case: postcondition_mut is found
    let base = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("args"), var("st"), var("res")],
    );
    assert!(
        AYEncoder::body_has_any_postcondition_mut(&base),
        "direct postcondition_mut should be found"
    );

    // Nested under exists: still found (traverses through Exists boundary)
    let nested_exists = exists("j", and(var("j"), base.clone()));
    assert!(
        AYEncoder::body_has_any_postcondition_mut(&nested_exists),
        "postcondition_mut under Exists should be found (traverses boundary)"
    );

    // Nested under forall: still found (traverses through Forall boundary)
    let nested_forall = forall("k", base.clone());
    assert!(
        AYEncoder::body_has_any_postcondition_mut(&nested_forall),
        "postcondition_mut under Forall should be found (traverses boundary)"
    );

    // Nested under exists-forall-exists chain: still found
    let deep_nesting = exists("a", forall("b", exists("c", base.clone())));
    assert!(
        AYEncoder::body_has_any_postcondition_mut(&deep_nesting),
        "postcondition_mut under exists-forall-exists chain should be found"
    );

    // postcondition (not postcondition_mut) is NOT found
    let post_only = method_call(var("f"), "postcondition", vec![var("args"), var("res")]);
    assert!(
        !AYEncoder::body_has_any_postcondition_mut(&post_only),
        "postcondition (not _mut) should NOT be detected"
    );

    // postcondition_once is NOT found
    let post_once = method_call(
        var("f"),
        "postcondition_once",
        vec![var("args"), var("res")],
    );
    assert!(
        !AYEncoder::body_has_any_postcondition_mut(&post_once),
        "postcondition_once should NOT be detected"
    );
}

// =============================================================================
// User quantifier + axiom trigger interaction on same closure spec symbol
// =============================================================================

/// User quantifier with postcondition_mut trigger coexists with fn_mut_once axiom.
///
/// When a user writes `forall<res> f.postcondition_mut(args, st, res) ==> P(res)`,
/// trigger synthesis picks `postcondition_mut(f, args, st, res)` as the trigger.
/// The fn_mut_once axiom also triggers on `postcondition_mut(...)`. Both axioms
/// share the same E-matching symbol. This test verifies they don't cause spurious
/// unsatisfiability through interaction.
///
/// Re: #1018 (trigger synthesis), audit finding from P1-400
#[test]
#[timeout(30000)]
fn user_quantifier_and_axiom_triggers_on_same_postcondition_mut_symbol() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Ground precondition: f.postcondition_mut(args, st1, res1)
    let ground_pre = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("args"), var("st1"), var("res1")],
    );
    let pre_term = encoder
        .encode_pure(&ground_pre)
        .expect("encode ground postcondition_mut");
    encoder.assert_term(pre_term);

    // User quantifier: forall<res> (f.postcondition_mut(args, st1, res) ==> res > 0)
    // Trigger synthesis should pick postcondition_mut(f, args, st1, res).
    let user_body = binop(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("args"), var("st1"), var("res")],
        ),
        BinOp::Implies,
        gt(var("res"), int(0)),
    );
    let user_quant = forall("res", user_body);
    let user_term = encoder
        .encode_pure(&user_quant)
        .expect("encode user quantifier with postcondition_mut trigger");
    encoder.assert_term(user_term);

    // The ground precondition f.postcondition_mut(args, st1, res1) should trigger
    // the user quantifier instantiation (with res := res1), giving res1 > 0.
    // The formula is: postcondition_mut(f, args, st1, res1) AND
    //                 forall<res> (postcondition_mut(f, args, st1, res) ==> res > 0)
    // This is consistent (Sat) — just forces res1 > 0.
    let result = encoder.check_sat();
    assert_ne!(
        result,
        SolveResult::unsat(),
        "user quantifier + ground postcondition_mut should be consistent (Sat), got {:?}",
        result
    );
}

/// Verify that dual-triggered quantifier instantiation (user + axiom) on
/// postcondition_mut does not produce spurious contradiction when the ground
/// call satisfies the user constraint.
///
/// Asserts: ground call + user quantifier constraint + explicit satisfaction
/// of the constraint → should be Sat (no spurious Unsat from trigger interaction).
///
/// Re: #1018 (trigger synthesis)
#[test]
#[timeout(30000)]
fn dual_trigger_instantiation_user_and_axiom_no_spurious_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Ground: f.postcondition_mut(args, st1, res1)
    let ground = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("args"), var("st1"), var("res1")],
    );
    let g_term = encoder.encode_pure(&ground).expect("encode ground");
    encoder.assert_term(g_term);

    // Ground: res1 > 0 (satisfies the user constraint)
    let res1_positive = gt(var("res1"), int(0));
    let rp_term = encoder
        .encode_pure(&res1_positive)
        .expect("encode res1 > 0");
    encoder.assert_term(rp_term);

    // User: forall<res> (postcondition_mut(f, args, st1, res) ==> res > 0)
    let user_body = binop(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("args"), var("st1"), var("res")],
        ),
        BinOp::Implies,
        gt(var("res"), int(0)),
    );
    let user_quant = forall("res", user_body);
    let uq_term = encoder
        .encode_pure(&user_quant)
        .expect("encode user quantifier");
    encoder.assert_term(uq_term);

    // Also assert the fn_mut_once relationship via a second quantifier
    // on the same symbol: forall<st> (postcondition_mut(f, args, st, res1) ==> st > 0)
    // This simulates an axiom-like quantifier sharing the trigger symbol.
    let axiom_body = binop(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("args"), var("st"), var("res1")],
        ),
        BinOp::Implies,
        gt(var("st"), int(0)),
    );
    let axiom_quant = forall("st", axiom_body);
    let aq_term = encoder
        .encode_pure(&axiom_quant)
        .expect("encode axiom-like quantifier");
    encoder.assert_term(aq_term);

    // All constraints are satisfiable together (e.g., res1=1, st1=1).
    // Trigger interactions should NOT produce spurious Unsat.
    let result = encoder.check_sat();
    assert_ne!(
        result,
        SolveResult::unsat(),
        "dual-trigger instantiation should not produce spurious Unsat, got {:?}",
        result
    );
}
