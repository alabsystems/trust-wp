// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bool expansion, De Morgan transform, and slow-path verification tests.
//!
//! Tests trigger synthesis behavior through Bool-sorted quantifier expansion,
//! De Morgan transform output (negated existentials → forall with NOT body),
//! and slow-path OR combination for postcondition verification.
//!
//! Re: #1018 (trigger synthesis), #970 (De Morgan transform), #1027 (Bool expansion),
//! #1134 (partial trigger + Bool expansion interaction)

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::logic::LogicFnDef;

use super::{
    super::helpers::{
        and, binop, exists, exists_with_sort, forall, forall_with_sort, gt, int, logic_fn_call,
        not, or, var,
    },
    fixtures::{assert_synthesized_triggers, synthesized_trigger},
};
use crate::{AYEncoder, BinOp, ExprSort, PureExpr};

#[path = "bool_expansion_and_demorgan/triggerless_quantifier_tests.rs"]
mod triggerless_quantifier_tests;

/// Degenerate case: triggerless quantifier with literal-only body.
/// `forall<i> true` — no function calls, no variable references.
/// Trigger synthesis should return empty, encoder should handle gracefully.
/// De Morgan + trigger synthesis interaction: negated consecutive existentials.
///
/// When `negate_existential_postcondition` rewrites
/// `exists<a> exists<b> g(a,b) > 0` to `forall<a> forall<b> NOT(g(a,b) > 0)`,
/// the encoder's trigger synthesis must find triggers through the NOT wrapper
/// in the De Morgan output. This tests the full encode_pure pipeline.
///
/// Re: #1018, #970 (De Morgan + trigger synthesis audit)
#[test]
#[timeout(30000)]
fn de_morgan_forall_with_not_body_trigger_synthesis() {
    use trust_wp_core::formula::UnOp;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let g_def = LogicFnDef::new(
        "test_g".to_string(),
        "crate::audit::test_g".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn g");

    // Simulate De Morgan output: forall<a> forall<b> NOT(test_g(a,b) > 0)
    // This is what negate_existential_postcondition produces for
    // exists<a> exists<b> test_g(a,b) > 0
    let negated_body = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(gt(
            logic_fn_call("test_g", vec![var("a"), var("b")]),
            int(0),
        )),
    );
    let inner = forall("b", negated_body);
    let expr = forall("a", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("De Morgan forall with NOT body should encode with synthesized triggers");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["a", "b"],
            vec![vec![logic_fn_call("test_g", vec![var("a"), var("b")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "bound variables should not leak: {:?}",
        encoder.var_names()
    );
    // forall<a,b> NOT(a+b > 0) is not universally true (e.g. a=0, b=0: NOT(0>0) = true,
    // but a=1, b=1: NOT(2>0) = false). So asserting it constrains but is not Unsat.
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "De Morgan forall with NOT body should not be Unsat, got {:?}",
        result
    );
}

/// De Morgan slow-path end-to-end: verify_function with Bool existential
/// postcondition. Exercises the slow-path negation pipeline:
/// 1. `negate_existential_postcondition` rewrites exists→forall
/// 2. Bool expansion (#1027) handles the rewritten forall
/// 3. verify_function combines with OR for single-postcondition case
///
/// Note: Bool-sorted quantifiers use case-split expansion, not trigger
/// synthesis. This test validates the De Morgan + Bool expansion path.
///
/// Re: #970, #1027 (De Morgan + Bool expansion integration)
#[test]
#[timeout(30000)]
fn de_morgan_slow_path_bool_expansion_verify_function() {
    use crate::{verify_function_with_modes, ExprSort, VerificationRequest, VerificationResult};

    // exists<a:Bool> (a == true) — satisfiable, trivially true via a=true
    let postcondition = super::super::helpers::exists_with_sort(
        "a",
        ExprSort::Bool,
        binop(var("a"), BinOp::Eq, PureExpr::Bool(true)),
    );
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[postcondition]).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "existential postcondition with equality should verify: got {result:?}"
    );
}

/// Multi-variable quantifier with one unused variable: the unused-var
/// elimination (#1065) only fires for single-variable quantifiers
/// (`vars_collected.len() == 1`). When nested quantifiers collapse into
/// multi-variable form, unused vars are not eliminated.
///
/// `forall<_x> forall<y> test_f(y) > 0`
///   _x is unused in the body, but nested collapse produces
///   vars_collected = [_x, y], so the `len() == 1` guard does not fire.
///
/// This documents a P3 completeness gap: the formula encodes correctly
/// but ay receives a quantifier over an extra unused variable.
///
/// Re: #1065 (quantifier elimination)
#[test]
#[timeout(30000)]
fn multi_var_unused_elimination_gap_documents_behavior() {
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

    // forall<_x> forall<y> test_f(y) > 0
    // _x does not appear in the body. With single-var, it would be eliminated.
    // With the nested collapse (both triggerless same-kind), vars_collected = [_x, y].
    let inner = forall("y", gt(logic_fn_call("test_f", vec![var("y")]), int(0)));
    let expr = forall("_x", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("multi-var with unused should encode (gap: unused var not eliminated)");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["_x", "y"],
            vec![vec![logic_fn_call("test_f", vec![var("y")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "bound variables should not leak: {:?}",
        encoder.var_names()
    );
    // The formula is semantically equivalent to forall<y> test_f(y) > 0.
    // The extra _x variable is harmless — ay handles it correctly.
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "multi-var with unused formula should not be Unsat: {:?}",
        result
    );
}

/// Trigger synthesis for De Morgan output with conjunctive body containing
/// a nested existential: `forall<a> NOT(test_f(a) > 0 AND exists<b> g(b) > 0)`.
///
/// This is the De Morgan output for `exists<a> (test_f(a) > 0 AND exists<b> g(b) > 0)`
/// where the outer exists is negated but the inner exists (nested in BinOp)
/// is preserved inside the NOT wrapper (#1152).
///
/// Trigger synthesis should find `test_f(a)` through the NOT > BinOp path.
/// The inner `exists<b>` contributes no outer trigger because `test_g(b)`
/// only references inner `b`, not outer `a`.
///
/// Re: #1152, #1018 (trigger synthesis + De Morgan interaction)
#[test]
#[timeout(30000)]
fn trigger_synthesis_de_morgan_output_with_nested_exists_in_conjunction() {
    use trust_wp_core::formula::UnOp;

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

    // Simulate De Morgan output for:
    //   exists<a> (test_f(a) > 0 AND exists<b> test_g(b) > 0)
    // After negate_existential_postcondition:
    //   forall<a> NOT(test_f(a) > 0 AND exists<b> test_g(b) > 0)
    let inner_exists = exists("b", gt(logic_fn_call("test_g", vec![var("b")]), int(0)));
    let conjunction = and(
        gt(logic_fn_call("test_f", vec![var("a")]), int(0)),
        inner_exists,
    );
    let negated = PureExpr::UnOp(UnOp::Not, Arc::new(conjunction));
    let expr = forall("a", negated);

    let term = encoder
        .encode_pure(&expr)
        .expect("De Morgan output with nested exists in conjunction should encode");
    assert_synthesized_triggers(
        &encoder,
        &[
            synthesized_trigger(&["b"], vec![vec![logic_fn_call("test_g", vec![var("b")])]]),
            synthesized_trigger(&["a"], vec![vec![logic_fn_call("test_f", vec![var("a")])]]),
        ],
    );
    assert!(
        !encoder.var_names().contains(&"a".to_string()),
        "bound variable `a` should not leak: {:?}",
        encoder.var_names()
    );
    assert!(
        !encoder.var_names().contains(&"b".to_string()),
        "bound variable `b` should not leak: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // forall<a> NOT(a+1 > 0 AND exists<b> b+2 > 0) is satisfiable
    // (pick a=-2: a+1=-1 which is NOT > 0, so NOT(false AND ...) = NOT false = true)
    assert!(
        result != SolveResult::unsat(),
        "De Morgan nested exists conjunction should not be Unsat: {:?}",
        result
    );
}

/// Trigger synthesis for a quantifier whose body is a logic fn call.
///
/// This tests that trigger synthesis fires for `forall<i> test_p(i)` and
/// produces a quantifier encoding (not a panic or encoding error).
///
/// Note: the interaction between trigger synthesis (line 784) and Bool
/// expansion (line 877) means that if synthesis succeeds for a single
/// Bool-sorted variable, Bool expansion is bypassed. For Int-sorted
/// variables (as here), Bool expansion wouldn't fire anyway. The Bool
/// expansion bypass for Bool-sorted vars with logic fn calls in their body
/// is a documented edge case — see #1018 finding.
///
/// Re: #1018, #1027
#[test]
#[timeout(30000)]
fn triggerless_forall_with_logic_fn_predicate_body_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function p: Int -> Bool (predicate)
    let p_def = LogicFnDef::new(
        "test_p".to_string(),
        "crate::audit::test_p".to_string(),
        vec!["x".to_string()],
        // p(x) = x > 0
        binop(var("x"), BinOp::Gt, int(0)),
    );
    encoder
        .register_logic_fn(&p_def)
        .expect("register logic fn");

    // forall<i> test_p(i)
    // Trigger synthesis should find {:pattern test_p(i)} covering i.
    let expr = forall("i", logic_fn_call("test_p", vec![var("i")]));
    let term = encoder
        .encode_pure(&expr)
        .expect("triggerless forall with logic fn predicate body should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_p", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "bound var should not leak: {:?}",
        encoder.var_names()
    );
    // The emitted solver query is ONLY `forall<i> logic_test__p(i)` with
    // `logic_test__p` an uninterpreted Int -> Bool predicate: the registered
    // body `x > 0` is instantiated on demand via the ground pool, and this
    // test has no ground `test_p` application, so no defining instance is
    // asserted. That query is genuinely SATISFIABLE (p := λi. true; z3
    // agrees). The old pin `!= Sat` (with a comment reading the un-asserted
    // definition into the query) only held because the pre-2026-07-04 ay was
    // too incomplete to see the completion and returned Unknown; the
    // 2026-07-04 ay salvage's UF-completion certificate now correctly
    // returns Sat. Unsat is the verdict that would be unsound here.
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        !result.is_unsat(),
        "forall<i> test_p(i) with test_p uninterpreted in the emitted query is \
         satisfiable; Unsat would be unsound, got {:?}",
        result
    );
}

/// Verifies ay correctly solves a trivially satisfiable existential.
///
/// `exists<i> test_f(i) > 0` where `f(x) = x + 1` is trivially satisfiable
/// (witness: `i = 0`, `f(0) = 1 > 0`). ay now returns Sat after E-matching
/// improvements in the ay pin bump (previously returned Unknown).
///
/// Re: #1018
#[test]
#[timeout(30000)]
fn triggerless_exists_known_unknown_limitation() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        // f(x) = x + 1
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // exists<i: Int> test_f(i) > 0
    // Trivially satisfiable (i=0 gives f(0)=1>0). ay now returns Sat
    // after E-matching improvements in the ay pin bump.
    let expr = exists("i", gt(logic_fn_call("test_f", vec![var("i")]), int(0)));
    let term = encoder.encode_pure(&expr).expect("should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // ay E-matching now handles triggerless existentials over Int domain.
    // Previously returned Unknown; fixed in ay pin bump.
    assert_eq!(
        result,
        SolveResult::Sat,
        "exists<i> test_f(i) > 0 should be Sat (i=0 gives f(0)=1>0). Got: {result:?}"
    );
}

// ── Partial trigger + Bool expansion interaction tests (#1134 audit) ──

/// When trigger synthesis finds a partial trigger covering only one of two
/// Bool-sorted variables, the non-empty trigger causes the Bool expansion
/// guard (`effective_triggers.is_empty()`) to be false. The quantifier then
/// goes to ay as a regular triggered quantifier over Bool sorts, which ay
/// cannot decide (returns Unknown instead of decidable Sat/Unsat).
///
/// This test documents the current behavior. If Bool expansion is improved
/// to fire even with partial triggers over Bool-sorted vars, this test's
/// expected result should change from Unknown to Sat.
#[test]
#[timeout(30000)]
fn partial_trigger_blocks_bool_expansion_for_multi_var_bool_quantifier() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function: audit_p(x: Int) -> Int
    let f_def = LogicFnDef::new(
        "audit_p".to_string(),
        "crate::audit::audit_p".to_string(),
        vec!["x".to_string()],
        // p(x) = x + 1
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // forall<b: Bool> forall<i: Int> (audit_p(i) > 0 OR b OR NOT b)
    //
    // This is a tautology: `b OR NOT b` is always true, so the entire
    // body is always true regardless of b and i.
    //
    // `audit_p(i)` provides a trigger covering `i` but not `b`.
    // Trigger synthesis returns this partial trigger, making
    // `effective_triggers` non-empty, which blocks Bool expansion
    // for variable `b`. The quantifier goes to ay as a regular
    // triggered quantifier mixing Bool and Int.
    //
    // Note: collapsing only collapses same-kind quantifiers WITHOUT
    // triggers. Since inner forall<i> is also triggerless, both
    // variables get collapsed into one multi-var quantifier.
    let body = or(
        gt(logic_fn_call("audit_p", vec![var("i")]), int(0)),
        or(var("b"), not(var("b"))),
    );
    let expr = forall_with_sort("b", ExprSort::Bool, forall("i", body));
    let term = encoder.encode_pure(&expr).expect("should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["b", "i"],
            vec![vec![logic_fn_call("audit_p", vec![var("i")])]],
        )],
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();

    // The partial trigger covering only `i` blocks Bool expansion for `b`.
    // ay gets a triggered quantifier over both `b` (Bool) and `i` (Int).
    // E-matching fires on audit_p instances, but `b` is still universally
    // quantified over Bool which ay can't enumerate.
    //
    // Soundness guard: must NEVER be Unsat (this is a tautology).
    assert_ne!(
        result,
        SolveResult::unsat(),
        "forall<b:Bool, i:Int> (audit_p(i) > 0 OR b OR NOT b) is a tautology — \
         Unsat would indicate a soundness bug"
    );
    // Behavioral pin: mixed-sort Bool expansion now works — the solver
    // recognizes `b OR NOT b` as a tautology in the Bool component even
    // when Int variables are present, returning Sat correctly.
    // (Previously returned Unknown before per-variable Bool expansion landed.)
    assert_eq!(
        result,
        SolveResult::Sat,
        "mixed-sort (Bool+Int) quantifier: Bool expansion now handles \
         per-variable expansion, so b OR NOT b resolves to Sat"
    );
}

/// Verify that nested Bool quantifiers WITHOUT any trigger candidates
/// correctly use multi-variable Bool expansion (cartesian product).
/// This is the happy path that #1134 fixed.
#[test]
#[timeout(30000)]
fn triggerless_multi_var_bool_uses_cartesian_expansion() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<a: Bool> forall<b: Bool> ((a AND b) OR (NOT a) OR (NOT b))
    // This is a tautology: for all Bool a,b, at least one disjunct is true.
    // No function calls → no trigger candidates → Bool expansion fires.
    let body = or(or(and(var("a"), var("b")), not(var("a"))), not(var("b")));
    let expr = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "forall<a,b:Bool> ((a AND b) OR NOT a OR NOT b) is a tautology — \
         must be Sat via Bool expansion (#1134)"
    );
}

/// Multi-variable exists with Bool expansion: `exists<a,b:Bool> (a AND b)`
/// is satisfiable with a=true, b=true. Without function calls, no triggers
/// are synthesized, and Bool expansion fires correctly.
#[test]
#[timeout(30000)]
fn triggerless_multi_var_bool_exists_expansion() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let body = and(var("a"), var("b"));
    let expr = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "exists<a,b:Bool> (a AND b) is satisfiable — must be Sat via Bool expansion"
    );
}

/// When one variable is Unit-sorted and another is Bool-sorted, and there are
/// no trigger candidates (so synthesis returns empty), the variables are NOT
/// collapsed into a multi-variable quantifier. Instead, the outer `_x: ()`
/// quantifier is handled alone (Unit elimination fires, eliminating it), and
/// the inner `b: Bool` is encoded separately (Bool expansion fires).
///
/// This verifies that nested Unit+Bool quantifiers without triggers are
/// optimized correctly — each level gets its own optimization independently.
///
/// Note: The multi-variable bypass described in #1198 only manifests when
/// trigger synthesis SUCCEEDS (non-empty), forcing the re-collapse path.
/// Without triggers, the triggerless path returns empty and does NOT re-collapse.
#[test]
#[timeout(30000)]
fn nested_unit_bool_without_triggers_optimizes_each_level_independently() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<_x: ()> forall<b: Bool> (b OR NOT b)
    // This is a tautology: `b OR NOT b` is always true, _x is unused.
    // Without trigger candidates, synthesis returns empty →
    // _x is Unit-eliminated (single-var), then b gets Bool expansion.
    let body = or(var("b"), not(var("b")));
    let expr = forall_with_sort(
        "_x",
        ExprSort::Unit,
        forall_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();

    // Both optimizations fire independently → tautology is decidable → Sat.
    assert_eq!(
        result,
        SolveResult::Sat,
        "forall<_x:(), b:Bool> (b OR NOT b) is a tautology — \
         Unit elimination + Bool expansion should make this decidable"
    );
}

/// Closure parameter that shadows a quantifier variable must not leak
/// trigger coverage to the outer quantifier through the encoding pipeline.
///
/// `forall<i> |i| f(i) > 0` — the closure param `i` shadows the forall
/// `i`. If trigger synthesis incorrectly treats the inner `f(i)` as
/// covering the outer forall's `i`, the quantifier would get a trigger
/// referencing a variable it doesn't bind.
///
/// After #985 conservative handling, the closure encodes as a fresh
/// constant. This test verifies the pipeline doesn't crash and that
/// trigger synthesis correctly avoids the shadowed variable.
///
/// Re: #1018 trigger synthesis edge case audit.
#[test]
#[timeout(30000)]
fn closure_param_shadowing_quantifier_var_reaches_encoder() {
    use trust_wp_core::formula::PureExpr;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i> |i| f(i) > 0
    let closure = PureExpr::Closure {
        params: vec![("i".to_string(), None)],
        body: Arc::new(gt(logic_fn_call("f", vec![var("i")]), int(0))),
    };
    let expr = forall("i", closure);

    // Closures in logic context now encode conservatively (#985).
    // The closure becomes a fresh constant; the forall body is Bool.
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "closure in forall should encode conservatively (#985), got: {:?}",
        result
    );
}

/// Triple nested same-kind exists with a single function call covering
/// all three variables, tested through the encode pipeline.
///
/// `exists<i> exists<j> exists<k> g(i, j, k) > 0`
/// After `collect_nested_quantifier_vars` gathers [i, j, k] and trigger
/// synthesis finds `g(i, j, k)`, the three nested quantifiers should be
/// collapsed into a single triggered existential.
///
/// The solver should return Sat (the existential is satisfiable when g is
/// unconstrained), confirming that the trigger is correctly attached and
/// ay's E-matching can use it.
///
/// Re: #1018 trigger synthesis edge case audit.
#[test]
#[timeout(30000)]
fn triple_nested_exists_with_full_coverage_trigger() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register a logic function g(i, j, k) with trivial body
    let g_def = LogicFnDef::new(
        "test_g3".to_string(),
        "crate::audit::test_g3".to_string(),
        vec!["i".to_string(), "j".to_string(), "k".to_string()],
        binop(binop(var("i"), BinOp::Add, var("j")), BinOp::Add, var("k")),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn");

    // exists<i> exists<j> exists<k> test_g3(i, j, k) > 0
    let body = gt(
        logic_fn_call("test_g3", vec![var("i"), var("j"), var("k")]),
        int(0),
    );
    let expr = exists("i", exists("j", exists("k", body)));

    let term = encoder.encode_pure(&expr).expect("should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i", "j", "k"],
            vec![vec![logic_fn_call(
                "test_g3",
                vec![var("i"), var("j"), var("k")],
            )]],
        )],
    );
    encoder.assert_term(term);

    // An unconstrained existential with g > 0 is satisfiable.
    // The trigger synthesis should find test_g3(i,j,k) covering all 3 vars.
    // Int-sorted existentials return Unknown (ay E-matching cannot enumerate
    // integers), so we verify not-Unsat rather than Sat. (#1087)
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "exists<i,j,k> test_g3(i,j,k) > 0 should not be Unsat, got {:?}",
        result
    );
}

/// When an inner quantifier has user-provided triggers, trigger synthesis
/// should NOT collapse it with the outer quantifier.
///
/// `exists<a> exists<b: triggers=[g(b)]> f(a, b) > 0`
/// `collect_nested_quantifier_vars` stops at `b` because it has non-empty
/// triggers. Only `a` gets synthesis. The inner `exists<b>` keeps its user
/// trigger.
///
/// Re: #1018 trigger synthesis edge case audit.
#[test]
#[timeout(30000)]
fn user_triggered_inner_quantifier_not_collapsed() {
    use trust_wp_core::formula::PureExpr;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function f(a, b)
    let f_def = LogicFnDef::new(
        "test_f2".to_string(),
        "crate::audit::test_f2".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn f");

    // Register logic function g(b)
    let g_def = LogicFnDef::new(
        "test_g2".to_string(),
        "crate::audit::test_g2".to_string(),
        vec!["b".to_string()],
        binop(var("b"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn g");

    // exists<a> exists<b: triggers=[test_g2(b)]> test_f2(a, b) > 0
    let body = gt(logic_fn_call("test_f2", vec![var("a"), var("b")]), int(0));
    let inner_exists = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: None,
        body: Arc::new(body),
        triggers: vec![vec![logic_fn_call("test_g2", vec![var("b")])]],
    };
    let expr = exists("a", inner_exists);

    // After #1118, the outer `a` gets synthesis — test_f2(a, b) is found
    // inside the inner exists body (references outer `a`, inner `b` is shadowed).
    // Inner `b` keeps its user trigger.
    let term = encoder.encode_pure(&expr).expect("should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["a"],
            vec![vec![logic_fn_call("test_f2", vec![var("a"), var("b")])]],
        )],
    );
    encoder.assert_term(term);

    // Int-sorted existentials return Unknown (ay E-matching limitation, #1087).
    // Verify the formula encodes without error and doesn't return Unsat.
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "exists<a> exists<b: triggers=[test_g2(b)]> test_f2(a,b) > 0 should not be Unsat, got {:?}",
        result
    );
}

/// Semantic test: De Morgan transform output with trigger synthesis detects
/// contradiction through the NOT wrapper.
///
/// Simulates the verification pipeline for negated existential postconditions:
/// 1. `negate_existential_postcondition` rewrites `NOT(exists<a> P(a))`
///    to `forall<a> NOT P(a)` at PureExpr level.
/// 2. Trigger synthesis finds candidates through the NOT wrapper (UnOp
///    recursion at logic_fn.rs:1587).
/// 3. ay E-matching uses the synthesized trigger to instantiate and find
///    the contradiction.
///
/// This proves the full De Morgan + trigger synthesis + E-matching pipeline
/// is end-to-end functional for postcondition negation.
///
/// Re: #1018 (trigger synthesis), #970 (De Morgan transform)
#[test]
#[timeout(30000)]
fn de_morgan_trigger_synthesis_enables_contradiction_detection() {
    use trust_wp_core::formula::UnOp;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function: test_h(x) = x + 1
    let h_def = LogicFnDef::new(
        "test_h".to_string(),
        "crate::audit::test_h".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder.register_logic_fn(&h_def).expect("register test_h");

    // Ground fact: test_h(a) = 100 (a specific ground term for E-matching)
    let ground = binop(logic_fn_call("test_h", vec![var("a")]), BinOp::Eq, int(100));
    let ground_term = encoder.encode_pure(&ground).expect("encode ground fact");
    encoder.assert_term(ground_term);

    // De Morgan output: forall<i> NOT(test_h(i) > 0)
    // This is the PureExpr-level rewrite of NOT(exists<i> test_h(i) > 0).
    // Trigger synthesis must find {:pattern test_h(i)} through the NOT wrapper.
    let de_morgan_forall = forall(
        "i",
        PureExpr::UnOp(
            UnOp::Not,
            Arc::new(gt(logic_fn_call("test_h", vec![var("i")]), int(0))),
        ),
    );
    let q_term = encoder
        .encode_pure(&de_morgan_forall)
        .expect("De Morgan forall with NOT body should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_h", vec![var("i")])]],
        )],
    );
    encoder.assert_term(q_term);

    // With synthesized trigger {:pattern test_h(i)}, ay instantiates at i=a:
    //   NOT(test_h(a) > 0) = NOT(100 > 0) = NOT(true) = false
    // Combined with the forall assertion, this is a contradiction → UNSAT.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "De Morgan output with trigger synthesis through NOT wrapper \
         should detect contradiction when ground fact exists"
    );
}

/// Semantic test: De Morgan transform output for nested existentials
/// with trigger synthesis detects multi-variable contradiction.
///
/// Simulates: `NOT(exists<a> exists<b> test_g(a,b) > 0)` →
///            `forall<a> forall<b> NOT(test_g(a,b) > 0)`
///
/// Trigger synthesis collapses the nested foralls and finds
/// `{:pattern test_g(a,b)}` through the NOT wrapper. With a ground
/// fact `test_g(x,y) = 42`, E-matching detects the contradiction.
///
/// Re: #1018 (trigger synthesis), #970 (De Morgan nested existentials)
#[test]
#[timeout(30000)]
fn de_morgan_nested_exists_trigger_synthesis_enables_contradiction_detection() {
    use trust_wp_core::formula::UnOp;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register: test_g2_sem(a, b) = a + b
    let g_def = LogicFnDef::new(
        "test_g2_sem".to_string(),
        "crate::audit::test_g2_sem".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register test_g2_sem");

    // Ground fact: test_g2_sem(x, y) = 42
    let ground = binop(
        logic_fn_call("test_g2_sem", vec![var("x"), var("y")]),
        BinOp::Eq,
        int(42),
    );
    let ground_term = encoder.encode_pure(&ground).expect("encode ground fact");
    encoder.assert_term(ground_term);

    // De Morgan output: forall<a> forall<b> NOT(test_g2_sem(a,b) > 0)
    // From: NOT(exists<a> exists<b> test_g2_sem(a,b) > 0)
    let negated_body = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(gt(
            logic_fn_call("test_g2_sem", vec![var("a"), var("b")]),
            int(0),
        )),
    );
    let inner_forall = forall("b", negated_body);
    let outer_forall = forall("a", inner_forall);
    let q_term = encoder
        .encode_pure(&outer_forall)
        .expect("nested De Morgan forall should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["a", "b"],
            vec![vec![logic_fn_call("test_g2_sem", vec![var("a"), var("b")])]],
        )],
    );
    encoder.assert_term(q_term);

    // With synthesized trigger {:pattern test_g2_sem(a,b)}, ay instantiates
    // at a=x, b=y: NOT(42 > 0) = false → contradiction → UNSAT.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "nested De Morgan output with trigger synthesis through NOT wrapper \
         should detect multi-variable contradiction"
    );
}

/// De Morgan transform on existential with user-provided triggers preserves
/// triggers on the resulting forall AND trigger synthesis still fires for the
/// NOT-wrapped body.
///
/// Input: `NOT(exists<a> {:pattern test_h(a)} test_h(a) > 0)`
/// De Morgan: `forall<a> {:pattern test_h(a)} NOT(test_h(a) > 0)`
///
/// The forall already has triggers from the original exists, so trigger
/// synthesis should NOT re-synthesize. The preserved triggers must be
/// functional — ay E-matching uses `{:pattern test_h(a)}` to find
/// the contradiction with a ground fact.
///
/// Re: #1018 (trigger synthesis), #970 (De Morgan transform)
#[test]
#[timeout(30000)]
fn de_morgan_preserves_user_triggers_on_existential_semantic() {
    use trust_wp_core::formula::UnOp;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function: test_hpt(x) = x + 1
    let h_def = LogicFnDef::new(
        "test_hpt".to_string(),
        "crate::audit::test_hpt".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&h_def)
        .expect("register test_hpt");

    // Ground fact: test_hpt(a) = 100
    let ground = binop(
        logic_fn_call("test_hpt", vec![var("a")]),
        BinOp::Eq,
        int(100),
    );
    let ground_term = encoder.encode_pure(&ground).expect("encode ground fact");
    encoder.assert_term(ground_term);

    // De Morgan output with preserved triggers:
    // forall<i> {:pattern test_hpt(i)} NOT(test_hpt(i) > 0)
    // This simulates negate_existential_postcondition on:
    // exists<i> {:pattern test_hpt(i)} test_hpt(i) > 0
    let de_morgan_forall = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::UnOp(
            UnOp::Not,
            Arc::new(gt(logic_fn_call("test_hpt", vec![var("i")]), int(0))),
        )),
        triggers: vec![vec![logic_fn_call("test_hpt", vec![var("i")])]],
    };
    let q_term = encoder
        .encode_pure(&de_morgan_forall)
        .expect("De Morgan forall with preserved triggers should encode");
    assert_synthesized_triggers(&encoder, &[]);
    encoder.assert_term(q_term);

    // E-matching with {:pattern test_hpt(i)} should instantiate at i=a:
    // NOT(test_hpt(a) > 0) = NOT(100 > 0) = false → contradiction → UNSAT
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "De Morgan with preserved user triggers should detect contradiction via E-matching"
    );
}

/// De Morgan on nested existential where inner level has user triggers.
///
/// Input: `NOT(exists<a> exists<b> {:pattern test_g(b)} P(a,b))`
/// De Morgan: `forall<a> forall<b> {:pattern test_g(b)} NOT P(a,b)`
///
/// The trigger `{:pattern test_g(b)}` only covers `b`, not `a`. This tests
/// whether ay can still find the contradiction when only one variable has
/// E-matching coverage. The outer `a` is universally quantified — ay must
/// instantiate `b` via E-matching, then reason about `a` through the body.
///
/// Re: #1018 (trigger synthesis edge case), #1245 (trigger boundary)
#[test]
#[timeout(30000)]
fn de_morgan_nested_exists_inner_triggered_partial_coverage() {
    use trust_wp_core::formula::UnOp;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register: test_pci(a, b) = a + b (two-argument, both needed)
    let fn_def = LogicFnDef::new(
        "test_pci".to_string(),
        "crate::audit::test_pci".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&fn_def)
        .expect("register test_pci");

    // Register: test_trigger_b(b) = b (single-argument, for trigger)
    let trig_def = LogicFnDef::new(
        "test_trigger_b".to_string(),
        "crate::audit::test_trigger_b".to_string(),
        vec!["b".to_string()],
        var("b"),
    );
    encoder
        .register_logic_fn(&trig_def)
        .expect("register test_trigger_b");

    // Ground facts: test_pci(x, y) = 42, test_trigger_b(y) = y
    let ground1 = binop(
        logic_fn_call("test_pci", vec![var("x"), var("y")]),
        BinOp::Eq,
        int(42),
    );
    let ground2 = binop(
        logic_fn_call("test_trigger_b", vec![var("y")]),
        BinOp::Eq,
        var("y"),
    );
    let g1 = encoder.encode_pure(&ground1).expect("encode ground1");
    let g2 = encoder.encode_pure(&ground2).expect("encode ground2");
    encoder.assert_term(g1);
    encoder.assert_term(g2);

    // De Morgan output: forall<a> forall<b> {:pattern test_trigger_b(b)} NOT(test_pci(a,b) > 0)
    // The inner forall has a trigger for b; the outer has none for a.
    // With trigger synthesis disabled by the presence of user triggers,
    // we test whether the partial trigger coverage still leads to detection.
    let negated_body = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(gt(
            logic_fn_call("test_pci", vec![var("a"), var("b")]),
            int(0),
        )),
    );
    let inner_forall = PureExpr::Forall {
        var: "b".to_string(),
        var_sort: None,
        body: Arc::new(negated_body),
        triggers: vec![vec![logic_fn_call("test_trigger_b", vec![var("b")])]],
    };
    // Outer forall has no triggers — trigger synthesis should fire for `a`
    let outer_forall = forall("a", inner_forall);

    let q_term = encoder
        .encode_pure(&outer_forall)
        .expect("nested De Morgan with inner triggers should encode");
    // After #1118, trigger synthesis descends into the inner forall<b> body
    // (shadowing b) and finds test_pci(a, b) which references outer `a`.
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["a"],
            vec![vec![logic_fn_call("test_pci", vec![var("a"), var("b")])]],
        )],
    );
    encoder.assert_term(q_term);

    // With both triggers — test_trigger_b(b) for inner and test_pci(a,b)
    // for outer — ay E-matching can fully instantiate both quantifiers.
    // The formula forall<a,b> NOT(a+b > 0) combined with a+b=42>0 is
    // contradictory.
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::Sat,
        "De Morgan nested with inner-only triggers should not be satisfiable \
         (a+b=42 contradicts NOT(a+b>0)), got {:?}",
        result
    );
}

/// Slow path OR combination: verify that ORing the De Morgan rewritten form
/// with direct negation does not introduce false positives (spurious Verified).
///
/// Tests the specific pattern from encode_and_assert_negated_postconditions
/// line 284: `or(rewritten_neg, direct_neg)`.
///
/// Postcondition: `exists<a:Bool> NOT a` (i.e., there exists a false value)
/// This is TRUE (witnessed by a=false), so the function should VERIFY.
///
/// The slow path asserts:
///   OR(forall<a:Bool> NOT(NOT a), NOT(exists<a:Bool> NOT a))
/// = OR(forall<a:Bool> a, forall<a:Bool> a)  [by De Morgan on direct neg]
/// = forall<a:Bool> a  [idempotent OR]
///
/// This forall claims all bools are true — SAT (a=false is counterexample).
/// So the function should correctly detect this and return Verified (the
/// postcondition holds).
///
/// Re: #970 (slow path soundness), #1018 (trigger synthesis)
#[test]
#[timeout(30000)]
fn slow_path_or_combination_does_not_weaken_verification() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Postcondition: exists<a:Bool> NOT a  (true: witnessed by a=false)
    // Body result: true (any boolean value)
    let post = exists_with_sort("a", ExprSort::Bool, not(var("a")));
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[post]).return_expr(Some(&PureExpr::Bool(true))),
    )
    .expect("should not error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "exists<a:Bool> NOT a holds (witnessed by a=false), slow path OR must not weaken this, got {:?}",
        result
    );
}

/// Slow path OR: verify that a FALSE existential postcondition is correctly
/// detected as Failed even with the OR combination.
///
/// Postcondition: `exists<a:Bool> (a AND NOT a)` — unsatisfiable contradiction.
/// No witness exists, so the postcondition fails and the function should NOT verify.
///
/// The slow path asserts:
///   OR(forall<a:Bool> NOT(a AND NOT a), NOT(exists<a:Bool> (a AND NOT a)))
/// Both forms simplify to TRUE (the negation of an unsatisfiable formula is
/// a tautology). So the OR is TRUE, which means the negated conjunction is
/// SAT → verification FAILS. Correct behavior.
///
/// Re: #970 (slow path soundness), #1018 (trigger synthesis)
#[test]
#[timeout(30000)]
fn slow_path_or_combination_detects_unsatisfiable_existential() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Postcondition: exists<a:Bool> (a AND NOT a)  — contradiction, always false
    let post = exists_with_sort("a", ExprSort::Bool, and(var("a"), not(var("a"))));
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[post]).return_expr(Some(&PureExpr::Bool(true))),
    )
    .expect("should not error");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "exists<a:Bool> (a AND NOT a) is always false — slow path OR must detect failure, got {:?}",
        result
    );
}
