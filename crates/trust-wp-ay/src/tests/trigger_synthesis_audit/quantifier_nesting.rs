// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Nested exists/forall coverage, greedy set-cover behavior, alternation,
//! shadowing, and outer-var trigger recovery tests.
//!
//! Re: #1018 (trigger synthesis), #1118 (nested quantifier descent),
//! #1143 (greedy set-cover), #1245 (capture avoidance)

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::logic::LogicFnDef;

use super::{
    super::helpers::{and, binop, exists, forall, gt, int, logic_fn_call, method_call, var},
    fixtures::{assert_synthesized_triggers, synthesized_trigger},
};
use crate::{AYEncoder, BinOp, PureExpr};

/// Triggerless existential with logic fn should encode (trigger synthesis
/// fires for exists quantifiers, not just forall).
#[test]
#[timeout(30000)]
fn triggerless_exists_with_logic_fn_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function f: Int -> Int
    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::audit::test_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // exists<i: Int> test_f(i) > 0
    // No user triggers — synthesis should pick {:pattern test_f(i)}
    let expr = exists("i", gt(logic_fn_call("test_f", vec![var("i")]), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("triggerless exists with logic fn should encode with synthesized trigger");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "bound variable should not leak as free: {:?}",
        encoder.var_names()
    );
    // Assert the encoded term and check solver interaction:
    // test_f(x) = x + 1, so exists<i> (i + 1 > 0) is satisfiable (e.g. i = 0).
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "exists<i> test_f(i) > 0 should be satisfiable, got {:?}",
        result
    );
}

/// Triggerless nested exists quantifiers should encode with synthesized triggers.
#[test]
#[timeout(30000)]
fn triggerless_nested_exists_with_logic_fn_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function g: (Int, Int) -> Int
    let g_def = LogicFnDef::new(
        "test_g".to_string(),
        "crate::audit::test_g".to_string(),
        vec!["a".to_string(), "b".to_string()],
        binop(var("a"), BinOp::Add, var("b")),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn");

    // exists<i> exists<j> test_g(i, j) > 0
    let inner = exists(
        "j",
        gt(logic_fn_call("test_g", vec![var("i"), var("j")]), int(0)),
    );
    let expr = exists("i", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("triggerless nested exists should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i", "j"],
            vec![vec![logic_fn_call("test_g", vec![var("i"), var("j")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "nested exists bound vars should not leak: {:?}",
        encoder.var_names()
    );
    // test_g(a, b) = a + b, so exists<i,j> (i + j > 0) is satisfiable (e.g. i=1, j=0).
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "exists<i,j> test_g(i,j) > 0 should be satisfiable, got {:?}",
        result
    );
}

/// Mixed forall/exists nesting: trigger synthesis should only collect
/// variables from the same quantifier kind.
#[test]
#[timeout(30000)]
fn mixed_forall_exists_trigger_synthesis_encodes() {
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

    // forall<i> exists<j> test_f(i) > j
    // Trigger synthesis (#1118) descends into the exists<j> body and
    // finds test_f(i) as a trigger for the outer forall (it references outer
    // var `i` and the inner var `j` is shadowed).
    let inner = exists("j", gt(logic_fn_call("test_f", vec![var("i")]), var("j")));
    let expr = forall("i", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed forall/exists should encode");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "mixed forall/exists bound vars should not leak: {:?}",
        encoder.var_names()
    );
    // forall<i> exists<j> (i + 1 > j) is satisfiable (for any i, pick j = 0 when i >= 0).
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "forall<i> exists<j> test_f(i) > j should be satisfiable, got {:?}",
        result
    );
}

/// Triggerless forall with nested quantifier uses only outer-var candidates.
///
/// Trigger synthesis (#1118) descends into nested quantifier bodies but
/// shadows inner vars, so only candidates referencing outer vars are collected.
/// Here `test_g(j)` only references inner `j`, so only `test_f(i)` is the
/// outer trigger.
#[test]
#[timeout(30000)]
fn triggerless_forall_with_nested_forall_uses_outer_trigger_only() {
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
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn f");
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn g");

    // forall<i> (test_f(i) > 0 AND forall<j> test_g(j) > 0)
    // Trigger synthesis for the outer forall should find test_f(i),
    // NOT test_g(j) which is in the inner forall's body.
    let inner_forall = forall("j", gt(logic_fn_call("test_g", vec![var("j")]), int(0)));
    let body = and(
        gt(logic_fn_call("test_f", vec![var("i")]), int(0)),
        inner_forall,
    );
    let expr = forall("i", body);
    let term = encoder
        .encode_pure(&expr)
        .expect("forall with nested forall should encode using outer triggers only");
    assert_synthesized_triggers(
        &encoder,
        &[
            synthesized_trigger(&["j"], vec![vec![logic_fn_call("test_g", vec![var("j")])]]),
            synthesized_trigger(&["i"], vec![vec![logic_fn_call("test_f", vec![var("i")])]]),
        ],
    );
    assert!(
        encoder.var_names().is_empty(),
        "nested forall bound vars should not leak: {:?}",
        encoder.var_names()
    );
    // forall<i> (i+1 > 0 AND forall<j> j+2 > 0) is not universally true
    // (e.g. i = -2 makes i+1 = -1 <= 0), so asserting it and checking sat
    // should not return Unsat (the formula constrains but does not contradict).
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // With E-matching, the solver may return Unknown for quantified formulas,
    // but it should never return Unsat for this satisfiable formula.
    assert!(
        result != SolveResult::unsat(),
        "nested forall tautology-like formula should not be unsat, got {:?}",
        result
    );
}

/// Three-variable quantifier where no single candidate and no pair covers all
/// three variables — trigger synthesis should fall back to the best single
/// candidate rather than panicking or returning empty.
///
/// `forall<i, j, k> test_f(i) > 0 AND test_g(j) > 0 AND k > 0`
///
/// test_f(i) covers {i}, test_g(j) covers {j}, no candidate covers {k}.
/// The pair (test_f(i), test_g(j)) covers {i, j} but not {k}.
/// Synthesis should return the best partial trigger (test_f(i) or test_g(j)).
#[test]
#[timeout(30000)]
fn three_var_partial_coverage_fallback() {
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
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn f");
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn g");

    // forall<i> forall<j> forall<k> test_f(i) > 0 AND test_g(j) > 0 AND k > 0
    // No candidate covers k (it only appears in arithmetic), so full coverage
    // is impossible. Synthesis should return partial trigger.
    let body = and(
        and(
            gt(logic_fn_call("test_f", vec![var("i")]), int(0)),
            gt(logic_fn_call("test_g", vec![var("j")]), int(0)),
        ),
        gt(var("k"), int(0)),
    );
    let inner = forall("k", body);
    let mid = forall("j", inner);
    let expr = forall("i", mid);
    let term = encoder
        .encode_pure(&expr)
        .expect("three-var partial coverage should encode with best-effort trigger");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i", "j", "k"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "three-var forall bound vars should not leak: {:?}",
        encoder.var_names()
    );
    // Asserting the formula is genuinely UNSAT: it requires `k > 0` (and
    // `test_f(i) = i + 1 > 0`) to hold for ALL integers, which is false
    // (k = -1, i = -1). Unsat is the RIGHT verdict (z3 agrees); pinning
    // `!= Unsat` would enshrine single-round E-matching's failure to refute
    // the universal. Sat would be unsound; Unknown is acceptable
    // incompleteness.
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::Sat,
        "three-var partial coverage formula is UNSAT (forall k. k > 0 is false); \
         Sat would be unsound, got {:?}",
        result
    );
}

/// Greedy set-cover for three variables must improve the solver result over a
/// cloned partial user trigger on the same quantifier body. (#1143)
///
/// Triggerless form:
/// - synthesis should emit the triple multi-pattern {test_f(i), test_g(j), test_h(k)}
/// - the asserted ground facts should make the quantified formula contradictory
/// - solver result should therefore be `Unsat`
///
/// Cloned partial-trigger form:
/// - all three nested quantifiers carry the same user trigger {:pattern test_f(i)}
/// - collapse still yields one 3-variable quantifier, but only `i` is covered
/// - older ay builds lacked enough E-matching guidance for `j` and `k`, while
///   current ay may prove the contradiction anyway
#[test]
#[timeout(30000)]
fn three_var_greedy_set_cover_beats_partial_user_trigger() {
    fn register_three_unary_logic_fns(encoder: &mut AYEncoder) {
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
        let h_def = LogicFnDef::new(
            "test_h".to_string(),
            "crate::audit::test_h".to_string(),
            vec!["x".to_string()],
            binop(var("x"), BinOp::Add, int(3)),
        );
        encoder
            .register_logic_fn(&f_def)
            .expect("register logic fn f");
        encoder
            .register_logic_fn(&g_def)
            .expect("register logic fn g");
        encoder
            .register_logic_fn(&h_def)
            .expect("register logic fn h");
    }

    fn assert_ground_contradiction(encoder: &mut AYEncoder) {
        for ground in [
            binop(logic_fn_call("test_f", vec![var("a")]), BinOp::Eq, int(-1)),
            binop(logic_fn_call("test_g", vec![var("b")]), BinOp::Eq, int(-2)),
            binop(logic_fn_call("test_h", vec![var("c")]), BinOp::Eq, int(-3)),
        ] {
            let term = encoder.encode_pure(&ground).expect("encode ground fact");
            encoder.assert_term(term);
        }
    }

    fn three_var_body() -> PureExpr {
        and(
            and(
                gt(logic_fn_call("test_f", vec![var("i")]), int(0)),
                gt(logic_fn_call("test_g", vec![var("j")]), int(0)),
            ),
            gt(logic_fn_call("test_h", vec![var("k")]), int(0)),
        )
    }

    let mut synthesized = AYEncoder::new_pure_with_quantifiers();
    register_three_unary_logic_fns(&mut synthesized);
    assert_ground_contradiction(&mut synthesized);

    let triggerless = forall("i", forall("j", forall("k", three_var_body())));
    let triggerless_term = synthesized
        .encode_pure(&triggerless)
        .expect("triggerless three-var quantifier should encode");
    let synthesized_diags = synthesized.synthesized_triggers();
    assert_eq!(
        synthesized_diags.len(),
        1,
        "expected one synthesized trigger diagnostic, got {synthesized_diags:#?}"
    );
    let diag = &synthesized_diags[0];
    assert_eq!(
        diag.vars,
        vec!["i".to_string(), "j".to_string(), "k".to_string()],
        "expected synthesized trigger over all three quantifier vars"
    );
    assert_eq!(
        diag.patterns.len(),
        1,
        "expected a single multi-pattern trigger, got {diag:#?}"
    );
    assert_eq!(
        diag.patterns[0].len(),
        3,
        "expected three trigger terms from greedy set-cover, got {diag:#?}"
    );
    let synthesized_names: Vec<&str> = diag.patterns[0]
        .iter()
        .filter_map(|expr| match expr {
            PureExpr::LogicFnCall { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        synthesized_names.contains(&"test_f")
            && synthesized_names.contains(&"test_g")
            && synthesized_names.contains(&"test_h"),
        "synthesized multi-pattern should include test_f/test_g/test_h, got {diag:#?}"
    );
    synthesized.assert_term(triggerless_term);
    assert_eq!(
        synthesized.check_sat(),
        SolveResult::unsat(),
        "greedy set-cover should find the three-term trigger and detect the contradiction"
    );

    let partial_trigger = vec![vec![logic_fn_call("test_f", vec![var("i")])]];
    let partial_quantifier = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        triggers: partial_trigger.clone(),
        body: Arc::new(PureExpr::Forall {
            var: "j".to_string(),
            var_sort: None,
            triggers: partial_trigger.clone(),
            body: Arc::new(PureExpr::Forall {
                var: "k".to_string(),
                var_sort: None,
                triggers: partial_trigger,
                body: Arc::new(three_var_body()),
            }),
        }),
    };

    let mut partial = AYEncoder::new_pure_with_quantifiers();
    register_three_unary_logic_fns(&mut partial);
    assert_ground_contradiction(&mut partial);
    let partial_term = partial
        .encode_pure(&partial_quantifier)
        .expect("partial-trigger three-var quantifier should encode");
    partial.assert_term(partial_term);
    let partial_result = partial.check_sat();
    assert!(
        !matches!(partial_result, SolveResult::Sat),
        "cloned partial trigger must not produce a model for the contradictory facts: {partial_result:?}"
    );
}

/// Exists-forall-exists alternation: trigger synthesis handles each
/// quantifier level independently, descending but shadowing inner vars.
///
/// `exists<i> (test_f(i) > 0 AND forall<j> exists<k> test_g(k) > j)`
///
/// The outer exists: descends into forall<j> (shadow j) then exists<k>
/// (shadow k). test_g(k) only references inner vars → not collected.
/// test_f(i) at top level references outer `i` → collected.
/// The forall: descends into exists<k> (shadow k). test_g(k) only
/// references `k` (shadowed) → not collected. No trigger for `j`.
/// The inner exists: test_g(k) references `k` → collected.
#[test]
#[timeout(30000)]
fn exists_forall_exists_alternation_trigger_synthesis() {
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
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn f");
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn g");

    // exists<i> (test_f(i) > 0 AND forall<j> exists<k> test_g(k) > j)
    let innermost = exists("k", gt(logic_fn_call("test_g", vec![var("k")]), var("j")));
    let middle = forall("j", innermost);
    let body = and(gt(logic_fn_call("test_f", vec![var("i")]), int(0)), middle);
    let expr = exists("i", body);
    let term = encoder
        .encode_pure(&expr)
        .expect("exists-forall-exists alternation should encode");
    assert_synthesized_triggers(
        &encoder,
        &[
            synthesized_trigger(&["k"], vec![vec![logic_fn_call("test_g", vec![var("k")])]]),
            synthesized_trigger(&["i"], vec![vec![logic_fn_call("test_f", vec![var("i")])]]),
        ],
    );
    assert!(
        encoder.var_names().is_empty()
            || !encoder.var_names().contains(&"i".to_string())
                && !encoder.var_names().contains(&"j".to_string())
                && !encoder.var_names().contains(&"k".to_string()),
        "quantifier-bound vars i/j/k should not leak as free: {:?}",
        encoder.var_names()
    );
    // exists<i> (i+1 > 0 AND forall<j> exists<k> k+2 > j) is satisfiable
    // (pick i=0: 1 > 0 true; for any j, pick k=j: k+2 > j true)
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "exists-forall-exists should be satisfiable, got {:?}",
        result
    );
}

/// Closure body containing a method call that references the quantifier-bound
/// variable. Under conservative closure handling (#985) the closure encodes as a
/// fresh constant and the quantifier body becomes Bool-sorted.
///
/// `exists<i> (|x| seq.index_logic(i) > x)`
#[test]
#[timeout(30000)]
fn triggerless_exists_with_closure_method_call_unsupported() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let closure_body = gt(
        method_call(var("seq"), "index_logic", vec![var("i")]),
        var("x"),
    );
    let closure_expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let expr = exists("i", closure_expr);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "closure in quantifier body should encode conservatively (#985): {result:?}"
    );
}

/// Forall-exists-forall alternation: each quantifier level synthesizes
/// its own triggers independently, descending but shadowing inner vars.
///
/// `forall<i> exists<j> forall<k> test_f(i) > k AND test_g(k) > j`
///
/// The outer forall's synthesis (#1118) descends through exists<j> (shadow j) and
/// forall<k> (shadow k) to find test_f(i) referencing outer `i`.
/// Inner forall finds test_g(k) for `k`.
#[test]
#[timeout(30000)]
fn forall_exists_forall_alternation_trigger_synthesis() {
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
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn f");
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn g");

    // forall<i> exists<j> forall<k> (test_f(i) > k AND test_g(k) > j)
    let body = and(
        gt(logic_fn_call("test_f", vec![var("i")]), var("k")),
        gt(logic_fn_call("test_g", vec![var("k")]), var("j")),
    );
    let inner = forall("k", body);
    let mid = exists("j", inner);
    let expr = forall("i", mid);
    let term = encoder
        .encode_pure(&expr)
        .expect("forall-exists-forall alternation should encode");
    assert_synthesized_triggers(
        &encoder,
        &[
            synthesized_trigger(&["k"], vec![vec![logic_fn_call("test_g", vec![var("k")])]]),
            synthesized_trigger(&["i"], vec![vec![logic_fn_call("test_f", vec![var("i")])]]),
        ],
    );
    assert!(
        encoder.var_names().is_empty()
            || !encoder.var_names().contains(&"i".to_string())
                && !encoder.var_names().contains(&"j".to_string())
                && !encoder.var_names().contains(&"k".to_string()),
        "quantifier-bound vars i/j/k should not leak as free: {:?}",
        encoder.var_names()
    );
    encoder.assert_term(term);
    let result = encoder.check_sat();
    // forall<i> exists<j> forall<k> (i+1 > k AND k+2 > j) is genuinely UNSAT:
    // the inner `forall<k>. i+1 > k` must hold for ALL integers k, but k = i+1
    // falsifies it for every i ("may hold for small k" is not "holds for all
    // k"). Unsat is the right verdict (z3 agrees), so `!= Unsat` must not be
    // pinned. Sat would be unsound; Unknown is acceptable incompleteness.
    assert!(
        result != SolveResult::Sat,
        "forall-exists-forall alternation is UNSAT (forall k. i+1 > k is false); \
         Sat would be unsound, got {:?}",
        result
    );
}

/// Cross-kind variable shadowing: `forall<i> exists<i> test_f(i) > 0`.
///
/// The inner exists rebinds `i`, shadowing the outer forall's `i`.
/// After encoding, the outer forall's binding must be properly restored
/// and bound variables must not leak.
#[test]
#[timeout(30000)]
fn cross_kind_var_shadowing_forall_exists_same_name() {
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

    // forall<i> exists<i> test_f(i) > 0
    // The inner exists shadows the outer forall's i. The test_f(i) references
    // the innermost binding (the exists-bound i).
    let inner = exists("i", gt(logic_fn_call("test_f", vec![var("i")]), int(0)));
    let expr = forall("i", inner);
    let term = encoder
        .encode_pure(&expr)
        .expect("cross-kind var shadowing should encode without panic");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_f", vec![var("i")])]],
        )],
    );
    assert!(
        encoder.var_names().is_empty(),
        "cross-kind shadowed vars should not leak: {:?}",
        encoder.var_names()
    );
    // forall<i> exists<i'> (i'+1 > 0) is satisfiable (for any outer i, pick inner i' = 0)
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "cross-kind shadowing formula should be satisfiable, got {:?}",
        result
    );
}

/// The outer quantifier is not trigger-starved when the valid candidate is
/// inside a nested quantifier body.
///
/// Pattern: `forall<i> exists<j> f(i) > j`
/// - `f(i)` references outer var `i` and lives inside `exists<j>` body.
/// - `collect_trigger_candidates` descends into nested quantifier bodies
///   (shadowing inner vars), so `f(i)` IS found. (#1118)
///
/// Re: #1018 (trigger boundary gap), #1118, #1245
#[test]
#[timeout(30000)]
fn trigger_found_inside_nested_quantifier_for_outer_var() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register f: Int -> Int, f(x) = x + 1
    let f_def = LogicFnDef::new(
        "test_starved_f".to_string(),
        "crate::audit::test_starved_f".to_string(),
        vec!["x".to_string()],
        binop(var("x"), BinOp::Add, int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register test_starved_f");

    // Ground fact: test_starved_f(42) = 43
    let ground = binop(
        logic_fn_call("test_starved_f", vec![int(42)]),
        BinOp::Eq,
        int(43),
    );
    let g = encoder.encode_pure(&ground).expect("encode ground");
    encoder.assert_term(g);

    // forall<i> exists<j> test_starved_f(i) > j
    // test_starved_f(i) is found inside exists<j> (#1118) because
    // it references outer var `i` (inner var `j` is shadowed).
    let body = exists(
        "j",
        gt(logic_fn_call("test_starved_f", vec![var("i")]), var("j")),
    );
    let q = forall("i", body);

    let q_term = encoder
        .encode_pure(&q)
        .expect("forall with nested exists should encode with synthesized trigger");
    assert_synthesized_triggers(
        &encoder,
        &[synthesized_trigger(
            &["i"],
            vec![vec![logic_fn_call("test_starved_f", vec![var("i")])]],
        )],
    );
    encoder.assert_term(q_term);

    // With the trigger for `i`, ay E-matching can instantiate the outer forall.
    // The formula is satisfiable (for any i, pick j = 0 when f(i) > 0).
    let result = encoder.check_sat();
    assert_ne!(
        result,
        SolveResult::unsat(),
        "forall<i> exists<j> f(i) > j is satisfiable when f is total, got {:?}",
        result
    );
}
