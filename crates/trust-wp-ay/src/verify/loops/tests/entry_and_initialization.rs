// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

fn assert_initialization_failed_result(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(_) => {}
        other => panic!("{context} should fail initialization; got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn loop_entry_may_execute_false_when_requires_implies_not_condition() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(false)),
    )];
    let loop_condition = PureExpr::Var("x".to_string(), None);

    let may_execute = loop_entry_may_execute(
        &requires,
        &HashMap::new(),
        Some(&loop_condition),
        &LoopEncoderConfig::default(),
    )
    .expect("loop entry satisfiability check should encode");

    assert!(!may_execute, "loop entry should be unreachable");
}

#[test]
#[timeout(30000)]
fn loop_entry_may_execute_treats_bare_condition_as_formula() {
    let loop_condition = PureExpr::Var("flag".to_string(), None);

    let may_execute = loop_entry_may_execute(
        &[],
        &HashMap::new(),
        Some(&loop_condition),
        &LoopEncoderConfig::default(),
    )
    .expect("bare Bool loop condition should encode as a formula");

    assert!(
        may_execute,
        "unconstrained Bool condition should be satisfiable"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_rejects_non_boolean_invariant() {
    let requires = vec![PureExpr::Bool(true)];
    let invariants = vec![PureExpr::Int(1)];

    let err = verify_initialization(
        &requires,
        &invariants,
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect_err("non-boolean invariant should return an encoding error");
    let msg = err.to_string();
    assert!(
        msg.contains("boolean"),
        "error should mention boolean requirement, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_treats_init_extra_facts_as_formulas() {
    let invariants = vec![PureExpr::Var("flag".to_string(), None)];
    let init_extra_facts = vec![PureExpr::Var("flag".to_string(), None)];

    let result = verify_initialization(
        &[],
        &invariants,
        &HashMap::new(),
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("Bool init extra facts should encode as formulas");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected Bool init extra facts to prove initialization, got {result:?}"
    );
}

/// Regression: Seq-typed pre-loop binding preserves its sort through the
/// driver -> ay boundary when using `NamedBindingValue::new(Some(Seq), ...)`.
///
/// Before #2053 Slice B, loop VC builders rebuilt the LHS variable as
/// `PureExpr::Var(name, None)` which defaulted to `Sort::Int`. Now
/// `binding.lhs_var(name)` carries the `ExprSort::Seq` annotation, so the
/// assignment equality `s == seq_empty()` declares `s` with Seq sort.
///
/// This test proves the Seq-sorted binding works: invariant `s.len() == 0`
/// is provable from `s == seq_empty()` only when `s` is declared as Seq.
#[test]
#[timeout(30000)]
fn verify_initialization_preserves_seq_sort_from_named_binding() {
    let seq_empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    // Pre-loop: s = seq_empty() with Seq sort annotation
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "s".to_string(),
        NamedBindingValue::new(Some(ExprSort::Seq), seq_empty),
    );

    // Invariant: s.len() == 0
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), Some(ExprSort::Seq))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );

    let result = verify_initialization(
        &[],
        &[invariant],
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("Seq-typed pre-loop binding should encode successfully");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "initialization should verify: s == seq_empty() ∧ s.len() == 0 when s has Seq sort; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_uses_assigned_vec_len_fact() {
    let door_open = PureExpr::Var("door_open".to_string(), Some(ExprSort::Seq));
    let call_result = PureExpr::Var("call_1".to_string(), Some(ExprSort::Seq));
    let view = |expr: PureExpr| PureExpr::View(Arc::new(expr));
    let len = |expr: PureExpr| PureExpr::MethodCall {
        receiver: Arc::new(expr),
        method: "len".to_string(),
        args: vec![],
    };

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "door_open".to_string(),
        NamedBindingValue::new(Some(ExprSort::Seq), call_result.clone()),
    );

    let init_extra_facts = vec![PureExpr::BinOp(
        Arc::new(len(view(call_result))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(100)),
    )];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(len(view(door_open))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(100)),
    )];

    let result = verify_initialization(
        &[],
        &invariants,
        &pre_loop_assignments,
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("assigned Vec length initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "door_open = call_1 and call_1@.len() == 100 should prove door_open@.len() == 100, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_empty_produced_range_forall_without_quantifier_solver() {
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let j = PureExpr::Var("j".to_string(), Some(ExprSort::Int));
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };
    let invariant = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(j.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(j.clone()),
                    BinOp::Lt,
                    Arc::new(produced_len.clone()),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(produced.clone()),
                    method: "index_logic".to_string(),
                    args: vec![j],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            )),
        )),
        triggers: vec![],
    };
    let init_extra_facts = vec![PureExpr::BinOp(
        Arc::new(produced_len),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];

    let result = verify_initialization(
        &[],
        &[invariant],
        &HashMap::new(),
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("empty produced forall initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty produced range should prove the forall initialization directly; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_empty_range_forall_through_assigned_len_fact() {
    let candidates = PureExpr::Var("candidates".to_string(), Some(ExprSort::Seq));
    let call_result = PureExpr::Var("call_1".to_string(), Some(ExprSort::Seq));
    let i = PureExpr::Var("i".to_string(), Some(ExprSort::Int));
    let view = |expr: PureExpr| PureExpr::View(Arc::new(expr));
    let len = |expr: PureExpr| PureExpr::MethodCall {
        receiver: Arc::new(expr),
        method: "len".to_string(),
        args: vec![],
    };

    let candidates_len = len(view(candidates.clone()));
    let invariant = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(i.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(i),
                    BinOp::Lt,
                    Arc::new(candidates_len),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::Bool(false)),
        )),
        triggers: vec![],
    };

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "candidates".to_string(),
        NamedBindingValue::new(Some(ExprSort::Seq), call_result.clone()),
    );
    let init_extra_facts = vec![PureExpr::BinOp(
        Arc::new(len(view(call_result))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];

    let result = verify_initialization(
        &[],
        &[invariant],
        &pre_loop_assignments,
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("assigned len-zero forall initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "candidates = call_1 and call_1@.len() == 0 should make the range forall vacuous; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_empty_range_forall_when_receiver_sort_annotations_differ() {
    let candidates_invariant = PureExpr::Var("candidates".to_string(), Some(ExprSort::Seq));
    let candidates_fact = PureExpr::Var("candidates".to_string(), None);
    let i = PureExpr::Var("i".to_string(), Some(ExprSort::Int));
    let view = |expr: PureExpr| PureExpr::View(Arc::new(expr));
    let len = |expr: PureExpr| PureExpr::MethodCall {
        receiver: Arc::new(expr),
        method: "len".to_string(),
        args: vec![],
    };

    let candidates_len = len(view(candidates_invariant));
    let invariant = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Le,
                    Arc::new(i.clone()),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(i),
                    BinOp::Lt,
                    Arc::new(candidates_len),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::Bool(false)),
        )),
        triggers: vec![],
    };
    let init_extra_facts = vec![PureExpr::BinOp(
        Arc::new(len(view(candidates_fact))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];

    let result = verify_initialization(
        &[],
        &[invariant],
        &HashMap::new(),
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("sort-annotated len-zero forall initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "same receiver name with differing sort annotations should make the range forall vacuous; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_empty_list_seg_from_equal_bounds_directly() {
    use trust_wp_core::logic::LogicFnDef;

    let i = var("i");
    let j = var("j");
    let s_i = method_call(var("s"), "index_logic", vec![i.clone()]);
    let s_j = method_call(var("s"), "index_logic", vec![j.clone()]);
    let list_seg_body = and(
        eq(
            var("first"),
            ite(
                eq(var("h"), var("l")),
                var("last"),
                method_call(var("s"), "index_logic", vec![var("l")]),
            ),
        ),
        and(
            forall(
                "i",
                implies(
                    and(le(var("l"), i.clone()), lt(i.clone(), var("h"))),
                    and(
                        method_call(var("self"), "nonnull_ptr", vec![s_i.clone()]),
                        eq(
                            method_call(var("self"), "index_logic", vec![s_i]),
                            ite(
                                eq(i.clone(), sub(var("h"), int(1))),
                                var("last"),
                                method_call(var("s"), "index_logic", vec![add(i, int(1))]),
                            ),
                        ),
                    ),
                ),
            ),
            forall(
                "i",
                forall(
                    "j",
                    implies(
                        and(
                            and(
                                and(le(var("l"), var("i")), lt(var("i"), var("h"))),
                                le(var("l"), j.clone()),
                            ),
                            and(lt(j.clone(), var("h")), ne(var("i"), j.clone())),
                        ),
                        ne(method_call(var("s"), "index_logic", vec![var("i")]), s_j),
                    ),
                ),
            ),
        ),
    );
    let list_seg_def = LogicFnDef::new(
        "list_seg".to_string(),
        "Memory::list_seg".to_string(),
        vec![
            "self".to_string(),
            "first".to_string(),
            "s".to_string(),
            "last".to_string(),
            "l".to_string(),
            "h".to_string(),
        ],
        list_seg_body,
    );
    let logic_fns = vec![list_seg_def];

    let mem = var("self");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_len = method_call(s.clone(), "len", vec![]);
    let null = var("NULL");
    let reverse_s = method_call(s, "reverse", vec![]);
    let invariant = implies(
        le(int(0), s_len.clone()),
        logic_fn_call(
            "Memory::list_seg",
            vec![
                mem,
                null.clone(),
                reverse_s,
                null,
                sub(s_len.clone(), int(0)),
                s_len,
            ],
        ),
    );

    let result = verify_initialization(
        &[],
        &[invariant.clone()],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("empty list_seg initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty list_seg with lower len - 0 and upper len should prove directly; got {result:?}"
    );

    let outcome = verify_initialization_outcome(
        &[],
        &[invariant],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("empty list_seg initialization outcome should encode");
    assert_verified_outcome_has_accepted_unsat_evidence(
        &outcome,
        "empty list_seg direct initialization should have solver evidence",
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_matches_list_seg_null_alias_directly() {
    let mem = var("self");
    let l = var("l");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_len = method_call(s.clone(), "len", vec![]);
    let fact = logic_fn_call(
        "Memory::list_seg",
        vec![
            mem.clone(),
            l.clone(),
            s.clone(),
            var("NULL"),
            int(0),
            s_len.clone(),
        ],
    );
    let invariant = logic_fn_call("Memory::list_seg", vec![mem, l, s, int(-1), int(0), s_len]);

    let result = verify_initialization(
        &[fact],
        &[invariant],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("list_seg null-alias initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "list_seg fact using NULL should prove the same segment using encoded null; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_implication_when_entry_guard_is_false() {
    let n = var_with_sort("n", ExprSort::Int);
    let s = var_with_sort("s", ExprSort::Seq);
    let s_len = method_call(s, "len", vec![]);
    let invariant = implies(
        eq(n.clone(), add(s_len, int(1))),
        logic_fn_call("Memory::expensive_unreachable_fact", vec![n.clone()]),
    );
    let init_extra_facts = vec![eq(n, int(0))];

    let result = verify_initialization(
        &[],
        &[invariant],
        &HashMap::new(),
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("false-guard implication initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "n == 0 and s.len() >= 0 should make n == s.len() + 1 false at entry; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_sum_of_seq_lens_guard_is_false_at_zero_entry() {
    let n = var_with_sort("n", ExprSort::Int);
    let s1 = var_with_sort("s1", ExprSort::Seq);
    let s2 = var_with_sort("s2", ExprSort::Seq);
    let s1_len = method_call(s1, "len", vec![]);
    let s2_len = method_call(s2, "len", vec![]);
    let invariant = implies(
        lt(add(s1_len, s2_len), n.clone()),
        logic_fn_call("Memory::expensive_lasso_phase_fact", vec![n.clone()]),
    );
    let init_extra_facts = vec![eq(n, int(0))];

    let result = verify_initialization(
        &[],
        &[invariant],
        &HashMap::new(),
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("sum-of-length false guard initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "seq lengths are nonnegative, so s1.len() + s2.len() < 0 is false at entry; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_uses_wrapper_require_body_as_direct_fact() {
    use trust_wp_core::logic::LogicFnDef;

    let mem = var("self");
    let first = var("l");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_len = method_call(s.clone(), "len", vec![]);
    let s_first = method_call(s.clone(), "index_logic", vec![int(0)]);
    let list_seg = logic_fn_call(
        "Memory::list_seg",
        vec![
            mem.clone(),
            first.clone(),
            s.clone(),
            s_first.clone(),
            int(0),
            s_len.clone(),
        ],
    );
    let loop_body = logic_fn_call(
        "Memory::list_seg",
        vec![
            var("self"),
            var("first"),
            var("s"),
            method_call(var("s"), "index_logic", vec![int(0)]),
            int(0),
            method_call(var("s"), "len", vec![]),
        ],
    );
    let loop_def = LogicFnDef::new(
        "loop_".to_string(),
        "Memory::loop_".to_string(),
        vec!["self".to_string(), "first".to_string(), "s".to_string()],
        loop_body,
    );
    let logic_fns = vec![loop_def];
    let requires = vec![logic_fn_call("Memory::loop_", vec![mem, first, s.clone()])];
    let invariant = implies(le(int(0), s_len), list_seg);

    let result = verify_initialization(
        &requires,
        &[invariant.clone()],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("wrapper require initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "loop_(self, l, s) should directly expose its list_seg body for initialization; got {result:?}"
    );

    let outcome = verify_initialization_outcome(
        &requires,
        &[invariant],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("wrapper require initialization outcome should encode");
    assert_verified_outcome_has_accepted_unsat_evidence(
        &outcome,
        "wrapper direct initialization should have solver evidence",
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_uses_method_list_wrapper_body_for_list_seg_view_alias() {
    use trust_wp_core::logic::LogicFnDef;

    let mem = var("self");
    let first = var("l");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_len = method_call(s.clone(), "len", vec![]);
    let list_body = method_call(
        var("self"),
        "list_seg",
        vec![
            var("first"),
            var("s"),
            var("NULL"),
            int(0),
            method_call(var("s"), "len", vec![]),
        ],
    );
    let list_def = LogicFnDef::new(
        "list".to_string(),
        "Memory::list".to_string(),
        vec!["self".to_string(), "first".to_string(), "s".to_string()],
        list_body,
    )
    .with_return_sort(Some(ExprSort::Bool));
    let list_seg_def = LogicFnDef::new(
        "list_seg".to_string(),
        "Memory::list_seg".to_string(),
        vec![
            "self".to_string(),
            "first".to_string(),
            "s".to_string(),
            "last".to_string(),
            "l".to_string(),
            "h".to_string(),
        ],
        PureExpr::Bool(true),
    )
    .with_return_sort(Some(ExprSort::Bool));
    let logic_fns = vec![list_def, list_seg_def];
    let requires = vec![method_call(
        mem.clone(),
        "list",
        vec![first.clone(), view(s.clone())],
    )];
    let invariant = logic_fn_call(
        "Memory::list_seg",
        vec![mem, first, s, int(-1), int(0), s_len],
    );

    let result = verify_initialization(
        &requires,
        &[invariant.clone()],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("method list wrapper initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "method-call list(self, l, View(s)) should expose list_seg with NULL/-1 and View(s) aliases; got {result:?}"
    );

    let outcome = verify_initialization_outcome(
        &requires,
        &[invariant],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("method list wrapper initialization outcome should encode");
    assert_verified_outcome_has_accepted_unsat_evidence(
        &outcome,
        "method list wrapper initialization should have solver evidence",
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_beta_reduces_lasso_wrapper_let_body_directly() {
    use trust_wp_core::logic::LogicFnDef;

    let len = |expr: PureExpr| method_call(expr, "len", vec![]);
    let last_index = |seq: PureExpr| sub(len(seq), int(1));
    let mid_expr = |s1: PureExpr, s2: PureExpr| {
        ite(
            eq(len(s2.clone()), int(0)),
            method_call(s1.clone(), "index_logic", vec![last_index(s1)]),
            method_call(s2.clone(), "index_logic", vec![last_index(s2)]),
        )
    };

    let body_s1 = var_with_sort("s1", ExprSort::Seq);
    let body_s2 = var_with_sort("s2", ExprSort::Seq);
    let lasso_body = let_bind(
        "mid",
        mid_expr(body_s1.clone(), body_s2),
        logic_fn_call(
            "Memory::list_seg",
            vec![
                var("self"),
                var("first"),
                body_s1.clone(),
                var("mid"),
                int(0),
                len(body_s1),
            ],
        ),
    );
    let lasso_def = LogicFnDef::new(
        "lasso".to_string(),
        "Memory::lasso".to_string(),
        vec![
            "self".to_string(),
            "first".to_string(),
            "s1".to_string(),
            "s2".to_string(),
        ],
        lasso_body,
    );
    let logic_fns = vec![lasso_def];

    let mem = var("self");
    let first = var("l");
    let s1 = var_with_sort("s1", ExprSort::Seq);
    let s2 = var_with_sort("s2", ExprSort::Seq);
    let requires = vec![logic_fn_call(
        "Memory::lasso",
        vec![
            mem.clone(),
            first.clone(),
            deref(view(s1.clone())),
            view(s2.clone()),
        ],
    )];
    let invariant_s1 = view(s1);
    let invariant_s2 = deref(view(s2));
    let invariant_mid = mid_expr(invariant_s1.clone(), invariant_s2);
    let invariant = implies(
        le(int(0), len(invariant_s1.clone())),
        logic_fn_call(
            "Memory::list_seg",
            vec![
                mem,
                first,
                invariant_s1.clone(),
                invariant_mid,
                int(0),
                len(invariant_s1),
            ],
        ),
    );

    let result = verify_initialization(
        &requires,
        &[invariant],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig {
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("lasso wrapper let-body initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "lasso wrapper let body should expose the list_seg fact across view/deref aliases; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_let_wrapped_sum_of_lens_guard_false_at_zero_entry() {
    let n = var_with_sort("n", ExprSort::Int);
    let s1 = var_with_sort("s1", ExprSort::Seq);
    let s2 = var_with_sort("s2", ExprSort::Seq);
    let len = |expr: PureExpr| method_call(expr, "len", vec![]);
    let mid = ite(
        eq(len(view(s2.clone())), int(0)),
        method_call(view(s1.clone()), "index_logic", vec![int(0)]),
        method_call(view(s2.clone()), "index_logic", vec![int(0)]),
    );
    let invariant = let_bind(
        "mid",
        mid,
        implies(
            lt(add(len(view(s1)), len(deref(view(s2)))), deref(n.clone())),
            logic_fn_call("Memory::expensive_lasso_phase_fact", vec![var("mid")]),
        ),
    );

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "n".to_string(),
        NamedBindingValue::new(Some(ExprSort::Int), int(0)),
    );

    let result = verify_initialization(
        &[],
        &[invariant],
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("let-wrapped sum-of-length false guard initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "seq lengths are nonnegative, so a let-wrapped s1.len() + s2.len() < *n guard is false when n starts at 0; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_matches_method_list_seg_with_view_and_null_aliases() {
    let mem = var("self");
    let first = var("l");
    let s = var_with_sort("s", ExprSort::Seq);
    let viewed_s = view(s.clone());
    let fact = method_call(
        mem.clone(),
        "list_seg",
        vec![
            first.clone(),
            viewed_s.clone(),
            var("NULL"),
            int(0),
            method_call(viewed_s, "len", vec![]),
        ],
    );
    let invariant = logic_fn_call(
        "Memory::list_seg",
        vec![
            mem,
            first,
            s.clone(),
            int(-1),
            int(0),
            method_call(s, "len", vec![]),
        ],
    );

    let result = verify_initialization(
        &[fact],
        &[invariant],
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("method list_seg initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "method-call list_seg should match logic list_seg across View(s) and NULL/-1 aliases; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_scalar_bound_from_literal_equality() {
    let perm_val = view(method_call(var("perm"), "val", vec![]));
    let requires = vec![eq(perm_val.clone(), int(1))];
    let invariants = vec![le(int(0), perm_val)];

    let result = verify_initialization(
        &requires,
        &invariants,
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("scalar literal equality initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "literal equality should prove a syntactic scalar bound directly; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_reversed_scalar_bound_fact() {
    let requires = vec![ge(var("pass"), int(1))];
    let invariants = vec![le(int(1), var("pass"))];

    let result = verify_initialization(
        &requires,
        &invariants,
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("reversed scalar bound initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pass >= 1 should directly prove 1 <= pass; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_proves_nested_for_loop_offset_bound() {
    let requires = vec![ge(var("pass"), int(1))];
    let invariants = vec![and(
        le(int(1), var("door")),
        le(var("door"), add(int(100), var("pass"))),
    )];

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("door".to_string(), NamedBindingValue::untyped(var("pass")));
    pre_loop_assignments.insert(
        "pass".to_string(),
        NamedBindingValue::untyped(var("__outer_range_elem")),
    );

    let result = verify_initialization(
        &requires,
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("nested for-loop scalar initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "door = pass and pass >= 1 should prove the 100doors inner-loop scalar bounds; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_matches_transparent_ward_deref_fact() {
    let ward = method_call(var("perm"), "ward", vec![]);
    let requires = vec![eq(deref(ward.clone()), var("ptr"))];
    let invariants = vec![eq(ward, var("ptr"))];

    let result = verify_initialization(
        &requires,
        &invariants,
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("transparent ward deref initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Deref(perm.ward()) should normalize to the stable ward target; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_transitively_includes_iter_state_view_chain() {
    let seq_sort = Some(ExprSort::Seq);
    let view_len = |name: &str| PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            name.to_string(),
            seq_sort.clone(),
        )))),
        method: "len".to_string(),
        args: vec![],
    };

    let invariants = vec![PureExpr::BinOp(
        Arc::new(view_len("iter")),
        BinOp::Eq,
        Arc::new(PureExpr::Var("len0".to_string(), None)),
    )];

    let init_extra_facts = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                "__trust_wp_for_iter_state_7".to_string(),
                seq_sort.clone(),
            )),
            BinOp::Eq,
            Arc::new(PureExpr::Var("iter".to_string(), seq_sort.clone())),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                "__trust_wp_for_iter_old_7".to_string(),
                seq_sort.clone(),
            )),
            BinOp::Eq,
            Arc::new(PureExpr::Var(
                "__trust_wp_for_iter_state_7".to_string(),
                seq_sort.clone(),
            )),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "__trust_wp_for_iter_state_7".to_string(),
                seq_sort.clone(),
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "iterable".to_string(),
                seq_sort.clone(),
            )))),
        ),
        PureExpr::BinOp(
            Arc::new(view_len("iterable")),
            BinOp::Eq,
            Arc::new(PureExpr::Var("len0".to_string(), None)),
        ),
    ];

    let result = verify_initialization(
        &[],
        &invariants,
        &HashMap::new(),
        &init_extra_facts,
        &LoopEncoderConfig::default(),
    )
    .expect("transitive iter-state init facts should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected transitive iter-state/view init facts to prove initialization, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_preservation_accepts_int_existential_invariant() {
    let invariants = vec![PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(crate::ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("i".to_string(), None)),
        )),
        triggers: vec![],
    }];
    let loop_condition = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("existential invariant should encode");
    // The formula `exists a: a == i_prime` is satisfiable with witness
    // `a = i + 1`; preservation should prove it directly.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "existential invariant should be preserved; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
/// Forced hard timeout on `loop_entry_may_execute` conservatively returns
/// `true` (loop may execute) so variant checks are not skipped (#2457).
fn loop_entry_may_execute_returns_true_on_forced_hard_timeout() {
    use crate::verify::force_hard_timeout_for_test;

    let loop_condition = PureExpr::Var("flag".to_string(), None);

    let _guard = force_hard_timeout_for_test();
    let may_execute = loop_entry_may_execute(
        &[],
        &HashMap::new(),
        Some(&loop_condition),
        &LoopEncoderConfig {
            timeout: Some(std::time::Duration::from_millis(1)),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("loop entry should encode even under forced timeout");

    assert!(
        may_execute,
        "loop_entry_may_execute should conservatively return true on hard timeout"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_scalar_failure_beats_existential_unknown_sibling() {
    let invariants = vec![
        PureExpr::Exists {
            var: "a".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("a".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Var("i".to_string(), None)),
            )),
            triggers: vec![],
        },
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(5)),
    );

    let result = verify_initialization(
        &[],
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("mixed initialization invariants should encode");

    assert_initialization_failed_result(
        &result,
        "failing scalar initialization invariant should beat quantified sibling Unknown",
    );
}

/// Multiple invariants where the first is provable but the second is false:
/// the conjunction must fail because initialization checks ALL invariants,
/// not just the first. This catches a potential short-circuit bug where
/// a passing first slice masks a failing second slice.
#[test]
#[timeout(30000)]
fn verify_initialization_fails_when_any_invariant_is_false() {
    // Pre-loop: x = 10
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "x".to_string(),
        NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(10)),
    );

    let invariants = vec![
        // x > 0 — true when x == 10
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        // x < 0 — false when x == 10
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        ),
    ];

    let result = verify_initialization(
        &[],
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("mixed true/false invariants should encode successfully");

    assert_initialization_failed_result(
        &result,
        "initialization when any invariant is false at entry",
    );
}

/// Pre-loop assignment value contradicts a require: `requires(x > 100)` but
/// `x = 5`. The contradiction makes the precondition base vacuous, so
/// initialization returns Unknown with a vacuity message rather than a proof
/// or a counterexample.
#[test]
#[timeout(30000)]
fn verify_initialization_detects_vacuity_when_assignment_contradicts_require() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(100)),
    )];
    // Pre-loop: x = 5, contradicting requires(x > 100)
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "x".to_string(),
        NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(5)),
    );

    // Invariant: x > 0 — true for x=5 but the precondition base is UNSAT
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let result = verify_initialization(
        &requires,
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("contradictory require + assignment should encode");

    match &result {
        VerificationResult::Unknown(crate::UnknownReason::SolverMessage(msg))
            if msg.contains(crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE) => {}
        other => panic!(
            "vacuous precondition base should yield Unknown(vacuous), not a spurious proof; got {other:?}"
        ),
    }
}

/// Empty requires with a non-trivial invariant provable purely from the
/// pre-loop assignment. Ensures that initialization works without any
/// preconditions — the assignment alone suffices.
#[test]
#[timeout(30000)]
fn verify_initialization_passes_from_assignment_alone_without_requires() {
    // Pre-loop: n = 42
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "n".to_string(),
        NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(42)),
    );

    // Invariant: n >= 0 AND n < 100 — true when n == 42
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(100)),
        )),
    )];

    let result = verify_initialization(
        &[],
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("no-requires initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "assignment n=42 should prove 0 <= n < 100 without any requires; got {result:?}"
    );
}

/// Seq-annotated variable in pre-loop assignment ensures sort propagation
/// through the initialization pipeline. The invariant references a Seq
/// method (`push_back`) that requires the variable to have Seq sort —
/// if the sort annotation is dropped, the encoder falls back to Int sort
/// and the axiom for `push_back` is not triggered.
#[test]
#[timeout(30000)]
fn verify_initialization_seq_annotated_push_back_preserves_sort() {
    let seq_empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    // Pre-loop: items = seq_empty() with Seq sort
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "items".to_string(),
        NamedBindingValue::new(Some(ExprSort::Seq), seq_empty.clone()),
    );

    // Invariant: items == seq_empty()
    // This is a direct equality — simpler than the len-based test above,
    // and exercises the Seq sort propagation for value equality.
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::Var("items".to_string(), Some(ExprSort::Seq))),
        BinOp::Eq,
        Arc::new(seq_empty),
    );

    let result = verify_initialization(
        &[],
        &[invariant],
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("Seq-annotated push_back initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "items == seq_empty() should verify when items is Seq-sorted and assigned seq_empty(); got {result:?}"
    );
}

fn assert_verified_outcome_has_accepted_unsat_evidence(
    outcome: &VerificationOutcome,
    context: &str,
) {
    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "{context}: expected Verified outcome, got {:?}",
        outcome.result
    );
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .unwrap_or_else(|| panic!("{context}: missing solver evidence"));
    assert!(
        evidence.result.to_ascii_lowercase().contains("unsat"),
        "{context}: expected UNSAT evidence, got {evidence:?}"
    );
    assert!(
        evidence.accepted_for_consumer,
        "{context}: evidence rejected: {evidence:?}"
    );
}

/// Bool-annotated variable in pre-loop assignment. Ensures the encoder
/// treats the variable as Bool sort (not the default Int fallback) when
/// the NamedBindingValue carries `ExprSort::Bool`. The invariant is a
/// logical expression over the Bool variable that would be non-trivial
/// if the sort were misinterpreted as Int.
#[test]
#[timeout(30000)]
fn verify_initialization_bool_annotated_variable_preserves_sort() {
    // Pre-loop: found = false with Bool sort annotation
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "found".to_string(),
        NamedBindingValue::new(Some(ExprSort::Bool), PureExpr::Bool(false)),
    );

    // Invariant: NOT found
    // When found == false, NOT found == NOT false == true.
    let invariant = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Var("found".to_string(), Some(ExprSort::Bool))),
    );

    let result = verify_initialization(
        &[],
        &[invariant],
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("Bool-annotated initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NOT found should verify when found is Bool-sorted and assigned false; got {result:?}"
    );
}

/// Regression for `inferred_invariants::nested_borrows` (Wave 6B).
///
/// `pub fn nested_borrows(x: &mut &mut i32)` with `#[requires(**x == 0)]`
/// and `#[invariant(**x == 0)]`. Both reference `**x`. The contract parser
/// emits both as `Deref(Deref(Var("x", MutRef(MutRef(Int)))))`, and the
/// loop initialization VC must see them produce the same SMT term so that
/// `precondition => invariant` holds trivially. Before the fix, the
/// requires path encoded `**x` to one carrier and the invariant path
/// encoded the same syntactic expression to a different carrier, so
/// initialization failed with `precondition does not imply invariant`.
#[test]
#[timeout(30000)]
fn verify_initialization_double_deref_mut_ref_invariant_matches_requires() {
    let x_sort = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int))));
    let x_var = PureExpr::Var("x".to_string(), Some(x_sort));
    let double_deref = || PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(x_var.clone()))));
    let eq_zero =
        |expr: PureExpr| PureExpr::BinOp(Arc::new(expr), BinOp::Eq, Arc::new(PureExpr::Int(0)));

    let requires = vec![eq_zero(double_deref())];
    let invariants = vec![eq_zero(double_deref())];

    // Mimic the function body's `let mut i = 0` shape.
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let result = verify_initialization(
        &requires,
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("Double-deref MutRef(MutRef) requires+invariant should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "requires(**x == 0) should imply invariant(**x == 0); got {result:?}"
    );
}
