// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

mod seq_raw;

#[test]
#[timeout(30000)]
fn verify_postcondition_preserves_unmodified_pre_loop_assignment() {
    let invariants = vec![PureExpr::Bool(true)];
    let loop_condition = PureExpr::Var("b".to_string(), None);
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    )];
    let modified_vars: Vec<&str> = Vec::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "x".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(10)),
    );

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &pre_loop_assignments, &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected postcondition VC to verify, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_postcondition_proves_shadow_counter_relation() {
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("j".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("i".to_string(), None)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Le,
                Arc::new(PureExpr::Var("n".to_string(), None)),
            )),
        ),
    ];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let return_expr = PureExpr::Var("j".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i", "j"];

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert(
        "j".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(
            &ensures,
            Some(&return_expr),
            &pre_loop_assignments,
            &[],
            &[],
        ),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected postcondition VC to verify, got {result:?}"
    );
}
#[test]
#[timeout(30000)]
fn verify_preservation_scalar_failure_beats_existential_unknown_sibling() {
    let invariants = vec![
        PureExpr::Exists {
            var: "a".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("a".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Var("i".to_string(), None)),
            )),
            triggers: vec![],
        },
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
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
    .expect("mixed preservation invariants should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "failing scalar preservation invariant should beat quantified sibling Unknown: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_preservation_links_nested_current_chain_invariants() {
    // `***x` encodes to `x_current_current_current`.
    // With `**x` body effects we constrain `x_prime_current_current`.
    // Current-chain aliases must bridge:
    //   x_prime_current_current_current = x_prime_current_current = 0
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
        ))))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];
    let loop_condition = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = vec!["x"];
    let body_effect = HashMap::new();
    let deref_body_effect = HashMap::new();
    let mut double_deref_body_effect = HashMap::new();
    double_deref_body_effect.insert("x".to_string(), PureExpr::Int(0));

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        effects(&body_effect, &deref_body_effect, &double_deref_body_effect),
        &LoopEncoderConfig::default(),
    )
    .expect("nested current-chain preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected nested _current-chain aliasing to prove preservation, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_preservation_keeps_reachable_deref_effect_without_direct_modified_var() {
    let invariants = vec![eq(deref(var("v")), int(0))];
    let loop_condition = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = Vec::new();
    let body_effect = HashMap::new();
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("v".to_string(), int(1));
    let double_deref_body_effect = HashMap::new();

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        effects(&body_effect, &deref_body_effect, &double_deref_body_effect),
        &LoopEncoderConfig::default(),
    )
    .expect("deref-only preservation should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "reachable deref effects must be applied even when the reference is not directly modified; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_preservation_handles_all_zero_prefix_push_set_step() {
    fn seq_len(receiver: PureExpr) -> PureExpr {
        method_call(receiver, "len", vec![])
    }

    fn seq_index(receiver: PureExpr, index: PureExpr) -> PureExpr {
        method_call(receiver, "index", vec![index])
    }

    fn seq_push_back(receiver: PureExpr, value: PureExpr) -> PureExpr {
        method_call(receiver, "push_back", vec![value])
    }

    fn seq_set(receiver: PureExpr, index: PureExpr, value: PureExpr) -> PureExpr {
        method_call(receiver, "set", vec![index, value])
    }

    let produced = var_with_sort("produced", ExprSort::Seq);
    let v = var("v");
    let v_view = view(deref(v.clone()));
    let j = var_with_sort("j", ExprSort::Int);
    let prefix_guard = and(
        le(int(0), j.clone()),
        lt(j.clone(), seq_len(produced.clone())),
    );
    let invariant = forall_with_sort(
        "j",
        ExprSort::Int,
        implies(
            prefix_guard,
            eq(seq_index(v_view.clone(), j.clone()), int(0)),
        ),
    );
    let len_invariant = eq(seq_len(v), seq_len(var("old_v")));
    let invariants = vec![len_invariant, invariant];
    let loop_condition = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = vec!["produced", "v"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        seq_push_back(produced.clone(), var("i")),
    );
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("v".to_string(), seq_set(v_view, var("i"), int(0)));
    let double_deref_body_effect = HashMap::new();

    let produced_next = seq_push_back(produced.clone(), var("i"));
    let transition_facts = vec![
        eq(var("i"), seq_len(produced.clone())),
        eq(seq_len(produced_next), add(seq_len(produced), int(1))),
    ];
    let config = LoopEncoderConfig::default().with_transition_facts(&transition_facts);

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        effects(&body_effect, &deref_body_effect, &double_deref_body_effect),
        &config,
    )
    .expect("all_zero-style preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "all_zero prefix invariant should preserve across produced.push_back(i) and v.set(i, 0); got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_initialization_links_nested_current_chain_invariants() {
    // `***x == **x` is valid only when `_current`-chain aliases are asserted.
    // Initialization must add those aliases before satisfiability checking.
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
        ))))),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("x".to_string(), None),
        ))))),
    )];

    let result = verify_initialization(
        &[],
        &invariants,
        &HashMap::new(),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("initialization should encode nested current-chain invariant");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected nested _current-chain aliasing to prove initialization, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_postcondition_links_nested_current_chain_ensures() {
    // Postconditions can also reference nested current chains. Ensure
    // postcondition VCs add `_current` aliases before satisfiability checks.
    let invariants = vec![PureExpr::Bool(true)];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
        ))))),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("x".to_string(), None),
        ))))),
    )];
    let modified_vars: Vec<&str> = Vec::new();

    let result = verify_postcondition(
        &invariants,
        None,
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition should encode nested current-chain ensures");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected nested _current-chain aliasing to prove postcondition, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn verify_postcondition_rejects_non_boolean_ensures() {
    let invariants = vec![PureExpr::Bool(true)];
    let loop_condition = PureExpr::Bool(false);
    let ensures = vec![PureExpr::Int(1)];
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = Vec::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(3)),
    );

    let err = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(
            &ensures,
            Some(&return_expr),
            &pre_loop_assignments,
            &[],
            &[],
        ),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect_err("non-boolean postcondition should return an encoding error");
    let msg = err.to_string();
    assert!(
        msg.contains("boolean"),
        "error should mention boolean requirement, got: {msg}"
    );
}

/// Defensive check: body_effect key not in modified_vars triggers debug_assert. (#1884)
///
/// If `i` has a body effect (`i = i + 1`) but is not listed in `modified_vars`,
/// the postcondition VC would unsoundly include frame assignments constraining
/// `i == 0` (its pre-loop value) and admit requires referencing `i`. This test
/// verifies that `verify_loop_invariant_inner` catches the inconsistency.
#[test]
#[timeout(30000)]
fn missing_modified_var_returns_encoding_error() {
    // Loop: i starts at 0, body increments i, but modified_vars is EMPTY.
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(10)),
    );

    // body_effect says i is modified, but modified_vars is empty — inconsistency!
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: false,
        modified_vars: &[], // MISSING: should contain "i"
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };
    // Must return Err, not silently pass through in release builds.
    let result = verify_loop_invariant_inner(&ctx);
    assert!(
        result.is_err(),
        "expected EncodingError for body_effect/modified_vars mismatch"
    );
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("body effect variable `i` is not in modified_vars"),
        "error should identify the offending variable, got: {msg}"
    );
}

/// Reproduction of inc_max_repeat (#2323): ITE body effects from conditional
/// mut-ref return + disjunctive invariant + counter increment.
///
/// Invariants:
///   1. a <= 1_000_000 + len && b <= 1_000_000 + len
///   2. a >= b + len || b >= a + len
///
/// Body effects (from `take_max(&mut a, &mut b); *mc += 1`):
///   a' = ITE(a >= b, a + 1, a)
///   b' = ITE(a >= b, b, b + 1)
///   len' = len + 1
///
/// This is a pure QF_LIA problem with ITE terms. If ay can solve this in
/// under 10s, the full-pipeline timeout is caused by encoding overhead
/// (structural invariant, Seq axioms, etc.), not solver capacity.
#[test]
#[timeout(30000)]
fn inc_max_repeat_preservation_ite_disjunctive_invariant() {
    let a = PureExpr::Var("a".to_string(), None);
    let b = PureExpr::Var("b".to_string(), None);
    let len = PureExpr::Var("len".to_string(), None);
    let million = PureExpr::Int(1_000_000);

    // Invariant 1: a <= 1_000_000 + len && b <= 1_000_000 + len
    let inv1 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(a.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(million.clone()),
                BinOp::Add,
                Arc::new(len.clone()),
            )),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(b.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(million.clone()),
                BinOp::Add,
                Arc::new(len.clone()),
            )),
        )),
    );

    // Invariant 2: a >= b + len || b >= a + len
    let inv2 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(a.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::BinOp(
                Arc::new(b.clone()),
                BinOp::Add,
                Arc::new(len.clone()),
            )),
        )),
        BinOp::Or,
        Arc::new(PureExpr::BinOp(
            Arc::new(b.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::BinOp(
                Arc::new(a.clone()),
                BinOp::Add,
                Arc::new(len.clone()),
            )),
        )),
    );

    let invariants = vec![inv1, inv2];

    // Loop condition: len < n (range not exhausted)
    let loop_condition = PureExpr::BinOp(
        Arc::new(len.clone()),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    // Body effects: ITE from take_max conditional return
    let cond = PureExpr::BinOp(Arc::new(a.clone()), BinOp::Ge, Arc::new(b.clone()));

    let mut body_effect = HashMap::new();
    // a' = ITE(a >= b, a + 1, a)
    body_effect.insert(
        "a".to_string(),
        PureExpr::Ite(
            Arc::new(cond.clone()),
            Arc::new(PureExpr::BinOp(
                Arc::new(a.clone()),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            Arc::new(a.clone()),
        ),
    );
    // b' = ITE(a >= b, b, b + 1)
    body_effect.insert(
        "b".to_string(),
        PureExpr::Ite(
            Arc::new(cond.clone()),
            Arc::new(b.clone()),
            Arc::new(PureExpr::BinOp(
                Arc::new(b.clone()),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        ),
    );
    // len' = len + 1
    body_effect.insert(
        "len".to_string(),
        PureExpr::BinOp(
            Arc::new(len.clone()),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let modified_vars: Vec<&str> = vec!["a", "b", "len"];
    let config = LoopEncoderConfig::default();

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &config,
    )
    .expect("preservation encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_repeat preservation with ITE body effects should verify, got {result:?}"
    );
}
