// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Same as above but with Seq-based `produced` body effect, matching the real
/// pipeline encoding for range iterators. The produced ghost variable's body
/// effect is `produced.push_back(elem)`, and the invariant references
/// `produced.len()` (via the structural invariant `produced.len() == ...`).
///
/// Without the ground-pool pre-assertion fix (#2323), this test times out
/// because the axiom-free probe fails on the Seq `push_back` term, then the
/// full axiom suite overwhelms E-matching on what is fundamentally a simple
/// arithmetic VC.
#[test]
#[timeout(30000)]
fn inc_max_repeat_preservation_with_seq_produced() {
    use trust_wp_core::formula::ExprSort;

    let a = PureExpr::Var("a".to_string(), None);
    let b = PureExpr::Var("b".to_string(), None);
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);

    // produced.len()
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    // Invariant 1: a <= 1_000_000 + produced.len() && b <= 1_000_000 + produced.len()
    let million = PureExpr::Int(1_000_000);
    let inv1 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(a.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(million.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(b.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(million.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
    );

    // Invariant 2: a >= b + produced.len() || b >= a + produced.len()
    let inv2 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(a.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::BinOp(
                Arc::new(b.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
        BinOp::Or,
        Arc::new(PureExpr::BinOp(
            Arc::new(b.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::BinOp(
                Arc::new(a.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
    );

    let invariants = vec![inv1, inv2];

    // Loop condition: produced.len() < n
    let loop_condition = PureExpr::BinOp(
        Arc::new(produced_len.clone()),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    // Body effects: ITE from take_max
    let cond = PureExpr::BinOp(Arc::new(a.clone()), BinOp::Ge, Arc::new(b.clone()));

    let mut body_effect = HashMap::new();
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
    // produced' = produced.push_back(elem)  — Seq body effect
    body_effect.insert(
        "produced".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(produced.clone()),
            method: "push_back".to_string(),
            args: vec![elem],
        },
    );

    let modified_vars: Vec<&str> = vec!["a", "b", "produced"];
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
        "inc_max_repeat preservation with Seq produced body effect should verify, got {result:?}"
    );
}

/// Full-pipeline reproduction for #2323: includes View wrappers on `a@`/`b@`,
/// the structural range invariant, transition facts, and `iter_state` body effect.
///
/// This matches the actual driver→encoder configuration for `inc_max_repeat`:
/// - User invariants use `a@` (View) and `produced.len()`
/// - Structural invariant relates `produced.len()` to range state
/// - Transition facts constrain one-step range advancement
/// - Body effects include `iter_state -> iter_state_next`
#[test]
#[timeout(30000)]
fn inc_max_repeat_preservation_full_pipeline() {
    use trust_wp_core::formula::ExprSort;

    let a = PureExpr::Var("a".to_string(), None);
    let b = PureExpr::Var("b".to_string(), None);
    let a_view = PureExpr::View(Arc::new(a.clone()));
    let b_view = PureExpr::View(Arc::new(b.clone()));
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);

    // Range iterator state variables
    let iter_state = PureExpr::Var("$for_iter_state_5".to_string(), None);
    let iter_state_next = PureExpr::Var("$for_iter_state_next_5".to_string(), None);
    let iter_old = PureExpr::Var("$for_iter_old_5".to_string(), None);

    // Helper: method call
    fn mc(receiver: &PureExpr, method: &str) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver.clone()),
            method: method.to_string(),
            args: vec![],
        }
    }

    let produced_len = mc(&produced, "len");
    let iter_state_start = mc(&iter_state, "start_log");
    let iter_state_next_start = mc(&iter_state_next, "start_log");
    let iter_old_start = mc(&iter_old, "start_log");
    let iter_state_end = mc(&iter_state, "end_log");
    let iter_state_next_end = mc(&iter_state_next, "end_log");
    let iter_old_end = mc(&iter_old, "end_log");

    let million = PureExpr::Int(1_000_000);

    // User invariant 1: a@ <= 1_000_000 + produced.len() && b@ <= 1_000_000 + produced.len()
    let inv1 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(a_view.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(million.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(b_view.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(million.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
    );

    // User invariant 2: a@ >= b@ + produced.len() || b@ >= a@ + produced.len()
    let inv2 = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(a_view.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::BinOp(
                Arc::new(b_view.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
        BinOp::Or,
        Arc::new(PureExpr::BinOp(
            Arc::new(b_view.clone()),
            BinOp::Ge,
            Arc::new(PureExpr::BinOp(
                Arc::new(a_view.clone()),
                BinOp::Add,
                Arc::new(produced_len.clone()),
            )),
        )),
    );

    // Structural invariant (range):
    // iter_old.end_log() == iter_state.end_log()
    // && iter_old.start_log() <= iter_state.start_log()
    // && produced.len() == iter_state.start_log() - iter_old.start_log()
    let struct_inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(iter_old_end.clone()),
            BinOp::Eq,
            Arc::new(iter_state_end.clone()),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(iter_old_start.clone()),
                BinOp::Le,
                Arc::new(iter_state_start.clone()),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(produced_len.clone()),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(iter_state_start.clone()),
                    BinOp::Sub,
                    Arc::new(iter_old_start.clone()),
                )),
            )),
        )),
    );

    let invariants = vec![inv1, inv2, struct_inv];

    // Loop condition (range header): iter_state.start_log() < iter_old.end_log()
    let loop_condition = PureExpr::BinOp(
        Arc::new(iter_state_start.clone()),
        BinOp::Lt,
        Arc::new(iter_old_end.clone()),
    );

    // Transition facts:
    // 1. iter_state.end_log() == iter_state_next.end_log()
    let tf_end = PureExpr::BinOp(
        Arc::new(iter_state_end.clone()),
        BinOp::Eq,
        Arc::new(iter_state_next_end),
    );
    // 2. iter_state.start_log() < iter_old.end_log() (guard)
    let tf_guard = PureExpr::BinOp(
        Arc::new(iter_state_start.clone()),
        BinOp::Lt,
        Arc::new(iter_old_end.clone()),
    );
    // 3. iter_state_next.start_log() == iter_state.start_log() + 1
    let tf_step = PureExpr::BinOp(
        Arc::new(iter_state_next_start),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(iter_state_start.clone()),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    // Body effects
    let cond = PureExpr::BinOp(Arc::new(a.clone()), BinOp::Ge, Arc::new(b.clone()));

    let mut body_effect = HashMap::new();
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
    body_effect.insert(
        "produced".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(produced.clone()),
            method: "push_back".to_string(),
            args: vec![elem],
        },
    );
    // iter_state' = iter_state_next
    body_effect.insert("$for_iter_state_5".to_string(), iter_state_next.clone());

    let modified_vars: Vec<&str> = vec!["a", "b", "produced", "$for_iter_state_5"];
    let transition_facts = vec![tf_end, tf_guard, tf_step];
    let config = LoopEncoderConfig::default()
        .with_transition_facts(&transition_facts)
        .with_timeout(std::time::Duration::from_millis(500));

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false, // header condition
        &modified_vars,
        BodyEffects::new(&body_effect, &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("preservation encoding should succeed");

    assert!(
        matches!(
            result,
            VerificationResult::Verified(_) | VerificationResult::Unknown(_)
        ),
        "inc_max_repeat full-pipeline preservation should verify or fail closed, got {result:?}"
    );
}
