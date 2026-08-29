// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Bisect #5: structural invariant ONLY (no user invariants), with transition
/// facts and iter_state + produced body effects.  If this passes, the structural
/// invariant CAN be preserved in isolation and the failure is an interaction effect
/// with the user invariants.  If it fails, the structural invariant's Seq/start_log
/// encoding is itself broken.
#[test]
#[timeout(30000)]
fn inc_max_repeat_structural_only_with_transition() {
    use trust_wp_core::formula::ExprSort;

    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let iter_state = PureExpr::Var("iter_state".to_string(), None);
    let iter_state_next = PureExpr::Var("iter_state_next".to_string(), None);
    let iter_old = PureExpr::Var("iter_old".to_string(), None);

    fn mc(r: &PureExpr, m: &str) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(r.clone()),
            method: m.to_string(),
            args: vec![],
        }
    }
    let produced_len = mc(&produced, "len");
    let is_start = mc(&iter_state, "start_log");
    let isn_start = mc(&iter_state_next, "start_log");
    let is_end = mc(&iter_state, "end_log");
    let isn_end = mc(&iter_state_next, "end_log");
    let io_start = mc(&iter_old, "start_log");
    let io_end = mc(&iter_old, "end_log");

    // Structural invariant ONLY:
    // iter_old.end_log() == iter_state.end_log()
    // && iter_old.start_log() <= iter_state.start_log()
    // && produced.len() == iter_state.start_log() - iter_old.start_log()
    let struct_inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(io_end.clone()),
            BinOp::Eq,
            Arc::new(is_end.clone()),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(io_start.clone()),
                BinOp::Le,
                Arc::new(is_start.clone()),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(produced_len.clone()),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(is_start.clone()),
                    BinOp::Sub,
                    Arc::new(io_start.clone()),
                )),
            )),
        )),
    );

    let invariants = vec![struct_inv];
    let loop_condition = PureExpr::BinOp(
        Arc::new(is_start.clone()),
        BinOp::Lt,
        Arc::new(io_end.clone()),
    );

    let tf_end = PureExpr::BinOp(Arc::new(is_end), BinOp::Eq, Arc::new(isn_end));
    let tf_guard = PureExpr::BinOp(Arc::new(is_start.clone()), BinOp::Lt, Arc::new(io_end));
    let tf_step = PureExpr::BinOp(
        Arc::new(isn_start),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(is_start),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(produced.clone()),
            method: "push_back".to_string(),
            args: vec![elem],
        },
    );
    body_effect.insert("iter_state".to_string(), iter_state_next.clone());

    let modified_vars: Vec<&str> = vec!["produced", "iter_state"];
    let transition_facts = vec![tf_end, tf_guard, tf_step];
    let config = LoopEncoderConfig::default().with_transition_facts(&transition_facts);

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        BodyEffects::new(&body_effect, &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "structural inv only (with transition facts) should verify, got {result:?}"
    );
}

/// Bisect #6: same arithmetic as the structural invariant but with direct Int
/// variables instead of UF method calls (start_log/end_log).  If this passes
/// but #5 fails, the UF indirection is the issue.
///
/// Invariant: `len(produced) == counter - base`
/// Effects: `produced' = push_back(produced, elem)`, `counter' = counter + 1`
/// Prove: `len(produced') == counter' - base`
#[test]
#[timeout(30000)]
fn inc_max_repeat_structural_no_uf_direct_ints() {
    use trust_wp_core::formula::ExprSort;

    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let counter = PureExpr::Var("counter".to_string(), None);
    let base = PureExpr::Var("base".to_string(), None);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    // Invariant: len(produced) == counter - base
    let inv = PureExpr::BinOp(
        Arc::new(produced_len.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(counter.clone()),
            BinOp::Sub,
            Arc::new(base.clone()),
        )),
    );

    let invariants = vec![inv];
    let loop_condition = PureExpr::BinOp(
        Arc::new(counter.clone()),
        BinOp::Lt,
        Arc::new(PureExpr::Var("end_val".to_string(), None)),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(produced.clone()),
            method: "push_back".to_string(),
            args: vec![elem],
        },
    );
    body_effect.insert(
        "counter".to_string(),
        PureExpr::BinOp(
            Arc::new(counter.clone()),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let modified_vars: Vec<&str> = vec!["produced", "counter"];
    let config = LoopEncoderConfig::default();

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        BodyEffects::new(&body_effect, &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "structural inv (direct ints, no UF) should verify, got {result:?}"
    );
}
