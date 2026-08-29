// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Bisect #1: full pipeline but WITHOUT View wrappers on a/b.
#[test]
#[timeout(30000)]
fn inc_max_repeat_full_pipeline_no_view() {
    use trust_wp_core::formula::ExprSort;

    let a = PureExpr::Var("a".to_string(), None);
    let b = PureExpr::Var("b".to_string(), None);
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
    let io_start = mc(&iter_old, "start_log");
    let is_end = mc(&iter_state, "end_log");
    let isn_end = mc(&iter_state_next, "end_log");
    let io_end = mc(&iter_old, "end_log");

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
    let invariants = vec![inv1, inv2, struct_inv];
    let loop_condition = PureExpr::BinOp(
        Arc::new(is_start.clone()),
        BinOp::Lt,
        Arc::new(io_end.clone()),
    );

    let tf_end = PureExpr::BinOp(Arc::new(is_end.clone()), BinOp::Eq, Arc::new(isn_end));
    let tf_guard = PureExpr::BinOp(
        Arc::new(is_start.clone()),
        BinOp::Lt,
        Arc::new(io_end.clone()),
    );
    let tf_step = PureExpr::BinOp(
        Arc::new(isn_start),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(is_start.clone()),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

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
    body_effect.insert("iter_state".to_string(), iter_state_next.clone());

    let modified_vars: Vec<&str> = vec!["a", "b", "produced", "iter_state"];
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
        "no-view variant should verify, got {result:?}"
    );
}

/// Bisect #2: View wrappers but NO structural invariant or transition facts.
#[test]
#[timeout(30000)]
fn inc_max_repeat_view_no_structural() {
    use trust_wp_core::formula::ExprSort;

    let a = PureExpr::Var("a".to_string(), None);
    let b = PureExpr::Var("b".to_string(), None);
    let a_view = PureExpr::View(Arc::new(a.clone()));
    let b_view = PureExpr::View(Arc::new(b.clone()));
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    let million = PureExpr::Int(1_000_000);
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
    let invariants = vec![inv1, inv2];
    let loop_condition = PureExpr::BinOp(
        Arc::new(produced_len.clone()),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

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

    let modified_vars: Vec<&str> = vec!["a", "b", "produced"];
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
        "view-no-structural variant should verify, got {result:?}"
    );
}
