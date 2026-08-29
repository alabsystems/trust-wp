// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::encoder::trigger::synthesize_triggers;

/// Build a PureExpr body with N distinct `LogicFnCall` nodes, each mentioning
/// one of the given variables as an argument.
fn build_body_with_n_logic_fn_calls(n: usize, vars: &[String]) -> PureExpr {
    // Build: f_0(v_0) && f_1(v_1) && ... && f_{n-1}(v_{(n-1) % vars.len()})
    let calls: Vec<PureExpr> = (0..n)
        .map(|i| PureExpr::LogicFnCall {
            name: format!("f_{i}"),
            args: vec![PureExpr::Var(vars[i % vars.len()].clone(), None)],
        })
        .collect();

    // Chain with And: c_0 && c_1 && ... && c_{n-1}
    calls
        .into_iter()
        .reduce(|acc, call| {
            PureExpr::BinOp(
                Arc::new(acc),
                trust_wp_core::formula::BinOp::And,
                Arc::new(call),
            )
        })
        .unwrap_or(PureExpr::Bool(true))
}

fn wrap_with_not_layers(mut expr: PureExpr, layers: usize) -> PureExpr {
    for _ in 0..layers {
        expr = not(expr);
    }
    expr
}

/// Build a trigger body where the only covering pair is the final deep pair.
///
/// The decoys mention only `vars[0]` or `vars[1]`. The two late candidates
/// cover `{vars[0], vars[1]}` and `{vars[2], vars[3]}` respectively, so the
/// pair search must scan every decoy pair before it can return a covering pair.
#[allow(clippy::cast_possible_wrap)]
fn build_late_pair_search_body(decoy_count: usize, vars: &[String]) -> PureExpr {
    assert!(
        vars.len() == 4,
        "late-pair helper requires exactly 4 quantified vars"
    );

    let mut terms = Vec::with_capacity(decoy_count + 2);
    for i in 0..decoy_count {
        let var_name = if i % 2 == 0 { &vars[0] } else { &vars[1] };
        let call = logic_fn_call(&format!("decoy_{i}"), vec![var(var_name)]);
        terms.push(gt(call, int(i as i64)));
    }

    let late_left = logic_fn_call("late_ab", vec![var(&vars[0]), var(&vars[1])]);
    let late_right = logic_fn_call("late_cd", vec![var(&vars[2]), var(&vars[3])]);
    terms.push(wrap_with_not_layers(gt(late_left, int(0)), 8));
    terms.push(wrap_with_not_layers(gt(late_right, int(0)), 8));

    terms
        .into_iter()
        .reduce(|acc, term| {
            PureExpr::BinOp(
                Arc::new(acc),
                trust_wp_core::formula::BinOp::And,
                Arc::new(term),
            )
        })
        .unwrap_or(PureExpr::Bool(true))
}

fn assert_late_pair_triggers(vars: &[String], body: &PureExpr) {
    let triggers = synthesize_triggers(vars, body);
    assert_eq!(
        triggers.len(),
        1,
        "late-pair body should synthesize one multi-trigger"
    );
    assert_eq!(
        triggers[0].len(),
        2,
        "late-pair body should require two trigger terms"
    );
    let trigger_names: HashSet<_> = triggers[0]
        .iter()
        .map(|expr| match expr {
            PureExpr::LogicFnCall { name, .. } => name.as_str(),
            other => panic!("expected LogicFnCall trigger, got {other:?}"),
        })
        .collect();
    assert_eq!(
        trigger_names,
        HashSet::from(["late_ab", "late_cd"]),
        "late-pair helper should force the terminal covering pair"
    );
}

/// Measures the late-pair trigger-synthesis path through `encode_pure`.
///
/// The body builder deliberately places the only covering pair behind many
/// single-variable decoys, so `synthesize_triggers` must scan almost the full
/// candidate matrix before finding a covering pair. This keeps the integration
/// test on the real O(C²) path instead of the previous first-pair early exit.
///
/// Re: performance_proofs phase — trigger synthesis O(C²) pair search
#[test]
#[timeout(30000)]
fn test_trigger_synthesis_pair_search_scaling() {
    use std::time::Instant;

    let small_n = 20;
    let large_n = 80;
    let rounds = 5;
    let iters = 50;
    let vars = vec![
        "i".to_string(),
        "j".to_string(),
        "k".to_string(),
        "m".to_string(),
    ];
    let wrap_forall = |body: PureExpr| {
        vars.iter()
            .rev()
            .fold(body, |acc, var_name| forall(var_name, acc))
    };

    let small_body = build_late_pair_search_body(small_n, &vars);
    let large_body = build_late_pair_search_body(large_n, &vars);
    assert_late_pair_triggers(&vars, &small_body);
    assert_late_pair_triggers(&vars, &large_body);

    let small_expr = wrap_forall(small_body);
    let large_expr = wrap_forall(large_body);

    for expr in [&small_expr, &large_expr] {
        let mut enc = AYEncoder::new_with_quantifiers();
        let _ = enc.encode_pure(expr);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new_with_quantifiers();
            let _ = enc.encode_pure(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new_with_quantifiers();
            let _ = enc.encode_pure(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median_ratio = ratios[rounds / 2];

    // The late-pair builder forces near-worst-case pair search, so 80/20
    // candidates should land near the 16x quadratic bound.
    assert!(
        median_ratio < 20.0,
        "Trigger synthesis late-pair scaling ratio ({large_n}/{small_n}) = \
         {median_ratio:.1}x (rounds: {ratios:.1?}). \
         Expected ~16x for the forced O(C²) path. If > 20x, pair search likely \
         regressed beyond quadratic."
    );

    eprintln!(
        "trigger_synthesis_late_pair_search: median ratio={median_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (forced late-pair path, O(C²) expect ~16x)"
    );
}

#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_synthesize_triggers_many_vars_scaling() {
    // Test with increasing variable count while keeping both sides on the same
    // full-scan fallback path. Using 3 vars vs 8 vars ensures no candidate pair
    // can cover all vars in either case.
    let small_v = 3;
    let large_v = 8;

    let small_vars: Vec<String> = (0..small_v).map(|i| format!("v_{i}")).collect();
    let large_vars: Vec<String> = (0..large_v).map(|i| format!("v_{i}")).collect();

    // 40 candidates, each covering one variable
    let n = 40;
    let small_body = build_body_with_n_logic_fn_calls(n, &small_vars);
    let large_body = build_body_with_n_logic_fn_calls(n, &large_vars);

    // Warmup
    for _ in 0..100 {
        let _ = synthesize_triggers(&small_vars, &small_body);
        let _ = synthesize_triggers(&large_vars, &large_body);
    }

    let rounds = 5;
    let iters = 1000;
    let mut ratios = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = synthesize_triggers(&small_vars, &small_body);
        }
        let small_time = start.elapsed();

        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = synthesize_triggers(&large_vars, &large_body);
        }
        let large_time = start.elapsed();

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    // Both have 40 candidates, so pair search is same O(40^2). The variable
    // count affects HashSet construction in coverage checks. Should be modest.
    assert!(
        median < 10.0,
        "synthesize_triggers var count scaling ({large_v}/{small_v} vars) \
         median={median:.1}x. With same candidate count, variable count \
         should have modest impact on pair search time."
    );

    eprintln!(
        "synthesize_triggers var count: median={median:.1}x \
         ({small_v}->{large_v} vars, {n} candidates)"
    );
}
