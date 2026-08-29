// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantified constraint scaling and combined axiom dimension tests.
//!
//! Split from `solver_axiom_scaling.rs` (#901) to stay under the 1000-line
//! file size limit. Tests here exercise cross-cutting scaling properties:
//!
//! 1. **Quantified + recheck interaction** — validates that quantified forall
//!    constraints combined with Bool disjoint constraints don't cause
//!    superlinear blowup in the recheck pipeline.
//!
//! 2. **Combined S×M×arity axiom scaling** — validates that closure axiom
//!    assertion scales as O(S×M×arity) when all three dimensions grow together.

use std::{sync::Arc, time::Instant};

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use serial_test::serial;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{super::AYEncoder, helpers::closure_sort_signature};

// ---------------------------------------------------------------------------
// 1. Solver refinement loop with quantified constraints at scale
// ---------------------------------------------------------------------------

/// Measures time to run check_sat with N quantified forall constraints combined
/// with K disjoint constraint sets. This tests the interaction between quantifier
/// processing overhead and the recheck loop — a dimension the pure-Bool tests
/// in `solver_axiom_scaling.rs` don't cover.
///
/// The quantified constraints are triggered tautologies:
///   forall x. (trigger: f(x)) => f(x) implies f(x)
/// and the disjoint constraints create satisfiable Bool disequalities that
/// force the recheck loop to fire without relying on an incomplete quantified
/// unsat proof.
fn build_quantified_recheck_encoder(
    n_quantifiers: usize,
    n_disjoint_vars: usize,
    prefix: &str,
) -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode N independent quantified forall constraints via encode_pure.
    // Each uses a triggered Bool UF tautology: forall x. f(x) implies f(x).
    // This keeps the workload quantified while preserving a strict Sat result.
    for i in 0..n_quantifiers {
        let fn_name = format!("{prefix}_qf_{i}");
        let var_name = format!("{prefix}_qv_{i}");

        let fn_call = PureExpr::LogicFnCall {
            name: fn_name,
            args: vec![PureExpr::Var(var_name.clone(), None)],
        };
        let body = PureExpr::BinOp(
            Arc::new(fn_call.clone()),
            BinOp::Implies,
            Arc::new(fn_call.clone()),
        );
        let quantified = PureExpr::Forall {
            var: var_name,
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![vec![fn_call]],
        };
        let term = encoder
            .encode_pure(&quantified)
            .unwrap_or_else(|err| panic!("forall {i} should encode: {err:?}"));
        encoder.assert_term(term);
    }

    // Add Bool disjoint constraints to trigger the recheck loop.
    let vars: Vec<_> = (0..n_disjoint_vars)
        .map(|i| {
            encoder
                .get_or_declare_var(&format!("{prefix}_db_{i}"), Sort::Bool)
                .expect("bool var")
        })
        .collect();
    for i in 0..n_disjoint_vars {
        for j in (i + 1)..n_disjoint_vars {
            encoder
                .assertion_pipeline_mut_for_test()
                .push_active_disjoint_constraint_for_test(vec![vars[i]], vec![vars[j]]);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(vars[i]);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(vars[j]);
        }
    }
    let revision = encoder
        .assertion_pipeline_for_test()
        .assertion_revision()
        .max(1);
    encoder
        .assertion_pipeline_mut_for_test()
        .set_assertion_revision_for_test(revision);
    encoder
        .assertion_pipeline_mut_for_test()
        .set_quantified_pairs_revision_for_test(0);
    encoder
}

fn measure_quantified_recheck_time(
    n_quantifiers: usize,
    n_disjoint_vars: usize,
    prefix: &str,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for i in 0..iters {
        let mut encoder = build_quantified_recheck_encoder(
            n_quantifiers,
            n_disjoint_vars,
            &format!("{prefix}_{i}"),
        );
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "quantified recheck workload should remain Sat for n_q={n_quantifiers}, \
             n_d={n_disjoint_vars}, iter={i}; got {result:?}"
        );
    }
    start.elapsed()
}

/// Proves that adding quantified forall constraints to the recheck pipeline
/// does not cause superlinear blowup. Doubling quantifier count from 4 to 16
/// should scale roughly linearly in quantifier encoding overhead, while the
/// recheck loop overhead (dominated by Bool disjoint constraints) stays fixed.
///
/// Re: #901 — solver refinement loop scaling with quantified constraints
#[test]
#[timeout(60000)]
#[serial(scaling)]
fn test_recheck_loop_scales_with_quantified_constraint_count() {
    let small_q = 4;
    let large_q = 16;
    let disjoint_vars = 2; // one satisfiable disjoint pair still triggers recheck
    let rounds = 5;
    let iters = 12;

    // Warm up.
    let _ = measure_quantified_recheck_time(small_q, disjoint_vars, "__qrc_warm_s", iters);
    let _ = measure_quantified_recheck_time(large_q, disjoint_vars, "__qrc_warm_l", iters);

    let mut ratios = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let small_time = measure_quantified_recheck_time(
            small_q,
            disjoint_vars,
            &format!("__qrc{round}s"),
            iters,
        );
        let large_time = measure_quantified_recheck_time(
            large_q,
            disjoint_vars,
            &format!("__qrc{round}l"),
            iters,
        );
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // Quantifier encoding is O(Q). Recheck overhead is O(D²) but D is fixed.
    // Total: O(Q + D²) ≈ O(Q) for this test. Ratio(16/4) ~= 4x.
    // Observed: ~3.1x min. Threshold 8x catches superlinear interaction
    // while allowing 2x headroom over observed peak (~3.4x).
    assert!(
        min_ratio < 8.0,
        "quantified recheck loop scaling ({large_q}/{small_q}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 8x, quantifier encoding has superlinear \
         interaction with the recheck pipeline."
    );

    eprintln!(
        "quantified_recheck_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(Q) expect ~4x for Q={small_q}->{large_q}, D={disjoint_vars} fixed)"
    );
}

// ---------------------------------------------------------------------------
// 2. Combined S×M×arity axiom witness binding scaling
// ---------------------------------------------------------------------------

fn closure_once_and_mut_sorts(
    arity: usize,
    iter: usize,
    closure_idx: usize,
) -> (Vec<Sort>, Vec<Sort>) {
    assert!(
        arity > 0,
        "closure benchmark arity must be greater than zero"
    );

    let mut once_sorts = Vec::with_capacity(arity);
    once_sorts.push(Sort::Uninterpreted(format!(
        "ClosureEnv_Bench_{iter}_{closure_idx}"
    )));
    for _ in 1..arity {
        once_sorts.push(Sort::Int);
    }

    let mut mut_sorts = once_sorts.clone();
    // res_state has the same sort as self (the closure env type). (#1997)
    mut_sorts.insert(arity - 1, once_sorts[0].clone());
    (once_sorts, mut_sorts)
}

fn closure_mut_sorts_with_state(once_sorts: &[Sort], res_state_sort: Sort) -> Vec<Sort> {
    let mut mut_sorts = once_sorts.to_vec();
    let insert_pos = once_sorts
        .len()
        .checked_sub(1)
        .expect("closure arity must be > 0");
    mut_sorts.insert(insert_pos, res_state_sort);
    mut_sorts
}

fn closure_benchmark_state_sort(iter: usize, closure_idx: usize, variant_idx: usize) -> Sort {
    match variant_idx {
        // variant 0: res_state matches self sort (identity matching). (#1997)
        0 => Sort::Uninterpreted(format!("ClosureEnv_Bench_{iter}_{closure_idx}")),
        // Non-identity variants: use ClosureEnv_ prefix so production
        // closure_sort_tag produces unique "c..." tags and the Strategy B
        // identity check properly rejects them. (#1997, cb2f4e70)
        _ => Sort::Uninterpreted(format!(
            "ClosureEnv_BenchState_{iter}_{closure_idx}_{variant_idx}"
        )),
    }
}

fn measure_closure_axiom_matching_symbol_time(
    n_closures: usize,
    matching_symbols: usize,
    arity: usize,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();

        for closure_idx in 0..n_closures {
            let (once_sorts, _) = closure_once_and_mut_sorts(arity, iter, closure_idx);
            let once_name = format!(
                "closure_postcondition_once_{arity}_{}",
                closure_sort_signature(&once_sorts)
            );
            let once_decl = encoder
                .solver
                .declare_fun(&once_name, &once_sorts, Sort::Bool);
            encoder
                .decls_for_test_mut()
                .insert_logic_func(once_name, once_decl);

            for variant_idx in 0..matching_symbols {
                let res_state_sort = closure_benchmark_state_sort(iter, closure_idx, variant_idx);
                let mut_sorts = closure_mut_sorts_with_state(&once_sorts, res_state_sort);
                let mut_name = format!(
                    "closure_postcondition_mut_{}_{mut_sig}",
                    arity + 1,
                    mut_sig = closure_sort_signature(&mut_sorts)
                );
                let mut_decl = encoder
                    .solver
                    .declare_fun(&mut_name, &mut_sorts, Sort::Bool);
                encoder
                    .decls_for_test_mut()
                    .insert_logic_func(mut_name, mut_decl);
            }
        }

        encoder.assert_fn_mut_once_law();
        let witness_count = encoder
            .decls()
            .logic_func_names()
            .filter(|name| name.starts_with("fn_mut_once_witness_"))
            .count();
        // Strategy B (#1997): identity-only matching means only variants whose
        // res_state sort matches the self sort produce witnesses.
        assert_eq!(
            witness_count, n_closures,
            "expected one witness per closure (identity-only matching) \
             (closures={n_closures}, matching_symbols={matching_symbols}, \
             arity={arity}, iter={iter})"
        );
    }
    start.elapsed()
}

/// Proves that the combined S×M×arity cost of closure axiom assertion scales
/// as expected: doubling all three dimensions should produce ~8x overhead
/// (2×2×2). Existing tests isolate each dimension; this validates no
/// combinatorial blowup in the cross-product.
///
/// Re: #901 — axiom witness binding O(S×M×arity) combined scaling
#[test]
#[timeout(60000)]
#[serial(scaling)]
fn test_closure_axiom_combined_s_m_arity_scaling() {
    let small_s = 2;
    let small_m = 1;
    let small_a = 2;
    let large_s = 4;
    let large_m = 2;
    let large_a = 4;
    let rounds = 5;
    let iters = 20;

    // Warm up.
    let _ = measure_closure_axiom_matching_symbol_time(small_s, small_m, small_a, iters);
    let _ = measure_closure_axiom_matching_symbol_time(large_s, large_m, large_a, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time =
            measure_closure_axiom_matching_symbol_time(small_s, small_m, small_a, iters);
        let large_time =
            measure_closure_axiom_matching_symbol_time(large_s, large_m, large_a, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(S×M×arity): doubling all three gives 2×2×2 = 8x.
    // Observed: ~4.3x min (sub-linear due to setup overhead dominating
    // at small sizes). Threshold 12x catches combinatorial blowup
    // (e.g., O(S²×M×arity) = 4×2×2 = 16x) while allowing headroom.
    assert!(
        min_ratio < 12.0,
        "combined S×M×arity scaling (S:{large_s}/{small_s}, M:{large_m}/{small_m}, \
         A:{large_a}/{small_a}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ~8x for 2×2×2, observed ~4x. \
         If > 12x, combinatorial blowup in the cross-product."
    );

    eprintln!(
        "closure_axiom_combined: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(S×M×A) expect ~8x for S={small_s}->{large_s}, \
         M={small_m}->{large_m}, A={small_a}->{large_a})"
    );
}
