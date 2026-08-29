// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Solver refinement loop scaling and axiom witness binding scaling tests (#901).
//!
//! 1. **Recheck loop scaling** — O(L+R) per constraint set via value-indexed collision.
//! 2. **Axiom witness binding** — O(S×M×arity) closure spec symbol assertion.
//! 3. **Ground pool instantiation** — O(A×G) respecting `TRUST_WP_CAP_PER_AXIOM`.
//!
//! Sections 4-5 (quantified+recheck, combined S×M×arity) in solver_quantified_scaling.rs.

use std::{sync::Arc, time::Instant};

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use serial_test::serial;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    super::AYEncoder,
    helpers::{closure_sort_signature, closure_sort_tag},
};

#[cfg(ay_performance_proofs)]
mod recheck_loop_scaling;

// 2. Axiom witness binding scaling (closure spec symbols)

/// Measures the time to declare closure spec UFs and assert fn_mut_once laws
/// for `n_closures` closure types, each with `arity` parameters.
///
/// Each closure gets a unique `postcondition_once` and `postcondition_mut`
/// uninterpreted function with a parseable signature recognized by
/// `assert_fn_mut_once_law`. The fn_mut_once law connects them via Skolem
/// witness functions.
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
    // Use ClosureEnv_ prefix to match production closure_sort_tag convention.
    once_sorts.push(Sort::Uninterpreted(format!(
        "ClosureEnv_Bench_{iter}_{closure_idx}"
    )));
    for _ in 1..arity {
        once_sorts.push(Sort::Int);
    }

    let mut mut_sorts = once_sorts.clone();
    // fn_mut_once law expects res_state inserted before the result position.
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
        // identity check (starts_with('c') guard) properly rejects them.
        // (#1997, cb2f4e70)
        _ => Sort::Uninterpreted(format!(
            "ClosureEnv_BenchState_{iter}_{closure_idx}_{variant_idx}"
        )),
    }
}

fn measure_closure_axiom_time(
    n_closures: usize,
    arity: usize,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        for c in 0..n_closures {
            let (once_sorts, mut_sorts) = closure_once_and_mut_sorts(arity, iter, c);
            let once_name = format!(
                "closure_postcondition_once_{arity}_{}",
                closure_sort_signature(&once_sorts)
            );
            let mut_name = format!(
                "closure_postcondition_mut_{}_{mut_sig}",
                arity + 1,
                mut_sig = closure_sort_signature(&mut_sorts)
            );

            // Declare postcondition_once: (receiver, ..., result) -> Bool
            let once_decl = encoder
                .solver
                .declare_fun(&once_name, &once_sorts, Sort::Bool);
            encoder
                .decls_for_test_mut()
                .insert_logic_func(once_name, once_decl);

            // Declare postcondition_mut with res_state inserted before result.
            let mut_decl = encoder
                .solver
                .declare_fun(&mut_name, &mut_sorts, Sort::Bool);
            encoder
                .decls_for_test_mut()
                .insert_logic_func(mut_name, mut_decl);
        }
        // Trigger the full axiom assertion pipeline
        encoder.assert_fn_mut_once_law();
        let witness_count = encoder
            .decls()
            .logic_func_names()
            .filter(|name| name.starts_with("fn_mut_once_witness_"))
            .count();
        assert_eq!(
            witness_count, n_closures,
            "expected one witness per closure (n_closures={n_closures}, arity={arity}, iter={iter})"
        );
    }
    start.elapsed()
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
        // res_state sort matches the self sort produce witnesses. Variant 0
        // matches (see closure_benchmark_state_sort), others are filtered out.
        assert_eq!(
            witness_count,
            n_closures,
            "expected one witness per closure (identity-only matching) \
             (closures={n_closures}, matching_symbols={matching_symbols}, arity={arity}, iter={iter})"
        );
    }
    start.elapsed()
}

/// Regression guard: ensure generated benchmark signatures are parseable by
/// `assert_fn_mut_once_law` and declare the expected witness symbol.
#[test]
#[timeout(30000)]
fn test_closure_axiom_benchmark_signature_declares_witness() {
    let arity = 3;
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let (once_sorts, mut_sorts) = closure_once_and_mut_sorts(arity, 0, 0);

    let once_sig = closure_sort_signature(&once_sorts);
    let once_name = format!("closure_postcondition_once_{arity}_{once_sig}");
    let mut_name = format!(
        "closure_postcondition_mut_{}_{mut_sig}",
        arity + 1,
        mut_sig = closure_sort_signature(&mut_sorts)
    );

    let once_decl = encoder
        .solver
        .declare_fun(&once_name, &once_sorts, Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(once_name, once_decl);
    let mut_decl = encoder
        .solver
        .declare_fun(&mut_name, &mut_sorts, Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(mut_name, mut_decl);

    // With identity-only matching (#1997), res_state sort matches self sort,
    // so the witness name includes the res_state tag suffix.
    let self_tag = closure_sort_tag(&once_sorts[0]);
    let witness_name = if self_tag == "i" {
        format!("fn_mut_once_witness_{arity}_{once_sig}")
    } else {
        format!("fn_mut_once_witness_{arity}_{once_sig}_{self_tag}")
    };
    assert!(
        !encoder.decls().has_logic_func(&witness_name),
        "witness should not exist before fn_mut_once law assertion"
    );

    encoder.assert_fn_mut_once_law();
    assert!(
        encoder.decls().has_logic_func(&witness_name),
        "fn_mut_once law should declare witness symbol `{witness_name}` for parseable signatures"
    );
}

/// Re: #901 — closure axiom assertion should scale linearly in closure count.
#[test]
#[timeout(60000)]
#[serial(scaling)]
fn test_closure_axiom_scales_linearly_in_closure_count() {
    let small_n = 4;
    let large_n = 16;
    let arity = 3;
    let rounds = 5;
    let iters = 30;

    // Warm up.
    let _ = measure_closure_axiom_time(small_n, arity, iters);
    let _ = measure_closure_axiom_time(large_n, arity, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_closure_axiom_time(small_n, arity, iters);
        let large_time = measure_closure_axiom_time(large_n, arity, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(n): ratio(16/4) ~= 4x. Threshold 14x catches quadratic regression.
    assert!(
        min_ratio < 14.0,
        "closure axiom scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 14x, axiom assertion likely regressed to quadratic."
    );

    eprintln!(
        "closure_axiom_count: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(n) expect ~4x for n={small_n}->{large_n})"
    );
}

/// Re: #901 — closure axiom assertion should scale linearly in arity.
#[test]
#[timeout(60000)]
#[serial(scaling)]
fn test_closure_axiom_scales_linearly_in_arity() {
    let n_closures = 4;
    let small_a = 3;
    let large_a = 12;
    let rounds = 5;
    let iters = 30;

    // Warm up.
    let _ = measure_closure_axiom_time(n_closures, small_a, iters);
    let _ = measure_closure_axiom_time(n_closures, large_a, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_closure_axiom_time(n_closures, small_a, iters);
        let large_time = measure_closure_axiom_time(n_closures, large_a, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(a): ratio(12/3) ~= 4x. Threshold 14x catches superlinear arity blowup.
    assert!(
        min_ratio < 14.0,
        "closure axiom arity scaling ({large_a}/{small_a}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 14x, axiom construction likely has superlinear arity cost."
    );

    eprintln!(
        "closure_axiom_arity: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(a) expect ~4x for a={small_a}->{large_a})"
    );
}

/// Identity-only matching (#1997): only the variant whose res_state sort
/// matches the self sort produces a witness; others are filtered out.
#[test]
#[timeout(30000)]
fn test_closure_axiom_declares_witness_for_each_matching_signature() {
    let arity = 3;
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let (once_sorts, _) = closure_once_and_mut_sorts(arity, 0, 0);
    let once_sig = closure_sort_signature(&once_sorts);
    let once_name = format!("closure_postcondition_once_{arity}_{once_sig}");
    let once_decl = encoder
        .solver
        .declare_fun(&once_name, &once_sorts, Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(once_name, once_decl);

    let self_tag = closure_sort_tag(&once_sorts[0]);
    for variant_idx in 0..4 {
        let res_state_sort = closure_benchmark_state_sort(0, 0, variant_idx);
        let mut_sorts = closure_mut_sorts_with_state(&once_sorts, res_state_sort);
        let mut_sig = closure_sort_signature(&mut_sorts);
        let mut_name = format!("closure_postcondition_mut_{}_{mut_sig}", arity + 1);
        let mut_decl = encoder
            .solver
            .declare_fun(&mut_name, &mut_sorts, Sort::Bool);
        encoder
            .decls_for_test_mut()
            .insert_logic_func(mut_name, mut_decl);
    }

    encoder.assert_fn_mut_once_law();

    let witness = format!("fn_mut_once_witness_{arity}_{once_sig}_{self_tag}");
    assert!(
        encoder.decls().has_logic_func(&witness),
        "identity-matching witness missing"
    );
    let total = encoder
        .decls()
        .logic_func_names()
        .filter(|n| n.starts_with("fn_mut_once_witness_"))
        .count();
    assert_eq!(
        total, 1,
        "identity-only matching should produce exactly 1 witness, got {total}"
    );
}

/// Assert the reverse fn_mut_once law forces postcondition_mut at the witness value.
fn assert_reverse_law_forces_mut(
    encoder: &mut AYEncoder,
    once_decl: &ay_dpll::api::FuncDecl,
    mut_decl: &ay_dpll::api::FuncDecl,
    witness_decl: &ay_dpll::api::FuncDecl,
    once_sorts: &[Sort],
    variant_idx: usize,
) {
    let arity = once_sorts.len();
    let once_args: Vec<_> = once_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| encoder.solver.fresh_var(&format!("arg_{i}"), sort.clone()))
        .collect();
    let once_term = encoder.solver.apply(once_decl, &once_args);
    encoder.solver.assert_term(once_term);

    let witness_term = encoder.solver.apply(witness_decl, &once_args);
    let mut mut_args: Vec<_> = once_args[..arity - 1].to_vec();
    mut_args.push(witness_term);
    mut_args.push(once_args[arity - 1]);

    let mut_term = encoder.solver.apply(mut_decl, &mut_args);
    let not_mut_term = encoder.solver.not(mut_term);
    encoder.solver.assert_term(not_mut_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "reverse law must force postcondition_mut at witness for variant {variant_idx}, got {result:?}"
    );
}

/// Semantic regression guard: the reverse fn_mut_once law must force
/// postcondition_mut at the witness value for matching variants.
///
/// Strategy B (#1997, cb2f4e70): identity check only applies to closure-env
/// sorts ("c..." tags). Uses ClosureEnv_ self sort to exercise the identity
/// check, with a non-identity ClosureEnv_ variant to test rejection.
#[test]
#[timeout(30000)]
fn test_closure_axiom_reverse_law_enforces_mut_for_each_matching_signature() {
    let arity = 3;
    let self_sort = Sort::Uninterpreted("ClosureEnv_RevLaw_0".to_string());
    let once_sorts = vec![self_sort.clone(), Sort::Int, Sort::Int];
    let once_sig = closure_sort_signature(&once_sorts);

    // Variant 0: identity (self sort) — should produce witness
    // Variant 1: non-identity closure-env — should NOT produce witness
    let variants: Vec<(Sort, bool)> = vec![
        (self_sort.clone(), true),
        (Sort::Uninterpreted("ClosureEnv_Other_0".to_string()), false),
    ];

    for (variant_idx, (res_state_sort, should_match)) in variants.into_iter().enumerate() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
        let res_state_tag = closure_sort_tag(&res_state_sort);
        let mut_sorts = closure_mut_sorts_with_state(&once_sorts, res_state_sort);

        let once_name = format!("closure_postcondition_once_{arity}_{once_sig}");
        let mut_sig = closure_sort_signature(&mut_sorts);
        let mut_name = format!("closure_postcondition_mut_{}_{mut_sig}", arity + 1);

        let once_decl = encoder
            .solver
            .declare_fun(&once_name, &once_sorts, Sort::Bool);
        encoder
            .decls_for_test_mut()
            .insert_logic_func(once_name, once_decl.clone());
        let mut_decl = encoder
            .solver
            .declare_fun(&mut_name, &mut_sorts, Sort::Bool);
        encoder
            .decls_for_test_mut()
            .insert_logic_func(mut_name, mut_decl.clone());

        encoder.assert_fn_mut_once_law();

        let witness_name = if res_state_tag == "i" {
            format!("fn_mut_once_witness_{arity}_{once_sig}")
        } else {
            format!("fn_mut_once_witness_{arity}_{once_sig}_{res_state_tag}")
        };

        if !should_match {
            assert!(
                !encoder.decls().has_logic_func(&witness_name),
                "non-identity closure-env variant {variant_idx} (tag={res_state_tag}) \
                 should NOT produce witness"
            );
            continue;
        }

        let witness_decl = encoder
            .decls()
            .get_logic_func(&witness_name)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "matching variant {variant_idx} (tag={res_state_tag}) should declare \
                     witness `{witness_name}`"
                )
            });
        assert_reverse_law_forces_mut(
            &mut encoder,
            &once_decl,
            &mut_decl,
            &witness_decl,
            &once_sorts,
            variant_idx,
        );
    }
}

/// Proves closure axiom assertion scales linearly in matching `postcondition_mut`
/// symbol count (the M dimension of O(S×M×arity)).
///
/// Re: #901 — axiom witness binding matching-symbol dimension
#[test]
#[timeout(60000)]
#[serial(scaling)]
fn test_closure_axiom_scales_linearly_in_matching_symbols() {
    let n_closures = 6;
    let arity = 3;
    let small_m = 1;
    let large_m = 6;
    let rounds = 5;
    let iters = 30;

    // Warm up.
    let _ = measure_closure_axiom_matching_symbol_time(n_closures, small_m, arity, iters);
    let _ = measure_closure_axiom_matching_symbol_time(n_closures, large_m, arity, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time =
            measure_closure_axiom_matching_symbol_time(n_closures, small_m, arity, iters);
        let large_time =
            measure_closure_axiom_matching_symbol_time(n_closures, large_m, arity, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(M): ratio(6/1) ~= 6x. Threshold 18x catches superlinear regressions.
    assert!(
        min_ratio < 18.0,
        "closure axiom matching-symbol scaling ({large_m}/{small_m}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 18x, axiom assertion likely regressed to superlinear in M."
    );

    eprintln!(
        "closure_axiom_matching_symbols: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(M) expect ~6x for M={small_m}->{large_m})"
    );
}

// 3. Ground pool instantiation scaling

/// Measures time to run ground pool instantiation with `n_axioms` axioms,
/// each having `n_ground_terms` matching ground entries.
fn measure_ground_pool_instantiation(
    n_axioms: usize,
    n_ground_terms: usize,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        let int_sort = Sort::Int;

        for ax_idx in 0..n_axioms {
            let fn_name = format!("logic_fn_gp_{iter}_{ax_idx}");
            let func_decl = encoder.solver.declare_fun(
                &fn_name,
                std::slice::from_ref(&int_sort),
                int_sort.clone(),
            );
            encoder
                .decls_for_test_mut()
                .insert_logic_func(fn_name.clone(), func_decl.clone());

            // Register axiom: forall x. f(x) = x + 1
            encoder.ground_pool_for_test_mut().register_axiom(
                super::super::encoder::ground_pool::AxiomEntry {
                    fn_symbol: fn_name.clone(),
                    params: vec!["x".to_string()],
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                        BinOp::Add,
                        Arc::new(PureExpr::Int(1)),
                    ),
                    requires: vec![],
                    func_decl: func_decl.clone(),
                    return_sort: int_sort.clone(),
                    kind: super::super::encoder::ground_pool::AxiomKind::Defining,
                },
            );

            // Register ground terms
            for gt_idx in 0..n_ground_terms {
                let val = i64::try_from(gt_idx).expect("ground term index fits i64") + 1;
                let arg = encoder.solver.int_const(val);
                let app = encoder.solver.apply(&func_decl, &[arg]);
                encoder.ground_pool_for_test_mut().register(
                    &fn_name,
                    app,
                    vec![arg],
                    vec![PureExpr::Int(val)],
                );
            }
        }

        let count = encoder
            .assert_ground_pool_instances()
            .expect("instantiation should succeed");
        assert_eq!(
            count,
            n_axioms * n_ground_terms,
            "expected {n_axioms} axioms × {n_ground_terms} ground terms = {} instances",
            n_axioms * n_ground_terms
        );
    }
    start.elapsed()
}

/// Proves that ground pool instantiation scales linearly in the number of
/// axiom×ground-term combinations.
///
/// Each instantiation re-encodes one axiom body with ground bindings. The
/// total work should be O(A × G) where A = axiom_count, G = ground_terms.
/// Doubling A should double wall time.
///
/// Re: #901 — ground pool instantiation scaling
#[test]
#[timeout(60000)]
#[serial(scaling)]
fn test_ground_pool_instantiation_scales_linearly() {
    let small_a = 4;
    let large_a = 16;
    let ground_terms = 5;
    let rounds = 5;
    let iters = 30;

    // Warm up.
    let _ = measure_ground_pool_instantiation(small_a, ground_terms, iters);
    let _ = measure_ground_pool_instantiation(large_a, ground_terms, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_ground_pool_instantiation(small_a, ground_terms, iters);
        let large_time = measure_ground_pool_instantiation(large_a, ground_terms, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(A): ratio(16/4) ~= 4x. Threshold 14x catches superlinear regression.
    assert!(
        min_ratio < 14.0,
        "ground pool scaling ({large_a}/{small_a}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 14x, instantiation likely regressed to superlinear."
    );

    eprintln!(
        "ground_pool_instantiation: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(A) expect ~4x for A={small_a}->{large_a})"
    );
}

/// Validates that ground pool instantiation correctly produces solver-checkable
/// instances: after asserting `f(x) = x + 1` for multiple axioms and ground
/// terms, the solver can derive the expected equalities.
///
/// Re: #901 — ground pool instantiation correctness at scale
#[test]
#[timeout(30000)]
fn test_ground_pool_multi_axiom_correctness() {
    let int_sort = Sort::Int;

    // Set up 3 axioms: f(x) = x+1, g(x) = x*2, h(x) = x+10
    let axioms_spec: Vec<(&str, PureExpr)> = vec![
        (
            "logic_fn_gp_f",
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
        ),
        (
            "logic_fn_gp_g",
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Mul,
                Arc::new(PureExpr::Int(2)),
            ),
        ),
        (
            "logic_fn_gp_h",
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(10)),
            ),
        ),
    ];

    // Verify each axiom independently: f(5) = 6, g(5) = 10, h(5) = 15
    let expected_values = [6i64, 10, 15];

    for (idx, &expected) in expected_values.iter().enumerate() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        let fn_name = axioms_spec[idx].0;
        let body = &axioms_spec[idx].1;
        let func_decl =
            encoder
                .solver
                .declare_fun(fn_name, std::slice::from_ref(&int_sort), int_sort.clone());
        encoder
            .decls_for_test_mut()
            .insert_logic_func(fn_name.to_string(), func_decl.clone());

        encoder.ground_pool_for_test_mut().register_axiom(
            super::super::encoder::ground_pool::AxiomEntry {
                fn_symbol: fn_name.to_string(),
                params: vec!["x".to_string()],
                body: body.clone(),
                requires: vec![],
                func_decl: func_decl.clone(),
                return_sort: int_sort.clone(),
                kind: super::super::encoder::ground_pool::AxiomKind::Defining,
            },
        );

        let five = encoder.solver.int_const(5);
        let app = encoder.solver.apply(&func_decl, &[five]);
        encoder.ground_pool_for_test_mut().register(
            fn_name,
            app,
            vec![five],
            vec![PureExpr::Int(5)],
        );

        let count = encoder
            .assert_ground_pool_instances()
            .expect("instantiation should succeed");
        assert_eq!(count, 1, "expected 1 ground instance for {fn_name}");
        let expected_term = encoder.solver.int_const(expected);
        let neq = encoder.solver.neq(app, expected_term);
        encoder.solver.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "{fn_name}(5) should equal {expected} via ground instance"
        );
    }
}
