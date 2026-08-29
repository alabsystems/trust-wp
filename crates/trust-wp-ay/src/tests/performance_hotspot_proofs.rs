// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Additional performance-proof tests for #901 hotspots.
//!
//! Keeps focused scaling proofs separate from the large `performance_proofs.rs`
//! module so they can be staged independently in a shared dirty worktree.

use std::{collections::HashSet, sync::Arc, time::Instant};

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult, Sort};
use ntest::timeout;
use serial_test::serial;
use trust_wp_core::formula::ExprSort;

use super::{
    super::{AYEncoder, PureExpr},
    helpers::*,
};

fn synthetic_datatype(encoder_idx: usize, datatype_idx: usize) -> DatatypeSort {
    DatatypeSort {
        name: format!("PerfLookupDt_{encoder_idx}_{datatype_idx}"),
        constructors: vec![
            DatatypeConstructor {
                name: format!("PerfLookupNone_{encoder_idx}_{datatype_idx}"),
                fields: vec![],
            },
            DatatypeConstructor {
                name: format!("PerfLookupSome_{encoder_idx}_{datatype_idx}"),
                fields: vec![DatatypeField {
                    name: format!("value_{encoder_idx}_{datatype_idx}"),
                    sort: Sort::Int,
                }],
            },
        ],
    }
}

fn run_constructor_lookup_benchmark(
    datatype_count: usize,
    encoder_count: usize,
    lookups_per_encoder: usize,
) -> std::time::Duration {
    // Pre-build encoders and datatype declarations outside timed section to
    // isolate constructor_datatype lookup cost from declaration overhead.
    let mut encoders = Vec::with_capacity(encoder_count);
    for encoder_idx in 0..encoder_count {
        let mut encoder = AYEncoder::new();
        for datatype_idx in 0..datatype_count {
            let dt = synthetic_datatype(encoder_idx, datatype_idx);
            encoder.ensure_datatype_declared(&dt);
        }
        encoders.push(encoder);
    }

    let start = Instant::now();
    for encoder in &mut encoders {
        for _ in 0..lookups_per_encoder {
            assert!(
                encoder
                    .constructor_datatype("__definitely_missing_constructor__")
                    .is_none(),
                "missing constructor unexpectedly resolved during lookup benchmark"
            );
        }
    }
    start.elapsed()
}

/// Proves that non-constructor lookup in `constructor_datatype` scales at most
/// linearly in the number of declared datatypes.
///
/// This targets the `for dt in declared_datatypes.values()` scan in
/// `match_enc.rs::constructor_datatype` under a many-datatype workload.
#[test]
#[timeout(30000)]
fn test_constructor_lookup_many_datatypes_scaling() {
    let small_d = 8;
    let large_d = 40;
    let encoder_count = 20;
    let lookups_per_encoder = 128;
    let rounds = 3;

    // Warm up both sizes.
    let _ = run_constructor_lookup_benchmark(small_d, encoder_count, lookups_per_encoder);
    let _ = run_constructor_lookup_benchmark(large_d, encoder_count, lookups_per_encoder);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time =
            run_constructor_lookup_benchmark(small_d, encoder_count, lookups_per_encoder);
        let large_time =
            run_constructor_lookup_benchmark(large_d, encoder_count, lookups_per_encoder);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum-of-rounds (not median) for resilience to system load
    // spikes during multi-worker execution. Follows #2023 fix pattern.
    let min_ratio = ratios[0];

    // For O(D): ratio(40/8) ~= 5x. For O(D²): ratio ~= 25x.
    // Threshold 14x catches superlinear regression while allowing runtime variance.
    assert!(
        min_ratio < 14.0,
        "constructor_datatype lookup scaling ({large_d}/{small_d}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 14x, lookup likely regressed to superlinear in datatype count."
    );

    eprintln!(
        "constructor_lookup_many_datatypes: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(D) expect ~5x for D={small_d}→{large_d})"
    );
}

fn build_forall_bool_or(n: usize) -> PureExpr {
    let mut body = bool_expr(false);
    for i in 0..n {
        body = or(body, var(&format!("b_{i}")));
    }
    for i in (0..n).rev() {
        body = PureExpr::Forall {
            var: format!("b_{i}"),
            var_sort: Some(ExprSort::Bool),
            body: Arc::new(body),
            triggers: vec![],
        };
    }
    body
}

fn run_forall_bool_cartesian(n: usize, iters: usize) -> std::time::Duration {
    let expr = build_forall_bool_or(n);
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = AYEncoder::new();
        let term = encoder.encode_pure(&expr).unwrap_or_else(|err| {
            panic!("forall bool-or should encode (n={n}, iter={iter}): {err}")
        });
        encoder.assert_term(term);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "forall bool-or should be Unsat for n={n} (all-false branch violates body), got {result:?}"
        );
    }
    start.elapsed()
}

/// Proves cartesian-product Bool quantifier expansion remains bounded and
/// semantically complete on a non-tautological formula.
///
/// `forall b_0..b_n. (b_0 || ... || b_n)` is false because the all-false
/// valuation violates the body; if Bool expansion misses that branch, this
/// test would incorrectly pass as SAT.
#[test]
#[timeout(30000)]
fn test_bool_quantifier_cartesian_scaling_non_tautology() {
    let small_n = 2; // 4 valuations
    let large_n = 4; // 16 valuations (expansion cap)
    let rounds = 3;
    let iters = 40;

    // Warm up both sizes.
    let _ = run_forall_bool_cartesian(small_n, iters);
    let _ = run_forall_bool_cartesian(large_n, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_forall_bool_cartesian(small_n, iters);
        let large_time = run_forall_bool_cartesian(large_n, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum-of-rounds (not median) for resilience to system load
    // spikes during multi-worker execution. Follows #2023 fix pattern.
    let min_ratio = ratios[0];

    // For pure cartesian expansion: ratio(16/4) ~= 4x.
    // Threshold 12x catches superlinear blowups in branch encoding/solving.
    assert!(
        min_ratio < 12.0,
        "bool cartesian expansion scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 12x, bool quantifier expansion likely regressed."
    );

    eprintln!(
        "bool_cartesian_non_tautology: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(2^N) expect ~4x for N={small_n}→{large_n})"
    );
}

fn build_forced_collision_recheck_encoder(
    n_sets: usize,
    terms_per_left: usize,
    prefix: &str,
) -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();

    for set_idx in 0..n_sets {
        let mut left_terms = Vec::with_capacity(terms_per_left);
        for term_idx in 0..terms_per_left {
            let term = encoder
                .get_or_declare_var(&format!("{prefix}_l{set_idx}_{term_idx}"), Sort::Bool)
                .expect("left term declaration should succeed");
            // Force model collisions deterministically.
            encoder.assert_term(term);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(term);
            left_terms.push(term);
        }

        let right = encoder
            .get_or_declare_var(&format!("{prefix}_r{set_idx}"), Sort::Bool)
            .expect("right term declaration should succeed");
        // Force model collisions deterministically.
        encoder.assert_term(right);
        encoder
            .assertion_pipeline_mut_for_test()
            .insert_disjoint_term_for_test(right);

        encoder
            .assertion_pipeline_mut_for_test()
            .push_active_disjoint_constraint_for_test(left_terms, vec![right]);
    }

    // Force one semantic-overlap recheck pass on next check_sat call.
    encoder
        .assertion_pipeline_mut_for_test()
        .set_quantified_pairs_revision_for_test(0);
    encoder
}

fn run_forced_collision_recheck(
    n_sets: usize,
    terms_per_left: usize,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = build_forced_collision_recheck_encoder(
            n_sets,
            terms_per_left,
            &format!("__hs_recheck_{iter}"),
        );
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "forced-collision recheck should be Unsat, got {result:?}"
        );
    }
    start.elapsed()
}

fn build_dense_all_pairs_recheck_encoder(n_vars: usize, prefix: &str) -> AYEncoder {
    assert!(n_vars > 2, "n_vars must be > 2 for dense all-pairs recheck");

    let mut encoder = AYEncoder::new_with_quantifiers();
    let vars: Vec<_> = (0..n_vars)
        .map(|idx| {
            encoder
                .get_or_declare_var(&format!("{prefix}_v{idx}"), Sort::Bool)
                .expect("bool variable declaration should succeed")
        })
        .collect();

    // Force every variable to `true` so each quantified pair collides.
    for &var in &vars {
        encoder.solver.assert_term(var);
        encoder
            .assertion_pipeline_mut_for_test()
            .insert_disjoint_term_for_test(var);
    }

    for i in 0..n_vars {
        for j in (i + 1)..n_vars {
            encoder
                .assertion_pipeline_mut_for_test()
                .push_active_disjoint_constraint_for_test(vec![vars[i]], vec![vars[j]]);
        }
    }

    // Trigger one recheck pass on the next SAT query.
    encoder
        .assertion_pipeline_mut_for_test()
        .prime_recheck_for_test();
    encoder
}

fn run_dense_all_pairs_recheck(n_vars: usize, iters: usize) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder =
            build_dense_all_pairs_recheck_encoder(n_vars, &format!("__hs_dense_{iter}"));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "dense all-pairs recheck must not return Sat, got {result:?}"
        );

        let expected_pairs = n_vars.saturating_mul(n_vars.saturating_sub(1)) / 2;
        let actual_pairs = encoder
            .assertion_pipeline_for_test()
            .asserted_neq_pairs_len();
        assert_eq!(
            actual_pairs, expected_pairs,
            "dense all-pairs setup should materialize every pair as neq"
        );
    }
    start.elapsed()
}

/// Proves the quantified-disjoint recheck path remains bounded with many active
/// constraint sets under deterministic forced collisions.
///
/// Re: #901 — solver refinement loop scaling with many quantified constraints.
#[test]
#[timeout(30000)]
fn test_recheck_many_constraint_sets_scaling_hotspot() {
    let small_sets = 8;
    let large_sets = 32;
    let terms_per_left = 4;
    let rounds = 3;
    let iters = 12;

    // Warm both sizes.
    let _ = run_forced_collision_recheck(small_sets, terms_per_left, iters);
    let _ = run_forced_collision_recheck(large_sets, terms_per_left, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_forced_collision_recheck(small_sets, terms_per_left, iters);
        let large_time = run_forced_collision_recheck(large_sets, terms_per_left, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum-of-rounds (not median) for resilience to system load
    // spikes during multi-worker execution. Follows #2023 fix pattern.
    let min_ratio = ratios[0];

    // O(C): ratio(32/8) ~= 4x. Threshold 16x catches strong superlinear regressions.
    assert!(
        min_ratio < 16.0,
        "recheck many-set scaling ({large_sets}/{small_sets}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 16x, recheck likely regressed to superlinear in set count."
    );

    eprintln!(
        "hotspot_recheck_many_sets: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(C) expect ~4x for sets={small_sets}->{large_sets})"
    );
}

/// Proves high-cardinality `check_sat` recheck remains bounded when quantified
/// disjoint constraints form a dense all-pairs graph.
///
/// This stresses the many-constraint lane directly: with `n` Bool vars fixed
/// to the same value, every one of C(n,2) quantified pairs collides and must be
/// materialized during recheck.
///
/// Re: #901 — high-cardinality check_sat with many quantified constraints.
#[test]
#[timeout(60000)]
#[serial(perf)]
fn test_recheck_dense_all_pairs_high_cardinality_scaling_hotspot() {
    let small_n = 8; // C(8,2)=28 pairs
    let large_n = 14; // C(14,2)=91 pairs
    let rounds = 3;
    let iters = 5;

    // Warm both sizes.
    let _ = run_dense_all_pairs_recheck(small_n, iters);
    let _ = run_dense_all_pairs_recheck(large_n, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_dense_all_pairs_recheck(small_n, iters);
        let large_time = run_dense_all_pairs_recheck(large_n, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum-of-rounds (not median) for resilience to system load
    // spikes during multi-worker execution. Follows #2023 fix pattern.
    let min_ratio = ratios[0];

    // Pair count ratio is 91/28 ~= 3.25x. Threshold 12x catches superlinear blowups.
    assert!(
        min_ratio < 12.0,
        "dense all-pairs recheck scaling (n={large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). If > 12x, high-cardinality recheck likely regressed."
    );

    eprintln!(
        "hotspot_recheck_dense_all_pairs: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (pairs: C({small_n},2)=28 -> C({large_n},2)=91, expected near 3.25x)"
    );
}

fn build_sparse_collision_recheck_encoder(
    n_sets: usize,
    left_terms_per_set: usize,
    right_terms_per_set: usize,
    prefix: &str,
) -> AYEncoder {
    assert!(left_terms_per_set > 0, "left_terms_per_set must be > 0");
    assert!(right_terms_per_set > 0, "right_terms_per_set must be > 0");

    let mut encoder = AYEncoder::new_with_quantifiers();

    for set_idx in 0..n_sets {
        let base = i64::try_from(set_idx).expect("set_idx should fit i64") * 10_000;

        let mut left_terms = Vec::with_capacity(left_terms_per_set);
        for left_idx in 0..left_terms_per_set {
            let left = encoder
                .get_or_declare_var(&format!("{prefix}_s{set_idx}_l{left_idx}"), Sort::Int)
                .expect("left term declaration should succeed");
            let left_val = base + i64::try_from(left_idx).expect("left_idx should fit i64");
            let left_const = encoder.solver.int_const(left_val);
            let left_eq = encoder.solver.eq(left, left_const);
            encoder.solver.assert_term(left_eq);
            left_terms.push(left);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(left);
        }

        let mut right_terms = Vec::with_capacity(right_terms_per_set);
        for right_idx in 0..right_terms_per_set {
            let right = encoder
                .get_or_declare_var(&format!("{prefix}_s{set_idx}_r{right_idx}"), Sort::Int)
                .expect("right term declaration should succeed");

            // Exactly one collision per set: right_0 shares left_0's value.
            let right_val = if right_idx == 0 {
                base
            } else {
                base + 5_000 + i64::try_from(right_idx).expect("right_idx should fit i64")
            };
            let right_const = encoder.solver.int_const(right_val);
            let right_eq = encoder.solver.eq(right, right_const);
            encoder.solver.assert_term(right_eq);
            right_terms.push(right);
            encoder
                .assertion_pipeline_mut_for_test()
                .insert_disjoint_term_for_test(right);
        }

        encoder
            .assertion_pipeline_mut_for_test()
            .push_active_disjoint_constraint_for_test(left_terms, right_terms);
    }

    // Force the recheck loop to run on the next check_sat call.
    encoder
        .assertion_pipeline_mut_for_test()
        .prime_recheck_for_test();
    encoder
}

fn run_sparse_collision_recheck(
    n_sets: usize,
    left_terms_per_set: usize,
    right_terms_per_set: usize,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = build_sparse_collision_recheck_encoder(
            n_sets,
            left_terms_per_set,
            right_terms_per_set,
            &format!("__hs_sparse_{iter}"),
        );
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "sparse-collision recheck should be Unsat, got {result:?}"
        );
        let pair_count = encoder
            .assertion_pipeline_for_test()
            .asserted_neq_pairs_len();
        assert_eq!(
            pair_count, n_sets,
            "sparse-collision setup should materialize exactly one neq pair per set"
        );
    }
    start.elapsed()
}

/// Proves the recheck loop scales with right-term count when collisions remain
/// sparse (one collision per set).
///
/// This isolates the `R` dimension of `O(L+R)` value-indexed collision
/// detection by keeping `L` and collision cardinality fixed.
///
/// Re: #901 — solver refinement loop scaling in right-term dimension
#[test]
#[timeout(60000)]
#[serial(perf)]
fn test_recheck_sparse_collision_right_term_scaling_hotspot() {
    let n_sets = 10;
    let left_terms_per_set = 6;
    let small_right = 3;
    let large_right = 12;
    let rounds = 3;
    let iters = 4;

    // Warm both sizes.
    let _ = run_sparse_collision_recheck(n_sets, left_terms_per_set, small_right, iters);
    let _ = run_sparse_collision_recheck(n_sets, left_terms_per_set, large_right, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time =
            run_sparse_collision_recheck(n_sets, left_terms_per_set, small_right, iters);
        let large_time =
            run_sparse_collision_recheck(n_sets, left_terms_per_set, large_right, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum-of-rounds (not median) for resilience to system load
    // spikes during multi-worker execution. Follows #2023 fix pattern.
    let min_ratio = ratios[0];

    // With fixed L and one collision per set, scaling should be near linear in R:
    // (L+R_large)/(L+R_small) = (6+12)/(6+3) = 2.0x.
    // Threshold 8x catches strong superlinear regressions.
    assert!(
        min_ratio < 8.0,
        "sparse-collision recheck right-term scaling ({large_right}/{small_right}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 8x, right-term collision detection likely regressed to superlinear."
    );

    eprintln!(
        "hotspot_recheck_sparse_right_terms: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (fixed sets={n_sets}, L={left_terms_per_set}, one collision/set, \
          expected near linear in R={small_right}->{large_right})"
    );
}

fn closure_res_state_sort(iter: usize, closure_idx: usize, variant_idx: usize) -> Sort {
    match variant_idx {
        // variant 0: res_state matches self sort (identity matching). (#1997)
        0 => Sort::Uninterpreted(format!("ClosureEnv_Hotspot_{iter}_{closure_idx}")),
        // Non-identity variants: use ClosureEnv_ prefix with distinct names so
        // production closure_sort_tag produces unique "c..." tags and the
        // Strategy B identity check properly rejects them. (#1997, cb2f4e70)
        _ => Sort::Uninterpreted(format!(
            "ClosureEnv_HotspotState_{iter}_{closure_idx}_{variant_idx}"
        )),
    }
}

fn closure_once_sorts(iter: usize, closure_idx: usize, arity: usize) -> Vec<Sort> {
    assert!(arity > 0, "closure arity must be > 0");
    let mut once_sorts = Vec::with_capacity(arity);
    once_sorts.push(Sort::Uninterpreted(format!(
        "ClosureEnv_Hotspot_{iter}_{closure_idx}"
    )));
    for _ in 1..arity {
        once_sorts.push(Sort::Int);
    }
    once_sorts
}

fn closure_mut_sorts_with_res_state(once_sorts: &[Sort], res_state_sort: Sort) -> Vec<Sort> {
    let mut mut_sorts = once_sorts.to_vec();
    let insert_pos = once_sorts
        .len()
        .checked_sub(1)
        .expect("closure arity must be > 0");
    mut_sorts.insert(insert_pos, res_state_sort);
    mut_sorts
}

fn register_closure_symbols_for_hotspot_benchmark(
    encoder: &mut AYEncoder,
    n_closures: usize,
    matching_symbols: usize,
    arity: usize,
    iter: usize,
) -> usize {
    let mut expected_witnesses = HashSet::new();

    for closure_idx in 0..n_closures {
        let once_sorts = closure_once_sorts(iter, closure_idx, arity);
        let once_sig = closure_sort_signature(&once_sorts);
        let once_name = format!("closure_postcondition_once_{arity}_{once_sig}");
        let once_decl = encoder
            .solver
            .declare_fun(&once_name, &once_sorts, Sort::Bool);
        encoder
            .decls_for_test_mut()
            .insert_logic_func(once_name, once_decl);

        let self_tag = closure_sort_tag(&once_sorts[0]);

        for variant_idx in 0..matching_symbols {
            let res_state_sort = closure_res_state_sort(iter, closure_idx, variant_idx);
            let res_state_tag = closure_sort_tag(&res_state_sort);
            let mut_sorts = closure_mut_sorts_with_res_state(&once_sorts, res_state_sort);
            let mut_sig = closure_sort_signature(&mut_sorts);
            let mut_name = format!("closure_postcondition_mut_{}_{mut_sig}", arity + 1);
            let mut_decl = encoder
                .solver
                .declare_fun(&mut_name, &mut_sorts, Sort::Bool);
            encoder
                .decls_for_test_mut()
                .insert_logic_func(mut_name, mut_decl);

            // Strategy B (#1997): only identity-matching variants (res_state
            // tag == self tag) produce witnesses. Non-identity closure-env
            // variants are rejected by the starts_with('c') guard.
            if res_state_tag == self_tag {
                let witness = if res_state_tag == "i" {
                    format!("fn_mut_once_witness_{arity}_{once_sig}")
                } else {
                    format!("fn_mut_once_witness_{arity}_{once_sig}_{res_state_tag}")
                };
                expected_witnesses.insert(witness);
            }
        }
    }

    expected_witnesses.len()
}

fn measure_closure_witness_binding_cross_product(
    n_closures: usize,
    matching_symbols: usize,
    arity: usize,
    iters: usize,
) -> std::time::Duration {
    let start = Instant::now();
    for iter in 0..iters {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        let expected = register_closure_symbols_for_hotspot_benchmark(
            &mut encoder,
            n_closures,
            matching_symbols,
            arity,
            iter,
        );
        encoder.assert_fn_mut_once_law();

        let actual_witnesses = encoder
            .decls()
            .logic_func_names()
            .filter(|name| name.starts_with("fn_mut_once_witness_"))
            .count();
        assert_eq!(
            actual_witnesses, expected,
            "expected one witness symbol per compatible once/mut pair"
        );
    }
    start.elapsed()
}

/// Proves fn_mut_once witness binding scales with the S×M cross product
/// (closure signatures × matching mut signatures) at fixed arity.
///
/// Re: #901 — axiom witness binding O(S×M×arity) scaling.
#[test]
#[timeout(60000)]
fn test_fn_mut_once_witness_binding_cross_product_scaling_hotspot() {
    let arity = 3;
    let small_s = 2;
    let large_s = 6;
    let small_m = 2;
    let large_m = 6;
    let rounds = 3;
    let iters = 10;

    let _ = measure_closure_witness_binding_cross_product(small_s, small_m, arity, iters);
    let _ = measure_closure_witness_binding_cross_product(large_s, large_m, arity, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time =
            measure_closure_witness_binding_cross_product(small_s, small_m, arity, iters);
        let large_time =
            measure_closure_witness_binding_cross_product(large_s, large_m, arity, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    // Use minimum-of-rounds (not median) for resilience to system load
    // spikes during multi-worker execution. Follows #2023 fix pattern.
    let min_ratio = ratios[0];

    let small_work = small_s * small_m;
    let large_work = large_s * large_m;
    let expected_ratio = {
        let large_work_u32 =
            u32::try_from(large_work).expect("large cross-product work should fit u32");
        let small_work_u32 =
            u32::try_from(small_work).expect("small cross-product work should fit u32");
        f64::from(large_work_u32) / f64::from(small_work_u32)
    }; // 9x

    // Threshold allows solver/runtime variance while catching strong superlinear growth.
    assert!(
        min_ratio < 30.0,
        "witness binding cross-product scaling ((S×M)={large_work}/{small_work}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). If > 30x, binding likely regressed \
         above O(S×M×arity)."
    );

    eprintln!(
        "hotspot_witness_cross_product: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (fixed arity={arity}, expected ~{expected_ratio:.1}x for S×M={small_work}->{large_work})"
    );
}
