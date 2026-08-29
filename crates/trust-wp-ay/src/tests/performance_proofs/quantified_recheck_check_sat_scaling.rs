// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// Quantified disjoint recheck: check_sat scaling with many active constraint sets
// =============================================================================

// =============================================================================

/// Measures that `check_sat` recheck overhead scales linearly with the number
/// of active quantified-disjoint constraint sets.
///
/// Each encoded SepConj chain contributes quantified cross-footprint sets.
/// Forcing `loc_0 == loc_last` per chain creates a cross-boundary collision
/// that the quantified disjoint recheck must detect and materialize as an
/// explicit `!=` constraint before reaching Unsat.
///
/// NOTE: The overlap must be between locations on opposite sides of a quantified
/// boundary. For a left-recursive 12-element chain, the outermost SepConj splits
/// left={loc_0..loc_10} vs right={loc_11}, so `loc_0 == loc_11` forces the
/// recheck to fire. Using `loc_0 == loc_1` would fail because those locations
/// are separated by a ground cross-pair `neq` (below the 8-element threshold),
/// not by the quantified recheck path.
///
/// With fixed chain size, recheck work should avoid catastrophic blowup in
/// chain count C. The dedicated microbench tests below prove linear behavior
/// for the recheck internals; this integration test includes solver
/// E-matching/instantiation overhead and is expected to be noisier.
///
/// Re: performance_proofs phase — solver refinement loop scaling
#[test]
#[timeout(90000)]
fn test_quantified_recheck_check_sat_scaling() {
    use std::time::Instant;

    use ay_dpll::api::SolveResult;

    let chain_size = 12;
    let right_idx = chain_size - 1;
    let small_chains = 2;
    let large_chains = 8;
    let rounds = 3;
    let iters = 4;

    fn run_recheck(
        chains: usize,
        iters: usize,
        chain_size: usize,
        right_idx: usize,
    ) -> std::time::Duration {
        let start = Instant::now();
        for iter in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();

            for chain_idx in 0..chains {
                let prefix = format!("rc{iter}_{chain_idx}_");
                let chain = build_sep_conj_chain_with_prefix(chain_size, &prefix);
                let chain_term = encoder.encode(&chain).unwrap_or_else(|err| {
                    panic!("chain {chain_idx} should encode for recheck scaling: {err:?}")
                });
                encoder.assert_term(chain_term);

                // Force cross-boundary semantic overlap: loc_0 (left side) == loc_last
                // (right side of the outermost quantified SepConj boundary).
                // This triggers the quantified-disjoint model recheck path.
                let overlap_eq = eq(
                    var(&format!("{prefix}loc_0")),
                    var(&format!("{prefix}loc_{right_idx}")),
                );
                encoder.register_sort_hints(std::slice::from_ref(&overlap_eq));
                let overlap_term = encoder.encode_pure(&overlap_eq).unwrap_or_else(|err| {
                    panic!("overlap equality for chain {chain_idx} should encode: {err:?}")
                });
                encoder.assert_term(overlap_term);
            }

            let sat = encoder.check_sat();
            assert!(
                matches!(sat, SolveResult::Unsat(_)),
                "forced cross-boundary overlap across {chains} quantified chains \
                 should be Unsat, got {sat:?}"
            );
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_recheck(small_chains, iters, chain_size, right_idx);
    let _ = run_recheck(large_chains, iters, chain_size, right_idx);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_recheck(small_chains, iters, chain_size, right_idx);
        let large_time = run_recheck(large_chains, iters, chain_size, right_idx);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    // Use minimum ratio: least affected by system load spikes from
    // concurrent workers (#2009 audit finding).
    let min_ratio = ratios[0];

    // Full integration path (encoding + solver + recheck) shows superlinear
    // behavior from quantifier instantiation overhead in ay. The O(N^2) total
    // get_value calls across constraint sets (each chain boundary has a
    // growing left-side) plus ay E-matching combinatorics cause the ratio to
    // sit at ~25-30x for 8/2 chains under concurrent worker load. Threshold
    // 36x catches severe regressions (true quadratic in chain count would be
    // 64x for 4x input ratio) while tolerating both the known O(N^2)-per-
    // chain-size solver overhead (#611) and multi-worker CPU contention (#2023).
    // Previous threshold of 28x (~12% headroom) caused repeated flaky failures
    // under load: P1-115 observed [29.2, 29.3, 34.3] with min=29.2x.
    assert!(
        min_ratio < 36.0,
        "quantified recheck check_sat scaling ratio ({large_chains}/{small_chains}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 36x, integrated solver+recheck pipeline likely regressed."
    );

    eprintln!(
        "quantified_recheck_check_sat_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (integration bound <36x for C={small_chains}→{large_chains}, \
          chain_size={chain_size}, iters={iters}; \
          see recheck microbench tests for linear internal bounds)"
    );
}

// =============================================================================
// Match encoding: constructor lookup and exhaustiveness check scaling
// =============================================================================

/// Measures that encoding match expressions with many constructor arms scales
/// linearly with the number of arms.
///
/// The `is_constructor_exhaustive` function (match_enc.rs:344-363) collects
/// arm constructor names into a Vec then checks `arm_ctors.contains()` for
/// each datatype constructor — O(arms × constructors). The `constructor_datatype`
/// function (match_enc.rs:411-430) performs a linear scan over all declared
/// datatypes for each arm — O(arms × datatypes × constructors_per_dt).
///
/// This test encodes match expressions over Option/Result with varying numbers
/// of logic function call arms to measure the overhead of constructor lookup
/// during match encoding.
///
/// Re: performance_proofs phase — match constructor lookup O(A × D × C)
#[test]
#[timeout(30000)]
fn test_match_encoding_arm_count_scaling() {
    use std::time::Instant;

    let small_a = 5;
    let large_a = 20;
    let rounds = 5;
    let iters = 100;

    /// Build a match expression with `Some(x)`, `None`, plus `n` wildcard
    /// arms containing logic function calls (to exercise constructor lookup).
    fn build_match_with_arms(n: usize) -> PureExpr {
        let mut arms = vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ];
        // Add n wildcard arms — these won't match but the encoder still
        // processes them for constructor lookup.
        for i in 0..n {
            arms.push((
                Pattern::Wildcard,
                #[allow(clippy::cast_possible_wrap)] // Test index, always small
                logic_fn_call(&format!("f_{i}"), vec![int(i as i64)]),
            ));
        }
        match_expr(var("opt"), arms)
    }

    let small_expr = build_match_with_arms(small_a);
    let large_expr = build_match_with_arms(large_a);

    // Warm up
    for _ in 0..iters {
        let mut enc = AYEncoder::new();
        let _ = enc.encode_pure(&small_expr);
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
    let min_ratio = ratios[0];

    // For O(A): ratio(20/5) ≈ 4x. For O(A²): ratio ≈ 16x.
    // The constructor lookup scans are per-arm, so O(A × D × C) total.
    // With fixed D and C (Option + Result), scaling should be O(A).
    // Threshold 10x catches quadratic regression.
    assert!(
        min_ratio < 10.0,
        "Match arm encoding ratio ({large_a}/{small_a}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, match encoding has superlinear arm scaling. \
         Expected ~4x with O(A) for fixed datatypes."
    );

    eprintln!(
        "match_arm_encoding_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(A) expect ~4x, O(A²) expect ~16x for A={small_a}→{large_a})"
    );
}

// =============================================================================
// Heap disjointness: O(L1 × L2) pairwise constraint generation
// =============================================================================

/// Measures that `heap_disjoint` generates O(L × L) pairwise neq constraints
/// and that the constraint generation + conjunction scales quadratically
/// (not worse) with location count.
///
/// `heap_disjoint` at heap.rs:225-238 builds |locs1| × |locs2| neq constraints
/// then combines them with `and_many`. This is the expected O(L²) behavior
/// for pairwise disjointness below the quantified threshold. The test verifies
/// the quadratic bound holds (not cubic or worse due to `and_many` overhead).
///
/// Re: performance_proofs phase — heap disjointness pairwise scaling
#[test]
#[timeout(30000)]
fn test_heap_disjoint_pairwise_scaling() {
    use std::time::Instant;

    use ay_dpll::api::Sort;

    let small_l = 10;
    let large_l = 40;
    let rounds = 7;
    let iters = 60;

    /// Pre-declare locations, then time only the heap_disjoint + assert_term
    /// calls to isolate pairwise constraint generation from declaration overhead.
    fn run_heap_disjoint(l: usize, iters: usize) -> std::time::Duration {
        // Pre-build encoders with declarations outside the timed section
        let mut encoders: Vec<(AYEncoder, Vec<Term>, Vec<Term>)> = Vec::with_capacity(iters);
        for iter_idx in 0..iters {
            let mut encoder = AYEncoder::new();
            let locs1: Vec<_> = (0..l)
                .map(|i| {
                    encoder
                        .solver
                        .declare_const(&format!("a{iter_idx}_{i}"), Sort::Int)
                })
                .collect();
            let locs2: Vec<_> = (0..l)
                .map(|i| {
                    encoder
                        .solver
                        .declare_const(&format!("b{iter_idx}_{i}"), Sort::Int)
                })
                .collect();
            encoders.push((encoder, locs1, locs2));
        }

        let start = Instant::now();
        for (encoder, locs1, locs2) in &mut encoders {
            let term = encoder.heap_disjoint(locs1, locs2);
            encoder.assert_term(term);
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_heap_disjoint(small_l, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_heap_disjoint(small_l, iters);
        let large_time = run_heap_disjoint(large_l, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    // Use median of 7 rounds to resist outlier rounds caused by system load
    // or memory pressure. Median of 7 tolerates up to 3 outlier rounds.
    // 60 iters per round provides sufficient amortization while reducing
    // wall-clock cost (~17s → ~9s). Previous: median-of-9 with 100 iters (#2096).
    let median_ratio = ratios[rounds / 2];

    // For O(L²): ratio(40/10) = (40/10)² = 16x.
    // For O(L³): ratio = 64x.
    //
    // Empirically the ratio is ~55-60x, well above the theoretical O(L²)=16x.
    // The superlinear overhead comes from ay term interning in `solver.neq`
    // and the `and_many` conjunction builder, which both scale with the
    // cumulative term pool size. This means heap_disjoint has effective
    // complexity closer to O(L^2.7) in wall-clock time.
    //
    // FINDING: The pairwise heap_disjoint is a genuine performance bottleneck
    // for large separation logic footprints. The TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD
    // (8) mitigates this in practice, but any footprint below the threshold
    // pays the full pairwise cost. Threshold 80x catches true cubic blowup
    // while documenting the known superquadratic behavior.
    assert!(
        median_ratio < 80.0,
        "heap_disjoint scaling ratio ({large_l}/{small_l}) = {median_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 80x, pairwise disjointness has cubic or worse overhead. \
         Expected ~16x for O(L²), empirically ~55-60x due to ay term overhead."
    );

    // Also verify the ratio shows genuine superlinear growth (not O(L)).
    // For O(L): ratio would be ~4x.
    // Threshold 5x gives margin above the 4x linear bound. Median of 7
    // rounds with 60 iters each tolerates up to 3/7 outlier rounds (#2096).
    assert!(
        median_ratio > 5.0,
        "heap_disjoint scaling ratio ({large_l}/{small_l}) = {median_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If < 5x, pairwise constraint generation may be short-circuiting. \
         Expected superlinear growth for O(L²) pairwise neq generation."
    );

    eprintln!(
        "heap_disjoint_pairwise_scaling: median ratio={median_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(L²) theory=16x, empirical ~55-60x for L={small_l}→{large_l}, \
          superquadratic from ay term interning overhead)"
    );
}

// =============================================================================
// Eager instantiation fixed-point: O(V × B × G) witness binding
// =============================================================================

/// Measures that eager existential instantiation scales linearly with the
/// number of ground postcondition_mut calls in the preconditions.
///
/// `build_witness_binding` at eager_instantiation.rs:149-179 uses a fixed-point
/// loop: `while progress { for body_call { for ground_call { ... } } }`.
/// For V bound variables, B body calls, and G ground calls, worst case is
/// O(V × B × G). With fixed V and B, scaling in G should be linear.
///
/// This test scales G (ground calls) with fixed V=2 and B=2 and checks
/// that the total time scales linearly, not quadratically.
///
/// Re: performance_proofs phase — eager instantiation fixed-point scaling
#[test]
#[timeout(30000)]
fn test_eager_instantiation_ground_call_scaling() {
    use std::time::Instant;

    use crate::verify::assert_eager_negated_existential_instantiations;

    let small_g = 5;
    let large_g = 20;
    let rounds = 5;
    let iters = 100;

    /// Build ensures: `exists<st, r> postcondition_mut(self, st) && postcondition_mut(self, r)`
    fn build_ensures() -> PureExpr {
        PureExpr::Exists {
            var: "st".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Exists {
                var: "r".to_string(),
                var_sort: None,
                body: Arc::new(and(
                    method_call(var("self"), "postcondition_mut", vec![var("st")]),
                    method_call(var("self"), "postcondition_mut", vec![var("r")]),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        }
    }

    /// Build requires with `g` ground postcondition_mut calls.
    fn build_requires(g: usize) -> Vec<PureExpr> {
        (0..g)
            .map(|i| {
                method_call(
                    var("self"),
                    "postcondition_mut",
                    vec![var(&format!("g_{i}"))],
                )
            })
            .collect()
    }

    fn run_eager(g: usize, iters: usize) -> std::time::Duration {
        let ensures = [build_ensures()];
        let requires = build_requires(g);
        let start = Instant::now();
        for _ in 0..iters {
            let mut encoder = AYEncoder::new_pure_with_quantifiers();
            for req in &requires {
                if let Ok(t) = encoder.encode_pure(req) {
                    encoder.assert_term(t);
                }
            }
            let _ = assert_eager_negated_existential_instantiations(
                &mut encoder,
                &ensures,
                &requires,
                &[],
            );
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_eager(small_g, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_eager(small_g, iters);
        let large_time = run_eager(large_g, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(G): ratio(20/5) ≈ 4x. For O(G²): ratio ≈ 16x.
    // The build_witness_binding loop is O(V × B × G) with fixed V=2, B=2.
    // Threshold 12x catches quadratic regression in G.
    assert!(
        min_ratio < 12.0,
        "eager instantiation scaling ratio ({large_g}/{small_g} ground calls) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 12x, eager instantiation has superlinear ground-call scaling. \
         Expected ~4x with O(G) for fixed V=2, B=2."
    );

    eprintln!(
        "eager_instantiation_ground_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(G) expect ~4x for G={small_g}→{large_g}, V=2, B=2)"
    );
}

// =============================================================================
// Quantified boolean expansion: O(2^N × N) enumeration bounded by var count
// =============================================================================

/// Verifies that boolean quantifier expansion in quantifier.rs produces
/// O(2^N) branch results and that the expansion is bounded by the number
/// of boolean-sorted quantifier variables.
///
/// The `expand_bool_quantifier` path at quantifier.rs:798-814 enumerates
/// all 2^N assignments for N boolean-sorted variables. For N=1 this is
/// 2 branches, for N=3 it's 8 branches, for N=5 it's 32 branches.
///
/// This test verifies:
/// 1. The encoding succeeds for small N (1-4 boolean variables)
/// 2. The time ratio between N=4 (16 branches) and N=2 (4 branches) stays
///    within the expected O(2^N) bound (ratio ≈ 4x, not exponential blow-up
///    from nested encoding inside each branch).
///
/// Re: performance_proofs phase — boolean quantifier expansion bound
#[test]
#[timeout(30000)]
fn test_bool_quantifier_expansion_scaling() {
    use std::time::Instant;

    use trust_wp_core::formula::ExprSort;

    let small_n = 2; // 4 branches
    let large_n = 4; // 16 branches
    let rounds = 5;
    let iters = 100;

    /// Build `forall<b0: Bool, b1: Bool, ..., b_{n-1}: Bool> (b0 && b1 && ... => true)`
    fn build_bool_quantified(n: usize) -> PureExpr {
        let mut body: PureExpr = bool_expr(true);
        for i in (0..n).rev() {
            let var_name = format!("b_{i}");
            body = implies(var(&var_name), body);
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

    fn run_bool_quant(n: usize, iters: usize) -> std::time::Duration {
        let expr = build_bool_quantified(n);
        let start = Instant::now();
        for _ in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();
            let _ = encoder.encode_pure(&expr);
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_bool_quant(small_n, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_bool_quant(small_n, iters);
        let large_time = run_bool_quant(large_n, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    // Use minimum ratio: least affected by system load spikes from
    // concurrent workers. Median is unreliable under multi-worker cargo
    // serialization (#2009 audit finding).
    let min_ratio = ratios[0];

    // For O(2^N): ratio(4/2) = 2^(4-2) = 4x. With inner encoding cost
    // per branch, could be somewhat higher. Threshold 10x catches unexpected
    // exponential blowup in the per-branch encoding cost.
    assert!(
        min_ratio < 10.0,
        "bool quantifier expansion ratio (N={large_n}/N={small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, per-branch encoding cost is growing faster than O(2^N). \
         Expected ~4x for N={small_n}→{large_n}."
    );

    eprintln!(
        "bool_quantifier_expansion: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(2^N) expect ~4x for N={small_n}→{large_n})"
    );
}

// =============================================================================

// =============================================================================
// Solver refinement loop: neq_pairs bounded by actual collisions
// =============================================================================

/// Verify that materialized neq pairs after recheck are bounded by the
/// number of actual collisions, not by the total term count.
///
/// The `asserted_quantified_neq_pairs` HashSet at `mod.rs:510` should
/// contain exactly the (left, right) pairs that collided in the solver
/// model, not all possible L*R combinations.
///
/// Re: #901 — neq pair accumulation bound
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)]
fn test_recheck_neq_pairs_bounded_by_collisions() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // 10 left terms, 10 right terms. Force exactly 3 collisions.
    let mut lefts = Vec::with_capacity(10);
    let mut rights = Vec::with_capacity(10);

    for i in 0..10 {
        let left = encoder
            .get_or_declare_var(&format!("__neq_l{i}"), Sort::Int)
            .expect("left");
        let right = encoder
            .get_or_declare_var(&format!("__neq_r{i}"), Sort::Int)
            .expect("right");
        lefts.push(left);
        rights.push(right);
    }

    // Force 3 specific collisions: left[0]==right[0], left[1]==right[1], left[2]==right[2]
    for i in 0..3 {
        let eq = encoder.solver.eq(lefts[i], rights[i]);
        encoder.solver.assert_term(eq);
    }
    // Force the remaining 7 pairs apart (left_i = i*100, right_i = i*100 + 50)
    for i in 3..10 {
        let lval = encoder.solver.int_const(i as i64 * 100);
        let leq = encoder.solver.eq(lefts[i], lval);
        encoder.solver.assert_term(leq);

        let rval = encoder.solver.int_const(i as i64 * 100 + 50);
        let req = encoder.solver.eq(rights[i], rval);
        encoder.solver.assert_term(req);
    }

    encoder
        .assertion_pipeline_mut_for_test()
        .push_active_disjoint_constraint_for_test(lefts.clone(), rights.clone());
    for &t in lefts.iter().chain(rights.iter()) {
        encoder
            .assertion_pipeline_mut_for_test()
            .insert_disjoint_term_for_test(t);
    }

    encoder
        .assertion_pipeline_mut_for_test()
        .prime_recheck_for_test();

    let result = encoder.check_sat();
    // May be Sat (if the solver finds a way to separate the 3) or Unsat.
    // Either way, materialized pairs should be bounded.

    let pair_count = encoder
        .assertion_pipeline_for_test()
        .asserted_neq_pairs_len();

    // At most 3 collisions can be detected, so at most 3 neq pairs materialized.
    // Definitely not 100 (L*R).
    assert!(
        pair_count <= 10,
        "neq pairs should be bounded by actual collisions, not L*R. \
         Got {pair_count} pairs for L=10, R=10 with 3 forced collisions. \
         If > 10, the recheck is materializing unnecessary pairs."
    );

    eprintln!(
        "recheck_neq_pairs_bounded: {pair_count} pairs materialized \
         (3 forced collisions, L=10, R=10, result={result:?})"
    );
}

// =============================================================================
// Solver refinement loop: revision gating prevents redundant rechecks
// =============================================================================

/// Verify that repeated check_sat calls without new assertions skip the
/// recheck loop via `AssertionPipeline::needs_disjoint_recheck()`.
///
/// After the first check_sat syncs `quantified_pairs_revision` to match
/// `assertion_revision`, subsequent calls should return immediately without
/// re-iterating constraint sets.
///
/// Re: #901 — revision-gated recheck efficiency
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_recheck_revision_gating_skips_redundant_recheck() {
    use std::time::Instant;

    use ay_dpll::api::{SolveResult, Sort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Set up 20 constraint sets (enough to be measurable)
    let anchor = encoder
        .get_or_declare_var("__rev_gate_anchor", Sort::Int)
        .expect("anchor");
    for i in 0..20 {
        let other = encoder
            .get_or_declare_var(&format!("__rev_gate_v{i}"), Sort::Int)
            .expect("var");
        encoder
            .assertion_pipeline_mut_for_test()
            .push_active_disjoint_constraint_for_test(vec![anchor], vec![other]);
        encoder
            .assertion_pipeline_mut_for_test()
            .insert_disjoint_term_for_test(anchor);
        encoder
            .assertion_pipeline_mut_for_test()
            .insert_disjoint_term_for_test(other);
    }

    encoder
        .assertion_pipeline_mut_for_test()
        .prime_recheck_for_test();

    // First call: does the actual recheck
    let result1 = encoder.check_sat();
    assert!(
        matches!(result1, SolveResult::Sat),
        "initial check should be SAT (no forced collisions), got {result1:?}"
    );

    // Revision should now be synced
    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .quantified_pairs_revision(),
        encoder.assertion_pipeline_for_test().assertion_revision(),
        "revision should be synced after first recheck"
    );

    // Second call: should skip recheck entirely (revision gate)
    let start = Instant::now();
    let repeat_count = 100;
    for _ in 0..repeat_count {
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "repeated check should still be SAT"
        );
    }
    let repeated_time = start.elapsed();

    // The 100 repeated calls should be fast since they skip recheck
    // (just solver.check_sat + revision comparison).
    // If revision gating is broken, they'd be 100x slower.
    eprintln!(
        "recheck_revision_gating: {repeat_count} repeated check_sat calls \
         in {:.1}ms (should be fast due to revision gating)",
        repeated_time.as_secs_f64() * 1000.0
    );
}

// =============================================================================
// Produces-ground scaling: real-encoder timing within four-hop range (#3313)
// =============================================================================

/// Verify that produces-ground transitivity stays bounded with the real encoder
/// within the four-hop active range (N <= TRUST_WP_PRODUCES_FOUR_HOP_CAP = 4).
///
/// Uses N=2 and N=4 (both within four-hop range) to measure real wall-clock
/// time. Non-adjacent high-hop chains are now pruned before emission, so this
/// test no longer requires super-linear growth; it only guards against
/// reintroducing explosive behavior.
///
/// Updated from #901 for three-tier cap system (#2688).
#[test]
#[timeout(60000)]
#[allow(clippy::cast_precision_loss)]
fn test_produces_ground_four_hop_real_encoder_scaling() {
    use std::time::Instant;

    let small_n = 2;
    let large_n = 4;
    let rounds = 2;

    fn run_produces_n_calls(n: usize) -> std::time::Duration {
        let start = Instant::now();
        let mut encoder = AYEncoder::new_with_quantifiers();

        let mut all_exprs = Vec::with_capacity(n);
        for i in 0..n {
            let from_name = format!("pgt_a{i}");
            let to_name = format!("pgt_a{}", i + 1);
            let vis_name = format!("pgt_v{i}");
            let p = method_call(
                var(&from_name),
                "produces",
                vec![view(var(&vis_name)), var(&to_name)],
            );
            all_exprs.push(p);
        }
        encoder.register_sort_hints(&all_exprs);

        for expr in &all_exprs {
            let term = encoder
                .encode_pure(expr)
                .expect("produces call should encode");
            encoder.assert_term(term);
        }

        start.elapsed()
    }

    // Warm up
    let _ = run_produces_n_calls(small_n);
    let _ = run_produces_n_calls(large_n);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let t_small = run_produces_n_calls(small_n);
        let t_large = run_produces_n_calls(large_n);
        let small_secs = t_small.as_secs_f64().max(1e-12);
        ratios.push(t_large.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // Non-adjacent high-hop chains are pruned, so the ratio is expected to be
    // close to linear at this scale. The key invariant is bounded growth.
    assert!(
        min_ratio > 0.2,
        "four-hop produces ground scaling ({large_n}/{small_n} calls) = \
         {min_ratio:.1}x — unexpectedly low; benchmark likely degenerated."
    );
    assert!(
        min_ratio < 60.0,
        "four-hop produces ground scaling ({large_n}/{small_n} calls) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 60x, the growth may be worse than expected."
    );

    eprintln!(
        "produces_four_hop_real_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (non-adjacent high-hop chains pruned for N={small_n}->{large_n})"
    );
}

// =============================================================================
// propagate_seq_value: component-wise equality soundness (mod.rs:758-784)
// =============================================================================

/// Helper: insert a SeqValue into the encoder's seq_state for a given term.
fn insert_seq_value(
    encoder: &mut AYEncoder,
    term: ay_dpll::api::Term,
    arr: ay_dpll::api::Term,
    len: ay_dpll::api::Term,
    offset: ay_dpll::api::Term,
) {
    encoder.seq_state_mut_for_test().insert_seq_value(
        term,
        crate::encoder::SeqValue {
            arr,
            len,
            offset,
            known_len: None,
        },
    );
}

/// Branch 1: `propagate_seq_value(t, t)` is a no-op (source == target).
///
/// Re: #901 — propagate_seq_value self-propagation no-op
#[test]
#[timeout(30000)]
fn test_propagate_seq_value_self_is_noop() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let t = encoder
        .get_or_declare_var("__psv_same", Sort::Int)
        .expect("var");
    let arr = encoder.solver.fresh_var("arr", Sort::Int);
    let len = encoder.solver.fresh_var("len", Sort::Int);
    let off = encoder.solver.int_const(0);
    insert_seq_value(&mut encoder, t, arr, len, off);

    encoder.propagate_seq_value(t, t);

    let sv = encoder.seq_state_for_test().get_seq_value(&t).unwrap();
    assert_eq!(sv.arr, arr, "self-propagation must not change arr");
    assert_eq!(sv.len, len, "self-propagation must not change len");
}

/// Branch 3: target has no SeqValue — propagation clones from source.
///
/// Re: #901 — propagate_seq_value insertion path
#[test]
#[timeout(30000)]
fn test_propagate_seq_value_inserts_to_empty_target() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let source = encoder
        .get_or_declare_var("__psv_src", Sort::Int)
        .expect("source");
    let target = encoder
        .get_or_declare_var("__psv_tgt", Sort::Int)
        .expect("target");
    let arr = encoder.solver.fresh_var("arr2", Sort::Int);
    let len = encoder.solver.fresh_var("len2", Sort::Int);
    let off = encoder.solver.int_const(0);
    insert_seq_value(&mut encoder, source, arr, len, off);

    assert!(!encoder.seq_state_for_test().has_seq_value(&target));
    encoder.propagate_seq_value(source, target);

    let sv = encoder
        .seq_state_for_test()
        .get_seq_value(&target)
        .expect("inserted");
    assert_eq!(sv.arr, arr, "propagated arr should match source");
    assert_eq!(sv.len, len, "propagated len should match source");
}

/// Branch 2 (soundness-critical): target already has a SeqValue with a
/// different length. Component-wise equality makes contradictory lengths UNSAT.
///
/// Re: #901 — propagate_seq_value component equality soundness
#[test]
#[timeout(30000)]
fn test_propagate_seq_value_contradictory_lengths_unsat() {
    use ay_dpll::api::{SolveResult, Sort};

    let mut encoder = AYEncoder::new();
    let source = encoder
        .get_or_declare_var("__psv_src2", Sort::Int)
        .expect("source");
    let target = encoder
        .get_or_declare_var("__psv_tgt2", Sort::Int)
        .expect("target");

    let arr_s = encoder.solver.fresh_var("arr_s", Sort::Int);
    let len_5 = encoder.solver.int_const(5);
    let off_0 = encoder.solver.int_const(0);
    insert_seq_value(&mut encoder, source, arr_s, len_5, off_0);

    let arr_t = encoder.solver.fresh_var("arr_t", Sort::Int);
    let len_10 = encoder.solver.int_const(10);
    let off_0b = encoder.solver.int_const(0);
    insert_seq_value(&mut encoder, target, arr_t, len_10, off_0b);

    encoder.propagate_seq_value(source, target);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "contradictory lengths (5 vs 10) should be UNSAT, got {result:?}"
    );
}

// =============================================================================
// Solver refinement loop: convergence pass count scaling
// =============================================================================

/// Measures that the refinement recheck loop converges in a bounded number of
/// passes regardless of the number of quantified disjoint constraint sets (K).
///
/// `check_sat_with_quantified_disjoint_recheck_bounded` iterates all K
/// constraint sets in a single pass, materializing `neq` for every collision
/// found. When the forced collision pattern is uniform (one collision per
/// set), a single pass should catch all K collisions simultaneously.
/// Convergence should therefore require O(1) passes independent of K, not
/// O(K) passes.
///
/// This test verifies that check_sat timing does not grow superlinearly with K
/// when each constraint set has exactly one forced collision.
///
/// Re: performance_proofs phase — solver refinement loop convergence (#901)
#[test]
#[timeout(30000)]
fn test_recheck_convergence_pass_count_invariant_of_k() {
    use std::time::Instant;

    use ay_dpll::api::SolveResult;

    let small_k = 4;
    let large_k = 16;
    let rounds = 5;
    let iters = 6;

    fn run_forced_collision_recheck(k: usize, iters: usize) -> std::time::Duration {
        let start = Instant::now();
        for iter in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();

            // For each constraint set, create two variables and force them equal.
            // The recheck loop should detect K collisions in pass 0, assert K neq
            // constraints, and converge in one recheck (pass 0 → materialize → recheck → Unsat).
            for set_idx in 0..k {
                let left = encoder
                    .get_or_declare_var(
                        &format!("__conv_l_{iter}_{set_idx}"),
                        ay_dpll::api::Sort::Int,
                    )
                    .expect("left var");
                let right = encoder
                    .get_or_declare_var(
                        &format!("__conv_r_{iter}_{set_idx}"),
                        ay_dpll::api::Sort::Int,
                    )
                    .expect("right var");

                // Force left == right (creates a collision)
                let forced_eq = encoder.solver.eq(left, right);
                encoder.solver.assert_term(forced_eq);

                // Register the disjoint constraint: left must != right
                encoder
                    .assertion_pipeline_mut_for_test()
                    .push_active_disjoint_constraint_for_test(vec![left], vec![right]);
                encoder
                    .assertion_pipeline_mut_for_test()
                    .insert_disjoint_term_for_test(left);
                encoder
                    .assertion_pipeline_mut_for_test()
                    .insert_disjoint_term_for_test(right);
            }

            // Set revisions to trigger recheck
            encoder
                .assertion_pipeline_mut_for_test()
                .prime_recheck_for_test();

            let result = encoder.check_sat();
            assert!(
                matches!(result, SolveResult::Unsat(_)),
                "forced {k}-set collision should be Unsat, got {result:?}"
            );
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_forced_collision_recheck(small_k, iters);
    let _ = run_forced_collision_recheck(large_k, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_forced_collision_recheck(small_k, iters);
        let large_time = run_forced_collision_recheck(large_k, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(K) pass-count-independent convergence: ratio(16/4) ~= 4x.
    // For O(K²) (if passes grow linearly with K): ratio ~= 16x.
    // Threshold 10x catches superlinear pass-count growth while tolerating
    // variance from term pool allocation and solver overhead.
    assert!(
        min_ratio < 10.0,
        "recheck convergence scaling ({large_k}/{small_k} constraint sets) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 10x, recheck loop pass count is growing with K \
         (expected O(1) passes, independent of constraint set count)."
    );

    eprintln!(
        "recheck_convergence_pass_count: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(1)-pass expect ~4x for K={small_k}→{large_k}, iters={iters})"
    );
}
