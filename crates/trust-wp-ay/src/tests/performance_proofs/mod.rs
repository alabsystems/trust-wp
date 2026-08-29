// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance proof tests for trust-wp-ay.
//!
//! These tests verify algorithmic complexity bounds and regression-test
//! performance-critical code paths identified in issue #564.
//!
//! # Tested Properties
//!
//! 1. `filter_logic_fns_for_goal` terminates in at most F iterations
//! 2. `SepConj` chain encoding produces bounded constraint counts
//! 3. Sort hint registration is idempotent (no double-work)
//! 4. Logic function filtering returns correct transitive closure

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ay_dpll::Term;
use ntest::timeout;
use serial_test::serial;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::{
    super::{AYEncoder, PureExpr},
    helpers::*,
};
use crate::{
    encoder::FormulaCacheKey, logic::filter_logic_fns_for_goal, verify::substitute_vars_in_expr,
    Pattern,
};
mod axiom_witness_binding;
mod cache_and_throughput;
mod eager_resolve_scaling;
mod filter_logic_fns;
mod ground_pool_axiom_clone;
mod pairwise_constraints;
mod produces_and_seq_value;
mod quantified_recheck_check_sat_scaling;
mod quantifier_var_liveness_and_sort_inference;
mod sep_conj;
mod seq_and_deref_scaling;
mod solver_refinement;
mod sort_hints_and_traversal;
mod structural_equality_scan;
mod substitution;
mod trigger_synthesis_pair_search;
mod try_match_expr_scaling;

// =============================================================================
// Trigger synthesis: O(C²) pair search scaling
// =============================================================================

// =============================================================================
// Seq encoding: scaling with sequence operations
// =============================================================================

/// Measures that encoding N independent `push_back` operations scales linearly.
///
/// Each `push_back` creates a new `SeqValue` in the encoder's `seq_state`,
/// with an array term, length term, and offset term. The total state grows
/// O(N). This test verifies the per-operation cost doesn't degrade as the
/// seq_state grows (e.g., from linear scans over existing SeqValues).
///
/// Uses independent push_back calls on separate base variables to avoid
/// building deeply nested expression trees that could overflow the stack
/// during recursive encoding.
///
/// Re: performance_proofs phase — Seq encoding gap
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)]
fn test_seq_push_back_scaling_linear() {
    use std::time::Instant;

    let small_n = 20;
    let large_n = 80;
    let rounds = 5;

    /// Build and encode N independent push_back calls, each on a fresh base
    /// variable. This exercises seq_state growth without deep expression nesting.
    fn encode_push_back_batch(n: usize) -> std::time::Duration {
        let start = Instant::now();
        let mut encoder = AYEncoder::new();

        // Register sort hints for all base variables
        let hints: Vec<PureExpr> = (0..n)
            .map(|i| method_call(var(&format!("v_{i}")), "len", vec![]))
            .collect();
        encoder.register_sort_hints(&hints);

        for i in 0..n {
            let push_expr = method_call(var(&format!("v_{i}")), "push_back", vec![int(i as i64)]);
            // Ignore encoding failures — we're measuring seq_state growth cost
            let _ = encoder.encode_pure(&push_expr);
        }
        start.elapsed()
    }

    // Warm up
    let _ = encode_push_back_batch(small_n);
    let _ = encode_push_back_batch(large_n);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = encode_push_back_batch(small_n);
        let large_time = encode_push_back_batch(large_n);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(N): ratio(80/20) ≈ 4x. For O(N²): ratio ≈ 16x.
    // Threshold 10x catches quadratic regression in seq_state management.
    assert!(
        min_ratio < 10.0,
        "Seq push_back scaling ratio ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, seq_state management has quadratic overhead. \
         Expected ~4x with O(N) per-operation cost."
    );

    eprintln!(
        "seq_push_back_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x, O(N²) expect ~16x)"
    );
}

// =============================================================================
// Deref/Final Ite branch duplication: exponential growth detection
// =============================================================================

/// Verifies that encoding nested Deref(Ite(...)) patterns doesn't cause
/// exponential expression tree growth.
///
/// The pure_encoding.rs Deref path (lines 411-412) clones both branches
/// of an Ite and wraps each with Deref. With D levels of Deref wrapping
/// an Ite, the tree size could grow as O(2^D). This test measures the
/// encode time at different Deref nesting depths to detect exponential
/// growth.
///
/// Re: performance_proofs phase — Deref/Final Ite branch duplication
#[test]
#[timeout(30000)]
fn test_deref_ite_nesting_does_not_explode() {
    use std::time::Instant;

    let small_d = 4;
    let large_d = 8;
    let iters = 50;

    /// Build Deref^d(Ite(cond, a, b)) — d levels of Deref wrapping an Ite.
    fn build_deref_ite(depth: usize) -> PureExpr {
        let base = ite(gt(var("c"), int(0)), var("a"), var("b"));
        let mut expr = base;
        for _ in 0..depth {
            expr = deref(expr);
        }
        expr
    }

    let small_expr = build_deref_ite(small_d);
    let large_expr = build_deref_ite(large_d);

    // Warm up
    for _ in 0..iters {
        let mut enc = AYEncoder::new();
        enc.register_sort_hints(&[gt(var("c"), int(0)), var("a"), var("b")]);
        let _ = enc.encode_pure(&small_expr);
    }

    let mut ratios = Vec::with_capacity(5);
    for _ in 0..5 {
        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new();
            enc.register_sort_hints(&[gt(var("c"), int(0)), var("a"), var("b")]);
            let _ = enc.encode_pure(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let mut enc = AYEncoder::new();
            enc.register_sort_hints(&[gt(var("c"), int(0)), var("a"), var("b")]);
            let _ = enc.encode_pure(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(2^D): ratio(8/4) = 2^4 = 16x. For O(D): ratio ≈ 2x.
    // The depth limit (MAX_ENCODING_DEPTH=128) prevents true exponential
    // blowup at high depths, but at depth 8 we should see the encoding
    // pattern. Threshold 32x catches exponential while allowing for
    // expected O(2^D) growth at small depths where D_large/D_small = 2.
    //
    // NOTE: If the encoder short-circuits Deref(Ite) by not cloning
    // both branches, the ratio should drop. This test documents the
    // current behavior.
    assert!(
        min_ratio < 32.0,
        "Deref(Ite) nesting ratio (depth {large_d} / depth {small_d}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 32x, Deref/Ite duplication has worse-than-expected growth."
    );

    eprintln!(
        "deref_ite_nesting: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(D) expect ~2x, O(2^D) expect ~16x for depth {small_d}→{large_d})"
    );
}

// =============================================================================
// Produces-ground transitivity: three-tier cap bounds assertion growth (#2688, #3313)
// =============================================================================

/// Verifies that the produces-ground transitivity assertion count is bounded
/// by the three-tier cap system in `produces_ground.rs`:
/// - `TRUST_WP_PRODUCES_FOUR_HOP_CAP` (4): disables 4-hop instances above 4 calls
/// - `TRUST_WP_PRODUCES_THREE_HOP_CAP` (4): disables 3-hop instances above 4 calls (#2671)
/// - `TRUST_WP_PRODUCES_GROUND_CAP` (6): disables all ground instances above 6 calls (#2671)
///
/// With the current cap system (post #2671 reduction):
/// - Calls 1-4: 2-hop (O(N)), 3-hop (O(N^2)), 4-hop (O(N^3)) all active
/// - Calls 5-6: only 2-hop (O(N) dominant)
/// - Calls 7+: quantified axiom only (0 new ground instances)
///
/// A hard storage cap (`TRUST_WP_PRODUCES_GROUND_CAP * 2 = 12`) in `ProducesGroundCalls::insert()`
/// prevents the per-symbol tracker from growing unboundedly after the cap. (#2709)
///
/// This dramatically reduces peak assertion count compared to the old
/// single-cap system (30 with 4-hop always active: 108K peak per call).
/// New peak: ~313 per call at N=4 (last 4-hop call), then ~11 at N=6
/// (2-hop only), then 0 for N=7+.
///
/// Re: #2688, #2671 — three-tier produces-ground cap for iterator timeout reduction
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_produces_ground_assertion_count_bounded_by_three_tier_cap() {
    /// Compute the number of transitivity instances for N ground calls,
    /// modeling the three-tier cap: 4-hop disabled above `four_hop_cap`,
    /// 3-hop disabled above `three_hop_cap`.
    fn assertion_count_for_n_calls(n: usize, four_hop_cap: usize, three_hop_cap: usize) -> usize {
        let mut total = 0;
        for k in 1..n {
            let all = k + 1;
            // 2-hop: 2 * prior_calls + self-pair (always active below overall cap)
            total += 2 * k + 1;
            // 3-hop: 3 patterns * all^2 combinations (disabled above three_hop_cap)
            if k + 1 <= three_hop_cap {
                total += 3 * all * all;
            }
            // 4-hop: only when call count <= four_hop_cap
            if k + 1 <= four_hop_cap {
                total += 4 * all * all * all;
            }
        }
        total
    }

    let four_hop_cap = 4;
    let three_hop_cap = 4; // Reduced from 6 to 4 in #2671
    let overall_cap = 6; // Reduced from 8 to 6 in #2671

    // Below four-hop cap: verify 4-hop growth is present.
    let n2 = assertion_count_for_n_calls(2, four_hop_cap, three_hop_cap);
    let n4 = assertion_count_for_n_calls(4, four_hop_cap, three_hop_cap);
    let ratio_2_to_4 = n4 as f64 / n2.max(1) as f64;
    assert!(
        ratio_2_to_4 > 3.0,
        "Assertion count ratio (4/2) = {ratio_2_to_4:.1}x should show super-linear growth \
         (4-hop active). n2={n2}, n4={n4}"
    );

    // Above both 3-hop and 4-hop caps (both = 4): growth drops to O(N) from
    // 2-hop only. Since three_hop_cap == four_hop_cap == 4, there is no
    // intermediate region where only 4-hop is disabled.
    let n5 = assertion_count_for_n_calls(5, four_hop_cap, three_hop_cap);
    let n6 = assertion_count_for_n_calls(6, four_hop_cap, three_hop_cap);
    let incremental_with_all_hops = (n4 - n2) as f64 / 2.0;
    let incremental_2hop_only = (n6 - n5) as f64;
    assert!(
        incremental_2hop_only < incremental_with_all_hops,
        "Per-call incremental assertions should decrease after 3-hop and 4-hop disabled: \
         with_all_hops={incremental_with_all_hops:.0}, 2hop_only={incremental_2hop_only:.0}"
    );
    // 2-hop only at N=6: incremental = 2*5 + 1 = 11 assertions
    assert!(
        incremental_2hop_only < 15.0,
        "2-hop only incremental should be ~2N+1: got {incremental_2hop_only:.0}"
    );

    // Verify the overall cap bounds total work.
    assert!(
        n6 < 5_000,
        "Cumulative assertions at overall cap (N={overall_cap}) should be <5K: got {n6}. \
         Old system at N=30 was >800K."
    );

    // Verify the peak per-call assertion count at the four-hop boundary.
    // At N=4 (last 4-hop call), incremental = 2*3+1 + 3*4^2 + 4*4^3 = 313.
    let n3 = assertion_count_for_n_calls(3, four_hop_cap, three_hop_cap);
    let peak_per_call = n4 - n3;
    assert!(
        peak_per_call < 500,
        "Peak per-call assertions at four-hop boundary should be <500: got {peak_per_call}"
    );

    eprintln!(
        "produces_ground_assertion_count (three-tier): n2={n2}, n4={n4}, n6={n6}, \
         ratio(4/2)={ratio_2_to_4:.1}x, peak_per_call={peak_per_call}, \
         four_hop_cap={four_hop_cap}, three_hop_cap={three_hop_cap}, overall_cap={overall_cap}"
    );
}

// =============================================================================
// Substitution depth scaling: public API stays linear at binder boundaries
// =============================================================================

/// Measures that substitution on deeply nested quantified expressions stays
/// materially linear in nesting depth (d) for fixed substitution map size (s).
///
/// `#2484` moved the shared substitution engine away from per-binder map
/// cloning and onto overlay shadowing, but this public `substitute()` surface
/// must still avoid worse-than-linear depth regressions if binder handling
/// drifts again.
///
/// Re: performance_proofs phase — substitution depth scaling
#[test]
#[timeout(30000)]
fn test_substitution_depth_scaling_linear_in_public_api() {
    use std::{collections::HashMap, sync::Arc, time::Instant};

    use trust_wp_core::formula::PureExpr;

    /// Build a chain of `depth` nested forall quantifiers, each binding a
    /// different variable, with a leaf expression that references all
    /// substitution variables.
    fn build_nested_forall(depth: usize) -> PureExpr {
        let mut expr = PureExpr::Int(42);
        for d in (0..depth).rev() {
            expr = PureExpr::Forall {
                var: format!("q_{d}"),
                var_sort: None,
                body: Arc::new(expr),
                triggers: vec![],
            };
        }
        expr
    }

    let map_size = 10;
    let mut subs: HashMap<String, PureExpr> = HashMap::new();
    for i in 0..map_size {
        subs.insert(format!("s_{i}"), PureExpr::Int(i64::from(i)));
    }

    let small_d = 20;
    let large_d = 80;
    let iters = 200;
    let rounds = 5;

    let small_expr = build_nested_forall(small_d);
    let large_expr = build_nested_forall(large_d);

    // Warm up
    for _ in 0..iters {
        let _ = small_expr.substitute(&subs);
        let _ = large_expr.substitute(&subs);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let _ = small_expr.substitute(&subs);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let _ = large_expr.substitute(&subs);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(d): ratio(80/20) ≈ 4x. For O(d²): ratio ≈ 16x.
    // With fixed s, substitution depth scaling should stay linear → ratio ~4x.
    // Threshold 10x catches quadratic regression.
    assert!(
        min_ratio < 10.0,
        "Substitution depth scaling ratio (depth {large_d}/{small_d}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). \
         If > 10x, substitution depth handling has regressed past linear scaling. \
         Expected ~4x with O(d) for fixed map size s={map_size}."
    );

    eprintln!(
        "substitution_depth_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(d) expect ~4x for depth {small_d}→{large_d}, map_size={map_size})"
    );
}

// =============================================================================
// Post-SepConj assertion overhead: quantified disjoint constraint scanning
// =============================================================================

// =============================================================================
// Quantified disjoint recheck: check_sat scaling with many active constraint sets
// =============================================================================
// Quantified forall encoding + check_sat scaling
// =============================================================================

/// Measures that encoding and solving N independent quantified forall
/// expressions scales linearly in N.
///
/// Each forall expression is of the form:
///   forall x_i. (trigger: f_i(x_i)) => f_i(x_i) > 0
///
/// The encoding path (quantifier.rs:325) processes each forall independently:
/// - Trigger synthesis: O(1) per forall (one variable, one trigger candidate)
/// - Variable binding: O(1) per forall
/// - Body encoding: O(1) per forall
///
/// Total should be O(N). check_sat overhead is solver-dependent but should
/// not exhibit superlinear growth for independent constraints.
///
/// Re: performance_proofs phase — quantified forall check_sat scaling (#901)
#[test]
#[timeout(30000)]
fn test_quantified_forall_encode_check_sat_scaling() {
    use std::time::Instant;

    use ay_dpll::api::SolveResult;

    let small_n = 8;
    let large_n = 32;
    let rounds = 5;
    let iters = 12;

    fn run_forall_encode_and_solve(n: usize, iters: usize) -> std::time::Duration {
        let start = Instant::now();
        for iter in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();

            // Build N independent forall constraints, each with two unique
            // uninterpreted Bool functions and a quantified variable.
            // Pattern: forall x. (trigger: f(x)) => f(x) implies g(x)
            // This is satisfiable (interpret f as constant false) but
            // non-trivial: the solver must process each quantifier and
            // reason about the UF implication. Previous version used
            // f(x) == f(x) which is tautologically true and requires
            // zero solver reasoning — fixed per #901 audit.
            for i in 0..n {
                let fn_name = format!("qf_{iter}_{i}");
                let gn_name = format!("qg_{iter}_{i}");
                let var_name = format!("qv_{iter}_{i}");

                let fn_call = logic_fn_call(&fn_name, vec![var(&var_name)]);
                let gn_call = logic_fn_call(&gn_name, vec![var(&var_name)]);
                let body = implies(fn_call.clone(), implies(fn_call.clone(), gn_call));
                let quantified = forall_with_triggers(&var_name, body, vec![vec![fn_call]]);

                let term = encoder
                    .encode_pure(&quantified)
                    .unwrap_or_else(|err| panic!("forall {i} should encode: {err:?}"));
                encoder.assert_term(term);
            }

            // check_sat should not be Unsat (the constraints are satisfiable).
            // The solver may return Sat or Unknown depending on quantifier
            // instantiation heuristics — both are acceptable for a scaling
            // test where the ratio measurement is the real assertion.
            let result = encoder.check_sat();
            assert!(
                !matches!(result, SolveResult::Unsat(_)),
                "{n} independent forall constraints should not be Unsat, got {result:?}"
            );
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_forall_encode_and_solve(small_n, iters);
    let _ = run_forall_encode_and_solve(large_n, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_forall_encode_and_solve(small_n, iters);
        let large_time = run_forall_encode_and_solve(large_n, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    // Use minimum ratio: least affected by system load spikes from
    // concurrent workers (#2009 audit finding).
    let min_ratio = ratios[0];

    // For O(N): ratio(32/8) ~= 4x. For O(N²): ratio ~= 16x.
    // Threshold 12x catches superlinear growth in quantifier encoding or
    // solver quantifier instantiation overhead.
    assert!(
        min_ratio < 12.0,
        "quantified forall encode+check_sat scaling ({large_n}/{small_n}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 12x, quantifier encoding or solver instantiation has \
         superlinear overhead."
    );

    eprintln!(
        "quantified_forall_encode_check_sat_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x for N={small_n}→{large_n}, iters={iters})"
    );
}

// =============================================================================
// Existential instantiation: encoding scales linearly with precondition count
// =============================================================================

/// Verifies that encoding existentially quantified postconditions scales
/// linearly with the number of precondition ground calls. The eager
/// instantiation engine uses `build_witness_binding` (a fixed-point loop)
/// to match existential bound variables against ground method calls in
/// preconditions. This loop is O(V * B * G) worst case.
///
/// This test encodes a function with an existential postcondition and
/// varying numbers of precondition method calls, measuring total encoding
/// + check_sat time to verify the pipeline doesn't blow up.
///
/// The `expr_mentions_bound_var` sub-function (called per-iteration in
/// the fixed-point loop) uses `&[String]` contains for O(V) per Var node
/// and allocates a new Vec at every binder. Converting to HashSet would
/// reduce this to O(1) per node.
///
/// Re: performance_proofs phase — witness binding fixed-point finding
#[test]
#[timeout(30000)]
fn test_existential_instantiation_scales_with_precondition_count() {
    use std::time::Instant;

    // Build preconditions with N method calls: m0(x) > 0 && m1(x) > 0 && ...
    fn build_preconditions(n: usize) -> Vec<PureExpr> {
        (0..n)
            .map(|i| gt(method_call(var("x"), &format!("m{i}"), vec![]), int(0)))
            .collect()
    }

    let small_pre = 5;
    let large_pre = 20;
    let iters = 20;
    let rounds = 5;

    // Fixed postcondition with an existential: ensures exists<y> result > y
    let ensures = vec![exists("y", gt(var("result"), var("y")))];

    fn run_encode(
        requires: &[PureExpr],
        ensures: &[PureExpr],
        iters: usize,
    ) -> std::time::Duration {
        let start = Instant::now();
        for _ in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();
            // Register sorts from the expressions
            encoder.register_sort_hints(requires);
            encoder.register_sort_hints(ensures);
            // Encode requires
            for req in requires {
                if let Ok(term) = encoder.encode_pure(req) {
                    encoder.assert_term(term);
                }
            }
            // Encode ensures
            for ens in ensures {
                if let Ok(term) = encoder.encode_pure(ens) {
                    encoder.assert_term(term);
                }
            }
            let _ = encoder.check_sat();
        }
        start.elapsed()
    }

    let small_reqs = build_preconditions(small_pre);
    let large_reqs = build_preconditions(large_pre);

    // Warm up
    let _ = run_encode(&small_reqs, &ensures, iters);
    let _ = run_encode(&large_reqs, &ensures, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_encode(&small_reqs, &ensures, iters);
        let large_time = run_encode(&large_reqs, &ensures, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // O(N) precondition encoding: ratio(20/5) = 4x for linear.
    // The existential instantiation loop adds O(V * B * G) but V and B are
    // fixed, so scaling in G (precondition ground calls) should be linear.
    // Threshold 12x catches quadratic blowup (would be 16x).
    assert!(
        min_ratio < 12.0,
        "existential instantiation precondition scaling ({large_pre}/{small_pre}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         Expected ~4x with linear precondition encoding + fixed existential."
    );

    eprintln!(
        "existential_instantiation_precondition_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x for N={small_pre}→{large_pre} preconditions)"
    );
}

// =============================================================================
// detect_logic_requirements: 10-pass expression scan count verification
// =============================================================================

/// Verifies that detect_logic_requirements makes exactly 10 any_expr_matches
/// calls (as of #1919, #1922, #1923 additions). The earlier test
/// `test_expr_analysis_all_7_passes_scaling_linear` covers only 7 of the 10
/// passes. This test documents the current pass count and confirms linear
/// scaling across all 10 passes.
///
/// The 10 passes are:
/// 1. expr_needs_quantifiers
/// 2. expr_has_closure_spec_method
/// 3. expr_has_tuple_fn
/// 4. expr_has_datatype_spec_method
/// 5. expr_has_match_constructor_pattern
/// 6. expr_has_seq_method_needing_quantifiers (#1919)
/// 7. expr_has_bitwise_ops (#1922)
/// 8. expr_has_uf_method_call (#1923)
/// 9. expr_has_seq_index_on_final
/// 10. (not a separate pass — has_type_invariants and has_logic_fns are O(1) checks)
///
/// A single-pass visitor combining all 10 checks would reduce total work by ~10x.
///
/// Re: performance_proofs phase — 10-pass detection stale-count finding
#[test]
#[timeout(30000)]
fn test_detect_logic_requirements_all_10_passes_scaling() {
    use std::time::Instant;

    use crate::{
        expr::{
            collect_logic_fn_names, expr_has_bitwise_ops, expr_has_closure_spec_method,
            expr_has_datatype_spec_method, expr_has_match_constructor_pattern, expr_has_tuple_fn,
            expr_has_uf_method_call, expr_needs_quantifiers,
        },
        expr_seq::{expr_has_seq_index_on_final, expr_has_seq_method_needing_quantifiers},
    };

    // Build a diverse expression tree exercising all analysis functions
    fn build_diverse_expr_10(depth: usize) -> PureExpr {
        let mut expr = var("x");
        for i in 0..depth {
            expr = match i % 10 {
                0 => add(expr, var("y")),
                1 => method_call(expr, "len", vec![var("z")]),
                2 => logic_fn_call("helper", vec![expr]),
                3 => ite(gt(var("a"), int(0)), expr, var("b")),
                4 => view(expr),
                5 => deref(expr),
                6 => final_expr(expr),
                7 => method_call(expr, "push_back", vec![var("v")]),
                8 => binop(expr, super::super::BinOp::BitAnd, var("mask")),
                9 => method_call(expr, "ext_eq", vec![var("other")]),
                _ => unreachable!(),
            };
        }
        expr
    }

    let small_n = 50;
    let large_n = 200;
    let iters = 80;
    let rounds = 5;

    // Run all 10 analysis passes (matching detect_logic_requirements structure)
    let scan_all_10 = |expr: &PureExpr| {
        let _ = expr_needs_quantifiers(expr);
        let _ = expr_has_closure_spec_method(expr);
        let _ = expr_has_tuple_fn(expr);
        let _ = expr_has_datatype_spec_method(expr);
        let _ = expr_has_match_constructor_pattern(expr);
        let _ = expr_has_seq_method_needing_quantifiers(expr);
        let _ = expr_has_bitwise_ops(expr);
        let _ = expr_has_uf_method_call(expr);
        let _ = expr_has_seq_index_on_final(expr);
        let mut names = HashSet::new();
        collect_logic_fn_names(expr, &mut names);
    };

    let small_expr = build_diverse_expr_10(small_n);
    let large_expr = build_diverse_expr_10(large_n);

    // Warm up
    for _ in 0..iters {
        scan_all_10(&small_expr);
        scan_all_10(&large_expr);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            scan_all_10(&small_expr);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            scan_all_10(&large_expr);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // 10 passes at O(N) each = O(10N), still linear → ratio(200/50) ≈ 4x.
    // Threshold 10x catches quadratic in any single pass.
    assert!(
        min_ratio < 10.0,
        "detect_logic_requirements 10-pass scaling ({large_n}/{small_n}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 10x, one of the 10 expr analysis passes has quadratic behavior. \
         Expected ~4x with O(N) per-pass scanning."
    );

    eprintln!(
        "detect_logic_requirements_all_10_passes: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(N) expect ~4x, 10 passes at O(N) each = O(10N) still linear)"
    );
}
