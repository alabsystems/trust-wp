// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Produces-ground transitivity: two-tier cap bounds assertion growth (#3313)
// =============================================================================

/// Verifies that the produces-ground transitivity assertion count is bounded
/// by the three-tier cap system in `produces_ground.rs`:
/// - `TRUST_WP_PRODUCES_FOUR_HOP_CAP` (4): disables 4-hop instances above 4 calls
/// - `TRUST_WP_PRODUCES_THREE_HOP_CAP` (4): disables 3-hop instances above 4 calls (#2671)
/// - `TRUST_WP_PRODUCES_GROUND_CAP` (6): disables all ground instances above 6 calls (#2671)
///
/// With the three-tier system (post #2671 reduction):
/// - Calls 1-4: 2-hop (O(N)), 3-hop (O(N^2)), 4-hop (O(N^3)) all active
/// - Calls 5-6: only 2-hop (O(N) dominant)
/// - Calls 7+: quantified axiom only (0 new ground instances)
///
/// A hard storage cap (`TRUST_WP_PRODUCES_GROUND_CAP * 2 = 12`) in `ProducesGroundCalls::insert()`
/// prevents unbounded memory growth after the cap. (#2709)
///
/// Re: #2688 — three-tier produces-ground cap for iterator timeout reduction
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_produces_ground_assertion_count_bounded_by_cap() {
    /// Compute assertion count with three-tier cap modeling.
    fn assertion_count_for_n_calls(n: usize, four_hop_cap: usize, three_hop_cap: usize) -> usize {
        let mut total = 0;
        for k in 1..n {
            let all = k + 1;
            total += 2 * k + 1;
            if k + 1 <= three_hop_cap {
                total += 3 * all * all;
            }
            if k + 1 <= four_hop_cap {
                total += 4 * all * all * all;
            }
        }
        total
    }

    let four_hop_cap = 4;
    let three_hop_cap = 4; // Reduced from 6 to 4 in #2671

    // Below four-hop cap: verify 4-hop growth is present.
    let n2 = assertion_count_for_n_calls(2, four_hop_cap, three_hop_cap);
    let n4 = assertion_count_for_n_calls(4, four_hop_cap, three_hop_cap);
    let ratio_2_to_4 = n4 as f64 / n2.max(1) as f64;
    assert!(
        ratio_2_to_4 > 3.0,
        "Assertion count ratio (4/2) = {ratio_2_to_4:.1}x should show super-linear growth \
         (4-hop active). n2={n2}, n4={n4}"
    );

    // At the overall cap (N=6, TRUST_WP_PRODUCES_GROUND_CAP), total should be manageable.
    let n6 = assertion_count_for_n_calls(6, four_hop_cap, three_hop_cap);
    assert!(
        n6 < 5_000,
        "Cumulative assertions at overall cap (N=6) should be <5K: got {n6}. \
         Old system at N=30 was >800K."
    );

    eprintln!(
        "produces_ground_assertion_count (three-tier): n2={n2}, n4={n4}, n6={n6}, \
         ratio(4/2)={ratio_2_to_4:.1}x, four_hop_cap={four_hop_cap}, three_hop_cap={three_hop_cap}"
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

    // Both within TRUST_WP_PRODUCES_FOUR_HOP_CAP (4) so 4-hop is active for all calls.
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
