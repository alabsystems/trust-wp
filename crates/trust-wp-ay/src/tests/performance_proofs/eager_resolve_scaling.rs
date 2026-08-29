// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// eager instantiation: resolve call collection scaling
// =============================================================================

/// Verifies that eager instantiation with resolve() calls in nested Forall
/// binders scales linearly with the number of binders.
///
/// Exercises the code path through `collectors.rs:228` where a `HashSet<String>`
/// is converted to `Vec<String>` before calling `expr_mentions_bound_var`, which
/// then converts it back to `HashSet<String>` (matching.rs:165). This
/// HashSet→Vec→HashSet round-trip allocates O(B) per resolve() call, where B is
/// the bound variable count. Total waste: O(R * B) across R resolve calls.
///
/// The test goes through the public `assert_eager_negated_existential_instantiations`
/// API, which internally calls `collect_body_resolve_calls`.
///
/// Re: performance_proofs phase audit — HashSet→Vec→HashSet round-trip
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_eager_resolve_nested_forall_scaling() {
    use std::time::Instant;

    use crate::verify::assert_eager_negated_existential_instantiations;

    /// Build ensures with `n` nested Forall binders, each containing a resolve()
    /// call. This exercises the bound_vars HashSet growth per binder level.
    fn build_nested_resolve_ensures(n: usize) -> PureExpr {
        let mut expr = logic_fn_call("resolve", vec![var("x_0")]);
        for i in 1..n {
            let var_name = format!("x_{i}");
            let resolve_call = logic_fn_call("resolve", vec![var(&var_name)]);
            expr = PureExpr::Exists {
                var: var_name,
                var_sort: None,
                body: Arc::new(add(resolve_call, expr)),
                triggers: vec![],
            };
        }
        expr
    }

    /// Build requires with `g` ground resolve calls.
    fn build_resolve_requires(g: usize) -> Vec<PureExpr> {
        (0..g)
            .map(|i| logic_fn_call("resolve", vec![var(&format!("g_{i}"))]))
            .collect()
    }

    let small_n = 8;
    let large_n = 32;
    let rounds = 5;

    fn run_eager(n: usize, iters: usize) -> std::time::Duration {
        let ensures = [build_nested_resolve_ensures(n)];
        let requires = build_resolve_requires(n);
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

    // Warmup
    run_eager(small_n, 2);
    run_eager(large_n, 2);

    let iters = 20;
    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_eager(small_n, iters);
        let large_time = run_eager(large_n, iters);

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    let size_ratio = large_n as f64 / small_n as f64; // 4.0

    // Linear: ratio(32/8) ≈ 4x. Allow up to 25x for the HashSet→Vec→HashSet
    // round-trip overhead. Quadratic would be ~16x; cubic = ~64x.
    assert!(
        median < 25.0,
        "eager resolve nested Forall scaling ({large_n}/{small_n}) median = \
         {median:.1}x (rounds: {ratios:.1?}). \
         Expected linear-ish (<25x for {size_ratio}x size ratio). If > 25x, the \
         HashSet→Vec→HashSet round-trip at collectors.rs:228 + matching.rs:165 \
         may have compounded into superlinear behavior."
    );

    eprintln!(
        "eager resolve nested Forall: median={median:.1}x, rounds={ratios:.1?} \
         (linear ideal: ~{size_ratio}x, current has HashSet→Vec→HashSet overhead)"
    );
}

/// Verifies that eager instantiation with resolve() calls inside Match arms
/// scales linearly with arm count, not quadratically.
///
/// Exercises the code path at `collectors.rs:366-374` where each Match arm does:
///   bound_names().collect::<Vec>() → quantified_vars.extend(bound.iter().cloned())
/// This creates an intermediate Vec then clones each element again during extend.
///
/// Re: performance_proofs phase audit — collect-then-extend-cloned
#[test]
#[timeout(30000)]
#[allow(clippy::cast_precision_loss)]
fn test_eager_resolve_match_arm_count_scaling() {
    use std::time::Instant;

    use crate::verify::assert_eager_negated_existential_instantiations;

    /// Build requires with `n` Match arms, each binding a fresh variable
    /// and containing a ground resolve() call.
    fn build_match_requires(n: usize) -> Vec<PureExpr> {
        let arms: Vec<_> = (0..n)
            .map(|i| {
                let bound_name = format!("arm_{i}");
                crate::MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding(bound_name.clone()))),
                    },
                    body: logic_fn_call("resolve", vec![var(&bound_name)]),
                }
            })
            .collect();

        vec![PureExpr::Match {
            scrutinee: Arc::new(var("x")),
            arms,
        }]
    }

    /// Build a simple existential ensures with resolve().
    fn build_resolve_ensures() -> PureExpr {
        PureExpr::Exists {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(logic_fn_call("resolve", vec![var("r")])),
            triggers: vec![],
        }
    }

    let small_n = 10;
    let large_n = 40;
    let rounds = 5;

    fn run_eager_match(n: usize, iters: usize) -> std::time::Duration {
        let ensures = [build_resolve_ensures()];
        let requires = build_match_requires(n);
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

    // Warmup
    run_eager_match(small_n, 2);
    run_eager_match(large_n, 2);

    let iters = 30;
    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_eager_match(small_n, iters);
        let large_time = run_eager_match(large_n, iters);

        if small_time.as_nanos() > 0 {
            ratios.push(large_time.as_nanos() as f64 / small_time.as_nanos() as f64);
        }
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = ratios[ratios.len() / 2];

    let size_ratio = large_n as f64 / small_n as f64; // 4.0

    // Linear: ratio(40/10) ≈ 4x. Collect-then-extend-cloned adds constant
    // overhead per arm but should not change the asymptotic behavior.
    assert!(
        median < 25.0,
        "eager resolve Match arm scaling ({large_n}/{small_n}) median = \
         {median:.1}x (rounds: {ratios:.1?}). \
         Expected linear (<25x for {size_ratio}x size ratio). If > 25x, the \
         collect-then-extend-cloned pattern at collectors.rs:366-374 may have \
         regressed."
    );

    eprintln!(
        "eager resolve Match arms: median={median:.1}x, rounds={ratios:.1?} \
         (linear ideal: ~{size_ratio}x)"
    );
}
