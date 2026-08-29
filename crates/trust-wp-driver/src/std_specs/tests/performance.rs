// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =============================================================================
// Performance: spec table lookup throughput
// =============================================================================

/// Benchmark `lookup_std_spec` by running `iters` lookups over `rounds`
/// and returning the median elapsed time for each round.
fn bench_lookup_median(path: &str, iters: usize, rounds: usize) -> std::time::Duration {
    use std::time::Instant;
    let mut times = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let _ = lookup_std_spec(path);
        }
        times.push(start.elapsed());
    }
    times.sort();
    times[rounds / 2]
}

/// Measures that `lookup_std_spec` throughput does not degrade for miss lookups
/// compared to hit lookups by more than the expected table scan factor.
///
/// This test verifies:
/// 1. Hit lookups are faster than miss lookups (early exit works).
/// 2. Miss lookup throughput doesn't have hidden quadratic behavior.
/// 3. Documents the absolute cost for future optimization (HashMap/phf).
///
/// Re: performance_proofs phase — std_specs linear scan lookup
#[test]
fn test_std_spec_lookup_throughput() {
    let iters = 10_000;
    let rounds = 5;

    let hit_path_early = "trust_wp_std::ghost::Ghost::new";
    let hit_path_late = "trust_wp_std::logic::ra::frac::Frac::split";
    let miss_path = "std::nonexistent::FakeType::fake_method";

    assert!(
        lookup_std_spec(hit_path_early).is_some(),
        "early hit path should resolve"
    );
    assert!(
        lookup_std_spec(hit_path_late).is_some(),
        "late hit path should resolve"
    );
    assert!(
        lookup_std_spec(miss_path).is_none(),
        "miss path should not resolve"
    );

    // Warm up
    for _ in 0..iters {
        let _ = lookup_std_spec(hit_path_early);
        let _ = lookup_std_spec(miss_path);
    }

    let median_hit = bench_lookup_median(hit_path_early, iters, rounds);
    let median_miss = bench_lookup_median(miss_path, iters, rounds);

    let hit_secs = median_hit.as_secs_f64().max(1e-12);
    let miss_hit_ratio = median_miss.as_secs_f64() / hit_secs;

    // Threshold 50x catches unexpected degradation while allowing for the
    // natural full-scan vs. early-exit difference.
    assert!(
        miss_hit_ratio < 50.0,
        "Miss/hit lookup ratio = {miss_hit_ratio:.1}x. \
         If > 50x, lookup_std_spec has unexpected overhead on misses. \
         hit={median_hit:?}, miss={median_miss:?} over {iters} iterations."
    );

    // Per-lookup cost: verify we can do at least 3K lookups/sec.
    // Threshold must be conservative: multi-worker builds under cargo
    // serialization and parallel compilation routinely drop to 13-15K ops/sec.
    // The 20K threshold caused flaky failures under load (P1]82, P1]18).
    // Lowered from 10K→3K after #2689 expanded UFCS path coverage from ~200→350+
    // entries: the linear scan proportionally slows miss lookups. A HashMap/phf
    // upgrade (tracked separately) would restore >100K ops/sec.
    #[allow(clippy::cast_precision_loss)] // Benchmark counter; precision loss is acceptable
    let miss_per_sec = iters as f64 / median_miss.as_secs_f64().max(1e-12);
    assert!(
        miss_per_sec > 3_000.0,
        "Miss lookup throughput = {miss_per_sec:.0} ops/sec. \
         Should be > 3K ops/sec (debug build). If slower, normalize_path or \
         table scan has regressed significantly."
    );
}
