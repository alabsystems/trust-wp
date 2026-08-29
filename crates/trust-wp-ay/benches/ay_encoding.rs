// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Benchmarks for `AYEncoder` encoding operations.
//!
//! These benchmarks measure the performance of separating conjunction encoding,
//! which has O(|left| * |right|) complexity for disjointness assertions.

use std::sync::Arc;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use trust_wp_ay::AYEncoder;
use trust_wp_core::formula::{Formula, Location, Permission, PureExpr, Value};

/// Create a `PointsTo` formula with a given index.
#[allow(clippy::cast_possible_wrap)]
fn make_points_to(idx: usize) -> Formula {
    Formula::PointsTo {
        location: Location(format!("loc{idx}")),
        value: Value::Expr(PureExpr::Int(idx as i64)),
        permission: Permission::FULL,
    }
}

/// Create a chain of separating conjunctions with `count` locations.
fn make_sep_conj_chain(count: usize) -> Formula {
    if count == 0 {
        return Formula::True;
    }
    let mut formula = make_points_to(0);
    for idx in 1..count {
        formula = Formula::SepConj(Arc::new(formula), Arc::new(make_points_to(idx)));
    }
    formula
}

/// Create two separate branches of separating conjunction for disjointness testing.
/// Returns `SepConj(left[0..size], right[size..2*size])` with `size` locations on each side.
fn make_sep_conj_pair(size: usize) -> Formula {
    let left = make_sep_conj_chain(size);
    // Right side: locations [size, size+1, ..., 2*size-1] (size elements)
    let mut right = make_points_to(size);
    for idx in (size + 1)..(2 * size) {
        right = Formula::SepConj(Arc::new(right), Arc::new(make_points_to(idx)));
    }
    Formula::SepConj(Arc::new(left), Arc::new(right))
}

/// Benchmark encoding of separating conjunction formulas.
///
/// Tests how encoding time scales with footprint size.
fn bench_sep_conj_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("sep_conj_encoding");

    // Test scaling: 2, 4, 8, 16, 32 locations per side
    // This exercises the O(n^2) disjointness assertion loop
    for size in [2usize, 4, 8, 16, 32] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter(|| {
                let formula = make_sep_conj_pair(size);
                let mut encoder = AYEncoder::new();
                let _ = encoder.encode(black_box(&formula));
            });
        });
    }

    group.finish();
}

/// Benchmark encoding of linear chain separating conjunction.
///
/// Tests encoding of a single chain of `SepConj`, which should be
/// roughly linear in the number of locations.
fn bench_sep_conj_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("sep_conj_chain");

    for count in [4usize, 8, 16, 32, 64] {
        group.bench_with_input(BenchmarkId::from_parameter(count), &count, |b, &count| {
            b.iter(|| {
                let formula = make_sep_conj_chain(count);
                let mut encoder = AYEncoder::new();
                let _ = encoder.encode(black_box(&formula));
            });
        });
    }

    group.finish();
}

/// Benchmark encoding + solving of `SepConj` chains with quantified disjointness.
///
/// Compares quantified (AUFLIA) encoding at various chain sizes.
/// Cross-pair benchmarks above use `AYEncoder::new()` (`QF_AUFLIA`).
fn bench_sep_conj_chain_quantified(c: &mut Criterion) {
    let mut group = c.benchmark_group("sep_conj_chain_quantified");

    for count in [4usize, 8, 16, 32, 64] {
        group.bench_with_input(BenchmarkId::from_parameter(count), &count, |b, &count| {
            b.iter(|| {
                let formula = make_sep_conj_chain(count);
                let mut encoder = AYEncoder::try_new_with_quantifiers()
                    .expect("failed to create quantified ay encoder");
                let result = encoder.encode(black_box(&formula));
                if let Ok(term) = result {
                    encoder.assert_term(term);
                    let _ = encoder.check_sat();
                }
            });
        });
    }

    group.finish();
}

/// Benchmark footprint extraction (used in disjointness).
fn bench_footprint_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("footprint_extraction");

    for count in [4usize, 8, 16, 32, 64] {
        // Pre-create formulas outside the benchmark loop
        let formula = make_sep_conj_chain(count);
        group.bench_with_input(
            BenchmarkId::from_parameter(count),
            &formula,
            |b, formula| {
                b.iter(|| {
                    // Encoder creation is included since extract_footprint is internal
                    let mut encoder = AYEncoder::new();
                    let _ = encoder.encode(black_box(formula));
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_sep_conj_encoding,
    bench_sep_conj_chain,
    bench_sep_conj_chain_quantified,
    bench_footprint_extraction,
);
criterion_main!(benches);
