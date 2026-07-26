// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use trust_wp_core::{
    formula::{BinOp, Formula, Location, MatchArm, Pattern, Permission, PureExpr, Value},
    smt::{expr_to_smt, formula_to_smt, SmtGenerator},
};

fn make_linear_expr(vars: usize) -> PureExpr {
    let mut expr = PureExpr::Var("x0".to_string(), None);
    for i in 1..vars {
        expr = PureExpr::BinOp(
            Arc::new(expr),
            BinOp::Add,
            Arc::new(PureExpr::Var(format!("x{i}"), None)),
        );
    }
    expr
}

#[allow(clippy::cast_possible_wrap)] // Benchmark indices are always small
fn make_points_to(idx: usize) -> Formula {
    Formula::PointsTo {
        location: Location(format!("loc{idx}")),
        value: Value::Expr(PureExpr::Int(idx as i64)),
        permission: Permission::FULL,
    }
}

fn make_sep_conj(count: usize) -> Formula {
    let mut formula = make_points_to(0);
    for idx in 1..count {
        formula = Formula::SepConj(Arc::new(formula), Arc::new(make_points_to(idx)));
    }
    formula
}

#[allow(clippy::cast_possible_wrap)] // Benchmark indices are always small
fn make_quantified_expr(triggers: usize) -> PureExpr {
    let var = "i".to_string();
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var(var.clone(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let mut trigger_groups = Vec::with_capacity(triggers);
    for idx in 0..triggers {
        let trigger = PureExpr::BinOp(
            Arc::new(PureExpr::Var(var.clone(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(idx as i64)),
        );
        trigger_groups.push(vec![trigger]);
    }
    PureExpr::Forall {
        var,
        var_sort: None,
        body: Arc::new(body),
        triggers: trigger_groups,
    }
}

#[allow(clippy::cast_possible_wrap)] // Benchmark indices are always small
fn make_match_expr(arms: usize) -> PureExpr {
    let mut match_arms = Vec::with_capacity(arms + 1);
    for idx in 0..arms {
        match_arms.push(MatchArm {
            pattern: Pattern::Literal(PureExpr::Int(idx as i64)),
            body: PureExpr::Int(idx as i64),
        });
    }
    match_arms.push(MatchArm {
        pattern: Pattern::Wildcard,
        body: PureExpr::Int(-1),
    });
    PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: match_arms,
    }
}

fn bench_expr_to_smt(c: &mut Criterion) {
    let mut group = c.benchmark_group("expr_to_smt");

    for size in [4usize, 16, 64] {
        let expr = make_linear_expr(size);
        group.bench_with_input(BenchmarkId::from_parameter(size), &expr, |b, input| {
            b.iter(|| black_box(expr_to_smt(black_box(input))));
        });
    }

    group.finish();
}

fn bench_expr_to_smt_complex(c: &mut Criterion) {
    let mut group = c.benchmark_group("expr_to_smt_complex");

    for triggers in [1usize, 4, 8] {
        let expr = make_quantified_expr(triggers);
        group.bench_with_input(
            BenchmarkId::new("forall_triggers", triggers),
            &expr,
            |b, input| {
                b.iter(|| black_box(expr_to_smt(black_box(input))));
            },
        );
    }

    for arms in [2usize, 6, 12] {
        let expr = make_match_expr(arms);
        group.bench_with_input(BenchmarkId::new("match_arms", arms), &expr, |b, input| {
            b.iter(|| black_box(expr_to_smt(black_box(input))));
        });
    }

    group.finish();
}

fn bench_formula_to_smt(c: &mut Criterion) {
    let mut group = c.benchmark_group("formula_to_smt");

    for count in [2usize, 8, 32] {
        let formula = make_sep_conj(count);
        group.bench_with_input(BenchmarkId::from_parameter(count), &formula, |b, input| {
            b.iter(|| black_box(formula_to_smt(black_box(input))));
        });
    }

    group.finish();
}

fn bench_declare_vars(c: &mut Criterion) {
    let mut group = c.benchmark_group("declare_vars");

    for vars in [4usize, 16, 64] {
        let expr = make_linear_expr(vars);
        group.bench_with_input(BenchmarkId::new("expr", vars), &expr, |b, input| {
            b.iter(|| {
                let mut generator = SmtGenerator::new();
                generator.declare_vars_in_expr(black_box(input));
                black_box(generator.output());
            });
        });
    }

    for points in [2usize, 8, 32] {
        let formula = make_sep_conj(points);
        group.bench_with_input(BenchmarkId::new("formula", points), &formula, |b, input| {
            b.iter(|| {
                let mut generator = SmtGenerator::new();
                generator.declare_vars_in_formula(black_box(input));
                black_box(generator.output());
            });
        });
    }

    group.finish();
}

criterion_group!(
    smt_benches,
    bench_expr_to_smt,
    bench_expr_to_smt_complex,
    bench_formula_to_smt,
    bench_declare_vars
);
criterion_main!(smt_benches);
