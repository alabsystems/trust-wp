// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_ground_pool_register_and_count() {
    let mut encoder = AYEncoder::new();
    let mut pool = GroundTermPool::new();

    let a = encoder.solver.int_const(1);
    let b = encoder.solver.int_const(2);
    let app = encoder.solver.add(a, b);

    pool.register(
        "f",
        app,
        vec![a, b],
        vec![PureExpr::Int(1), PureExpr::Int(2)],
    );
    assert_eq!(pool.ground_term_count(), 1);

    pool.register("g", app, vec![a], vec![PureExpr::Int(1)]);
    assert_eq!(pool.ground_term_count(), 2);
    assert_eq!(pool.symbol_count(), 2);

    let mut syms = pool.symbols();
    syms.sort_unstable();
    assert_eq!(syms, vec!["f", "g"]);
}

#[test]
#[timeout(30000)]
fn test_ground_pool_cap_per_symbol() {
    let mut encoder = AYEncoder::new();
    let mut pool = GroundTermPool::new();

    for i in 0..(TRUST_WP_CAP_PER_SYMBOL + 5) {
        let val = i64::try_from(i).expect("TRUST_WP_CAP_PER_SYMBOL index should fit in i64");
        let t = encoder.solver.int_const(val);
        pool.register("f", t, vec![t], vec![PureExpr::Int(val)]);
    }

    assert_eq!(
        pool.ground_term_count(),
        TRUST_WP_CAP_PER_SYMBOL,
        "should cap at {TRUST_WP_CAP_PER_SYMBOL} per symbol"
    );
}

#[test]
#[timeout(30000)]
fn test_ground_pool_entries_for() {
    let mut encoder = AYEncoder::new();
    let mut pool = GroundTermPool::new();

    let a = encoder.solver.int_const(1);
    pool.register("f", a, vec![a], vec![PureExpr::Int(1)]);

    assert!(pool.entries_for("f").is_some());
    assert_eq!(pool.entries_for("f").expect("just registered").len(), 1);
    assert!(pool.entries_for("g").is_none());
}

#[test]
#[timeout(30000)]
fn test_ground_pool_default_is_empty() {
    let pool = GroundTermPool::default();
    assert_eq!(pool.ground_term_count(), 0);
    assert_eq!(pool.symbol_count(), 0);
}

#[test]
#[timeout(30000)]
fn test_ground_pool_preserves_arg_exprs() {
    let mut encoder = AYEncoder::new();
    let mut pool = GroundTermPool::new();

    let a = encoder.solver.int_const(42);
    let expr = PureExpr::Int(42);
    pool.register("f", a, vec![a], vec![expr.clone()]);

    let entries = pool.entries_for("f").expect("just registered");
    assert_eq!(entries[0].arg_exprs.len(), 1);
    assert_eq!(entries[0].arg_exprs[0], expr);
}

#[test]
#[timeout(30000)]
fn test_ground_pool_register_axiom() {
    let mut encoder = AYEncoder::new();
    let mut pool = GroundTermPool::new();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl =
        encoder
            .solver
            .declare_fun("test_fn", std::slice::from_ref(&int_sort), int_sort.clone());

    pool.register_axiom(AxiomEntry {
        fn_symbol: "test_fn".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl,
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    assert_eq!(pool.axiom_count(), 1);
    assert_eq!(pool.axioms()[0].fn_symbol, "test_fn");
    assert_eq!(pool.axioms()[0].params, vec!["x"]);
}

#[test]
#[timeout(30000)]
fn test_ground_pool_axiom_default_empty() {
    let pool = GroundTermPool::default();
    assert_eq!(pool.axiom_count(), 0);
}
