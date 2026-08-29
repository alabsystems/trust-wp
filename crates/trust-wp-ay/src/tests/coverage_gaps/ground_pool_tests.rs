// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `encoder/ground_pool.rs` GroundTermPool functions with zero
//! external test coverage (#2514).
//!
//! Untested functions:
//! - `register_with_path_conditions`: path-condition registration + TRUST_WP_CAP_PER_SYMBOL guard
//! - `register_term_application`: term-only registration (no arg_exprs)
//! - `register_term_application_with_path_conditions`: combined path
//! - `needs_flush` / `mark_flushed`: revision-based idempotency tracking
//!
//! Also strengthens coverage of:
//! - `register`: basic registration
//! - `entries_for`: query after registration
//! - `register_axiom` + `axioms`: axiom lifecycle

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use crate::encoder::{
    ground_pool::{AxiomEntry, AxiomKind, GroundTermPool},
    AYEncoder,
};

// ── Helpers ──────────────────────────────────────────────────────────

fn make_encoder_and_terms() -> (AYEncoder, ay_dpll::api::Term, ay_dpll::api::Term) {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("x should declare");
    let y = encoder
        .get_or_declare_var("y", Sort::Int)
        .expect("y should declare");
    (encoder, x, y)
}

// ── register + entries_for ───────────────────────────────────────────

/// Empty pool returns None for any symbol.
#[test]
#[timeout(30000)]
fn entries_for_empty_pool() {
    let pool = GroundTermPool::new();
    assert!(pool.entries_for("f").is_none(), "empty pool has no entries");
}

/// Single registration is retrievable.
#[test]
#[timeout(30000)]
fn register_and_retrieve_entry() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);

    let mut pool = GroundTermPool::new();
    pool.register(
        "f",
        app,
        vec![x],
        vec![PureExpr::Var("x".to_string(), None)],
    );

    let entries = pool.entries_for("f").expect("should have entries for f");
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].arg_exprs.len(), 1);
    assert!(entries[0].path_conditions.is_empty());
}

/// Unregistered symbol returns None.
#[test]
#[timeout(30000)]
fn entries_for_unregistered_symbol() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);

    let mut pool = GroundTermPool::new();
    pool.register("f", app, vec![x], vec![PureExpr::Int(1)]);

    assert!(
        pool.entries_for("g").is_none(),
        "different symbol should be None"
    );
}

/// Multiple registrations for same symbol are all collected.
#[test]
#[timeout(30000)]
fn register_multiple_same_symbol() {
    let (mut encoder, x, y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app1 = encoder.solver.apply(&f, &[x]);
    let app2 = encoder.solver.apply(&f, &[y]);

    let mut pool = GroundTermPool::new();
    pool.register("f", app1, vec![x], vec![PureExpr::Int(1)]);
    pool.register("f", app2, vec![y], vec![PureExpr::Int(2)]);

    let entries = pool.entries_for("f").expect("entries for f");
    assert_eq!(entries.len(), 2, "should have 2 entries for f");
}

// ── register_with_path_conditions ────────────────────────────────────

/// Path conditions are stored in the entry.
#[test]
#[timeout(30000)]
fn register_with_path_conditions_stores_conditions() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);
    let guard = encoder.solver.bool_const(true);

    let mut pool = GroundTermPool::new();
    pool.register_with_path_conditions("f", app, vec![x], vec![PureExpr::Int(1)], vec![guard]);

    let entries = pool.entries_for("f").expect("entries for f");
    assert_eq!(entries.len(), 1);
    assert_eq!(
        entries[0].path_conditions.len(),
        1,
        "path condition should be stored"
    );
}

/// TRUST_WP_CAP_PER_SYMBOL (50) limits registrations per symbol.
#[test]
#[timeout(30000)]
fn register_cap_per_symbol_enforced() {
    let mut encoder = AYEncoder::new();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let mut pool = GroundTermPool::new();

    for i in 0..60 {
        let term = encoder.solver.int_const(i);
        let app = encoder.solver.apply(&f, &[term]);
        pool.register("f", app, vec![term], vec![PureExpr::Int(i)]);
    }

    let entries = pool.entries_for("f").expect("entries for f");
    assert_eq!(
        entries.len(),
        50,
        "entries should be capped at TRUST_WP_CAP_PER_SYMBOL (50)"
    );
}

// ── register_term_application ────────────────────────────────────────

/// Term-only registration stores empty arg_exprs.
#[test]
#[timeout(30000)]
fn register_term_application_empty_arg_exprs() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);

    let mut pool = GroundTermPool::new();
    pool.register_term_application("f", app, vec![x]);

    let entries = pool.entries_for("f").expect("entries for f");
    assert_eq!(entries.len(), 1);
    assert!(
        entries[0].arg_exprs.is_empty(),
        "term-only registration should have empty arg_exprs"
    );
    assert_eq!(
        entries[0].arg_terms.len(),
        1,
        "arg_terms should be preserved"
    );
}

/// Term-only with path conditions stores both.
#[test]
#[timeout(30000)]
fn register_term_application_with_path_conditions() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);
    let guard = encoder.solver.bool_const(true);

    let mut pool = GroundTermPool::new();
    pool.register_term_application_with_path_conditions("f", app, vec![x], vec![guard]);

    let entries = pool.entries_for("f").expect("entries for f");
    assert_eq!(entries.len(), 1);
    assert!(entries[0].arg_exprs.is_empty());
    assert_eq!(entries[0].path_conditions.len(), 1);
}

// ── needs_flush / mark_flushed ───────────────────────────────────────

/// Fresh pool does not need flush.
#[test]
#[timeout(30000)]
fn needs_flush_fresh_pool() {
    let pool = GroundTermPool::new();
    assert!(!pool.needs_flush(), "fresh pool should not need flush");
}

/// After registration, pool needs flush.
#[test]
#[timeout(30000)]
fn needs_flush_after_register() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);

    let mut pool = GroundTermPool::new();
    pool.register("f", app, vec![x], vec![PureExpr::Int(1)]);
    assert!(pool.needs_flush(), "pool should need flush after register");
}

/// After mark_flushed, pool no longer needs flush.
#[test]
#[timeout(30000)]
fn mark_flushed_clears_need() {
    let (mut encoder, x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app = encoder.solver.apply(&f, &[x]);

    let mut pool = GroundTermPool::new();
    pool.register("f", app, vec![x], vec![PureExpr::Int(1)]);
    assert!(pool.needs_flush());

    pool.mark_flushed();
    assert!(
        !pool.needs_flush(),
        "pool should not need flush after mark_flushed"
    );
}

/// New registration after flush re-triggers need.
#[test]
#[timeout(30000)]
fn needs_flush_re_triggered_after_new_register() {
    let (mut encoder, x, y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let app1 = encoder.solver.apply(&f, &[x]);
    let app2 = encoder.solver.apply(&f, &[y]);

    let mut pool = GroundTermPool::new();
    pool.register("f", app1, vec![x], vec![PureExpr::Int(1)]);
    pool.mark_flushed();
    assert!(!pool.needs_flush());

    pool.register("f", app2, vec![y], vec![PureExpr::Int(2)]);
    assert!(
        pool.needs_flush(),
        "pool should need flush after new register post-flush"
    );
}

/// Axiom registration also triggers needs_flush.
#[test]
#[timeout(30000)]
fn needs_flush_after_register_axiom() {
    let (mut encoder, _x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);

    let mut pool = GroundTermPool::new();
    pool.register_axiom(AxiomEntry {
        fn_symbol: "f".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl: f,
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    assert!(
        pool.needs_flush(),
        "pool should need flush after axiom registration"
    );
}

// ── register_axiom + axioms ──────────────────────────────────────────

/// Registered axiom is retrievable.
#[test]
#[timeout(30000)]
fn register_axiom_retrievable() {
    let (mut encoder, _x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);

    let mut pool = GroundTermPool::new();
    assert_eq!(pool.axioms().len(), 0);

    pool.register_axiom(AxiomEntry {
        fn_symbol: "f".to_string(),
        params: vec!["n".to_string()],
        body: PureExpr::Int(0),
        requires: vec![],
        func_decl: f,
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    assert_eq!(pool.axioms().len(), 1);
    assert_eq!(pool.axioms()[0].fn_symbol, "f");
    assert_eq!(pool.axioms()[0].kind, AxiomKind::Defining);
}

/// Spec axiom kind is preserved.
#[test]
#[timeout(30000)]
fn register_spec_axiom() {
    let (mut encoder, _x, _y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Bool);

    let mut pool = GroundTermPool::new();
    pool.register_axiom(AxiomEntry {
        fn_symbol: "f".to_string(),
        params: vec!["n".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl: f,
        return_sort: Sort::Bool,
        kind: AxiomKind::Spec,
    });

    assert_eq!(pool.axioms()[0].kind, AxiomKind::Spec);
}

// ── ground_term_count / symbol_count ─────────────────────────────────

/// Counts track registrations correctly.
#[test]
#[timeout(30000)]
fn counts_track_registrations() {
    let (mut encoder, x, y) = make_encoder_and_terms();
    let f = encoder.get_or_declare_logic_func("f", &[Sort::Int], Sort::Int);
    let g = encoder.get_or_declare_logic_func("g", &[Sort::Int], Sort::Int);
    let app_f = encoder.solver.apply(&f, &[x]);
    let app_g = encoder.solver.apply(&g, &[y]);

    let mut pool = GroundTermPool::new();
    assert_eq!(pool.ground_term_count(), 0);
    assert_eq!(pool.symbol_count(), 0);

    pool.register("f", app_f, vec![x], vec![PureExpr::Int(1)]);
    assert_eq!(pool.ground_term_count(), 1);
    assert_eq!(pool.symbol_count(), 1);

    pool.register("g", app_g, vec![y], vec![PureExpr::Int(2)]);
    assert_eq!(pool.ground_term_count(), 2);
    assert_eq!(pool.symbol_count(), 2);
}
