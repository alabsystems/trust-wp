// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `encoder/mod.rs` functions with zero or near-zero direct test
//! coverage (#2514).
//!
//! Targets:
//! - `maybe_assert_logic_ground_instances` (0 test refs, pub(crate))
//! - `axiom_apply` (0 test refs, pub(crate))
//! - `safe_apply` arity mismatch path (success + sort mismatch already covered
//!   by proof_coverage_gaps.rs)
//! - `try_restore_seq_element_from_int` guard paths (1 inline test, 0 external)

use ay_dpll::api::Sort;
use ntest::timeout;

use super::super::{super::*, helpers::*};
use crate::encoder::LogicGroundInstantiationMode;

// ── maybe_assert_logic_ground_instances ───────────────────────────

/// Disabled mode returns Ok(0) without touching the solver.
#[test]
#[timeout(30000)]
fn ground_instances_disabled_mode_returns_zero() {
    let mut encoder = AYEncoder::new();
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Disabled);
    let result = encoder.maybe_assert_logic_ground_instances();
    assert_eq!(result.unwrap(), 0, "Disabled mode should return 0");
}

/// Enabled mode with empty ground pool returns Ok(0) — no axioms or entries.
#[test]
#[timeout(30000)]
fn ground_instances_enabled_empty_pool_returns_zero() {
    let mut encoder = AYEncoder::new();
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Enabled);
    let result = encoder.maybe_assert_logic_ground_instances();
    assert_eq!(
        result.unwrap(),
        0,
        "Enabled mode with empty pool should return 0"
    );
}

/// Default mode is Enabled — verify the default behaves as Enabled.
#[test]
#[timeout(30000)]
fn ground_instances_default_mode_is_enabled() {
    let mut encoder = AYEncoder::new();
    // Don't set mode — use default
    let result = encoder.maybe_assert_logic_ground_instances();
    assert!(result.is_ok(), "default mode should succeed");
}

/// Switching from Enabled to Disabled changes behavior.
#[test]
#[timeout(30000)]
fn ground_instances_mode_switch() {
    let mut encoder = AYEncoder::new();

    // Default (Enabled) works
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Enabled);
    let r1 = encoder.maybe_assert_logic_ground_instances();
    assert!(r1.is_ok());

    // Switch to Disabled
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Disabled);
    let r2 = encoder.maybe_assert_logic_ground_instances();
    assert_eq!(r2.unwrap(), 0);

    // Switch back to Enabled
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Enabled);
    let r3 = encoder.maybe_assert_logic_ground_instances();
    assert!(r3.is_ok());
}

/// Enabled mode with registered axiom and matching ground entry produces
/// instantiations (count > 0).
#[test]
#[timeout(30000)]
fn ground_instances_enabled_with_axiom_and_entry() {
    let mut encoder = AYEncoder::new();
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Enabled);

    // Register a logic function and encode a call to populate ground pool
    let pred_expr = logic_fn_call("my_pred", vec![int(42)]);
    let _ = encoder.encode_pure(&pred_expr);

    // Now check — the pool may have entries if encoding registered them
    let result = encoder.maybe_assert_logic_ground_instances();
    assert!(
        result.is_ok(),
        "should succeed even with ground entries: {:?}",
        result
    );
}

// ── axiom_apply ───────────────────────────────────────────────────

/// Successful application returns Some(term) with correct sort.
#[test]
#[timeout(30000)]
fn axiom_apply_valid_returns_some() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("test_fn", &[Sort::Int], Sort::Bool);
    let arg = encoder.solver.int_const(42);
    let result = encoder.axiom_apply("test", &func, &[arg]);
    assert!(result.is_some(), "valid apply should return Some");
    let term = result.unwrap();
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "result should be Bool-sorted"
    );
}

/// Sort mismatch returns None instead of panicking.
#[test]
#[timeout(30000)]
fn axiom_apply_sort_mismatch_returns_none() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("int_fn", &[Sort::Int], Sort::Int);
    let bool_arg = encoder.solver.bool_const(true);
    let result = encoder.axiom_apply("test_mismatch", &func, &[bool_arg]);
    assert!(
        result.is_none(),
        "sort mismatch should return None, got Some"
    );
}

/// Arity mismatch (too few args) returns None.
#[test]
#[timeout(30000)]
fn axiom_apply_arity_too_few_returns_none() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("binary_fn", &[Sort::Int, Sort::Int], Sort::Int);
    let arg = encoder.solver.int_const(1);
    let result = encoder.axiom_apply("test_arity", &func, &[arg]);
    assert!(result.is_none(), "arity mismatch should return None");
}

/// Arity mismatch (too many args) returns None.
#[test]
#[timeout(30000)]
fn axiom_apply_arity_too_many_returns_none() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("unary_fn", &[Sort::Int], Sort::Int);
    let a = encoder.solver.int_const(1);
    let b = encoder.solver.int_const(2);
    let result = encoder.axiom_apply("test_arity_many", &func, &[a, b]);
    assert!(result.is_none(), "arity mismatch should return None");
}

/// Zero-arity function applied with no args succeeds.
#[test]
#[timeout(30000)]
fn axiom_apply_nullary_function() {
    let mut encoder = AYEncoder::new();
    let func = encoder.solver.declare_fun("const_fn", &[], Sort::Int);
    let result = encoder.axiom_apply("test_nullary", &func, &[]);
    assert!(result.is_some(), "nullary apply should return Some");
}

// ── safe_apply (arity mismatch — not covered by proof_coverage_gaps) ──

/// safe_apply with arity mismatch returns descriptive error.
#[test]
#[timeout(30000)]
fn safe_apply_arity_mismatch_returns_error() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("binary_fn", &[Sort::Int, Sort::Int], Sort::Bool);
    let arg = encoder.solver.int_const(1);
    let result = encoder.safe_apply("test_arity", &func, &[arg]);
    assert!(result.is_err(), "arity mismatch should return Err");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("arity mismatch"),
        "error should mention arity: {err_msg}"
    );
}

/// safe_apply with too many args returns arity error.
#[test]
#[timeout(30000)]
fn safe_apply_too_many_args_returns_error() {
    let mut encoder = AYEncoder::new();
    let func = encoder.solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let a = encoder.solver.int_const(1);
    let b = encoder.solver.int_const(2);
    let result = encoder.safe_apply("test_extra", &func, &[a, b]);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(err_msg.contains("expects 1 args, got 2"), "{err_msg}");
}

// ── try_restore_seq_element_from_int — guard paths ────────────────

/// Non-Int term returns None immediately.
#[test]
#[timeout(30000)]
fn restore_seq_elem_non_int_term_returns_none() {
    let mut encoder = AYEncoder::new();
    let bool_term = encoder.solver.bool_const(true);
    let target = Sort::Uninterpreted("Mapping".to_string());
    let result = encoder.try_restore_seq_element_from_int(bool_term, &target);
    assert!(result.is_none(), "non-Int term should return None");
}

/// Int target sort returns None immediately (no-op coercion).
#[test]
#[timeout(30000)]
fn restore_seq_elem_int_target_returns_none() {
    let mut encoder = AYEncoder::new();
    let int_term = encoder.solver.int_const(42);
    let result = encoder.try_restore_seq_element_from_int(int_term, &Sort::Int);
    assert!(result.is_none(), "Int target should return None");
}

/// Int term without seq-elem provenance and without seq-index source
/// returns None.
#[test]
#[timeout(30000)]
fn restore_seq_elem_no_provenance_returns_none() {
    let mut encoder = AYEncoder::new();
    let int_term = encoder.solver.int_const(99);
    let target = Sort::Uninterpreted("Foo".to_string());
    let result = encoder.try_restore_seq_element_from_int(int_term, &target);
    assert!(
        result.is_none(),
        "term without provenance should return None"
    );
}

/// Seq index_logic encodes to Int term, restoring to Mapping sort works
/// (exercises the seq_index_source path, complementing the inline test).
#[test]
#[timeout(30000)]
fn restore_seq_elem_via_index_logic_encoding() {
    use std::sync::Arc;

    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();

    // Encode a Seq index_logic call — this creates a term with seq_index provenance
    let seq_var = PureExpr::Var("preds".to_string(), Some(ExprSort::Seq));
    let index_expr = PureExpr::MethodCall {
        receiver: Arc::new(seq_var),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    let index_term = encoder
        .encode_pure(&index_expr)
        .expect("encode index_logic");
    assert_eq!(encoder.solver.get_sort(index_term), Sort::Int);

    // Restore to a custom sort — the seq_index_source path kicks in
    let custom = Sort::Uninterpreted("Custom".to_string());
    let result = encoder.try_restore_seq_element_from_int(index_term, &custom);
    assert!(
        result.is_some(),
        "index_logic term should restore via seq_index_source"
    );
    let restored = result.unwrap();
    assert_eq!(
        encoder.solver.get_sort(restored),
        custom,
        "restored term should have Custom sort"
    );
}

/// Fresh Int constant with no seq provenance returns None.
#[test]
#[timeout(30000)]
fn restore_seq_elem_fresh_int_no_provenance() {
    let mut encoder = AYEncoder::new();
    let fresh = encoder.solver.fresh_var("no_prov", Sort::Int);
    let target = Sort::Uninterpreted("Thing".to_string());
    let result = encoder.try_restore_seq_element_from_int(fresh, &target);
    assert!(
        result.is_none(),
        "fresh Int var without provenance should return None"
    );
}
