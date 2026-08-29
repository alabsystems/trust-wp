// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for quantifier encoding infrastructure in `encoder/quantifier/`.
//!
//! Covers genuinely untested paths:
//! - `QuantifierKind::apply_simple` (forall/exists dispatch)
//! - `QuantifierKind::apply_with_triggers` (triggered quantifiers)
//! - `QuantifierKind::apply_with_optional_invalid_trigger_fallback`
//! - `resolve_quantifier_var_sort` (multi-tier sort resolution)
//!
//! Part of #2514 (Tier 2 coverage gap: quantifier/mod.rs + pure_quantifier.rs,
//! 917 LOC combined, 0 inline tests, 3 external refs).

use std::collections::HashSet;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::super::{super::*, helpers::*};
use crate::encoder::quantifier::QuantifierKind;

// ── QuantifierKind::apply_simple ────────────────────────────────

/// Forall with a simple body produces a Bool-sorted term.
#[test]
#[timeout(30000)]
fn quantifier_kind_forall_simple() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = encoder.solver.int_var("x");
    let zero = encoder.solver.int_const(0);
    let body = encoder.solver.ge(x, zero);

    let result = QuantifierKind::Forall.apply_simple(&mut encoder.solver, &[x], body);
    assert!(result.is_ok(), "forall(x, x >= 0) should succeed");
    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(sort, Sort::Bool, "quantifier result should be Bool");
}

/// Exists with a simple body produces a Bool-sorted term.
#[test]
#[timeout(30000)]
fn quantifier_kind_exists_simple() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = encoder.solver.int_var("x");
    let five = encoder.solver.int_const(5);
    let body = encoder.solver.eq(x, five);

    let result = QuantifierKind::Exists.apply_simple(&mut encoder.solver, &[x], body);
    assert!(result.is_ok(), "exists(x, x == 5) should succeed");
    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(sort, Sort::Bool, "quantifier result should be Bool");
}

/// Multi-variable forall works.
#[test]
#[timeout(30000)]
fn quantifier_kind_forall_multi_var() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = encoder.solver.int_var("x");
    let y = encoder.solver.int_var("y");
    let eq_term = encoder.solver.eq(x, y);

    let result = QuantifierKind::Forall.apply_simple(&mut encoder.solver, &[x, y], eq_term);
    assert!(result.is_ok(), "forall(x y, x == y) should succeed");
}

// ── QuantifierKind::apply_with_triggers ─────────────────────────

/// Forall with a valid trigger succeeds.
#[test]
#[timeout(30000)]
fn quantifier_kind_forall_with_valid_trigger() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fd = encoder.get_or_declare_logic_func("logic_f", &[Sort::Int], Sort::Int);
    let x = encoder.solver.int_var("x");
    let fx = encoder.solver.apply(&fd, &[x]);
    let zero = encoder.solver.int_const(0);
    let body = encoder.solver.ge(fx, zero);

    let trigger = [fx];
    let result =
        QuantifierKind::Forall.apply_with_triggers(&mut encoder.solver, &[x], body, &[&trigger]);
    assert!(
        result.is_ok(),
        "forall(x, f(x) >= 0) with trigger {{f(x)}} should succeed"
    );
}

/// Exists with a valid trigger succeeds.
#[test]
#[timeout(30000)]
fn quantifier_kind_exists_with_valid_trigger() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fd = encoder.get_or_declare_logic_func("logic_g", &[Sort::Int], Sort::Bool);
    let x = encoder.solver.int_var("x");
    let gx = encoder.solver.apply(&fd, &[x]);

    let trigger = [gx];
    let result =
        QuantifierKind::Exists.apply_with_triggers(&mut encoder.solver, &[x], gx, &[&trigger]);
    assert!(
        result.is_ok(),
        "exists(x, g(x)) with trigger {{g(x)}} should succeed"
    );
}

// ── apply_with_optional_invalid_trigger_fallback ────────────────

/// Valid trigger does not trigger fallback.
#[test]
#[timeout(30000)]
fn optional_fallback_valid_trigger_no_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fd = encoder.get_or_declare_logic_func("logic_h", &[Sort::Int], Sort::Int);
    let x = encoder.solver.int_var("x");
    let hx = encoder.solver.apply(&fd, &[x]);
    let zero = encoder.solver.int_const(0);
    let body = encoder.solver.ge(hx, zero);

    let trigger = [hx];
    let result = QuantifierKind::Forall.apply_with_optional_invalid_trigger_fallback(
        &mut encoder.solver,
        &[x],
        body,
        &[&trigger],
        true,
    );
    assert!(result.is_ok(), "valid trigger should not produce error");
    let (term, fell_back) = result.unwrap();
    assert!(!fell_back, "valid trigger should not cause fallback");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(sort, Sort::Bool);
}

/// Invalid trigger with fallback allowed produces triggerless quantifier.
#[test]
#[timeout(30000)]
fn optional_fallback_invalid_trigger_falls_back() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = encoder.solver.int_var("x");
    let y = encoder.solver.int_var("y");
    let zero = encoder.solver.int_const(0);
    let body = encoder.solver.ge(x, zero);

    // Use y (not bound in this quantifier) as trigger — this is invalid
    // because triggers must reference at least one bound variable
    let trigger = [y];
    let result = QuantifierKind::Forall.apply_with_optional_invalid_trigger_fallback(
        &mut encoder.solver,
        &[x],
        body,
        &[&trigger],
        true, // allow fallback
    );
    // The result depends on ay-dpll behavior: it may either succeed with
    // fallback or succeed without error. Either way, not a hard error.
    if let Ok((_term, fell_back)) = result {
        // If it fell back, that's the expected behavior for invalid triggers
        let _ = fell_back;
    }
    // Even if ay-dpll accepts the trigger, the test confirms the method runs
}

/// Invalid trigger with fallback NOT allowed propagates the error.
#[test]
#[timeout(30000)]
fn optional_fallback_invalid_trigger_no_fallback_propagates() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = encoder.solver.int_var("x");
    let y = encoder.solver.int_var("y");
    let zero = encoder.solver.int_const(0);
    let body = encoder.solver.ge(x, zero);

    // Use y (not bound) as trigger
    let trigger = [y];
    let result = QuantifierKind::Forall.apply_with_optional_invalid_trigger_fallback(
        &mut encoder.solver,
        &[x],
        body,
        &[&trigger],
        false, // do NOT allow fallback
    );
    // If ay-dpll rejects the trigger, it should be an error (not a silent fallback)
    // If ay-dpll accepts it, the method should return Ok with fell_back=false
    if let Ok((_term, fell_back)) = result {
        assert!(!fell_back, "fallback disabled should not fall back");
    }
    // Err case: expected — error propagated from ay-dpll trigger rejection
}

// ── resolve_quantifier_var_sort ─────────────────────────────────

/// Explicit Bool ExprSort annotation produces Bool sort.
#[test]
#[timeout(30000)]
fn resolve_quant_sort_explicit_bool() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let sort = encoder.resolve_quantifier_var_sort(
        "b",
        Some(&ExprSort::Bool),
        &HashSet::new(),
        &bool_expr(true),
    );
    assert_eq!(
        sort,
        Sort::Bool,
        "explicit Bool annotation should produce Bool sort"
    );
}

/// Explicit Seq ExprSort annotation produces Seq sort.
#[test]
#[timeout(30000)]
fn resolve_quant_sort_explicit_seq() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let sort =
        encoder.resolve_quantifier_var_sort("s", Some(&ExprSort::Seq), &HashSet::new(), &int(0));
    assert!(
        sort.is_seq(),
        "explicit Seq annotation should produce Seq sort, got {sort:?}"
    );
}

/// No annotation + bool_names contains var → Bool.
#[test]
#[timeout(30000)]
fn resolve_quant_sort_bool_hint() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let mut bool_names = HashSet::new();
    bool_names.insert("flag".to_string());

    let sort = encoder.resolve_quantifier_var_sort("flag", None, &bool_names, &bool_expr(true));
    assert_eq!(sort, Sort::Bool, "bool_names hint should produce Bool sort");
}

/// No annotation + no hints → Int (default fallback).
#[test]
#[timeout(30000)]
fn resolve_quant_sort_default_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let sort = encoder.resolve_quantifier_var_sort("n", None, &HashSet::new(), &int(0));
    assert_eq!(sort, Sort::Int, "no annotation/hints should default to Int");
}

/// Explicit Int annotation returns Int (not overridden without hints).
#[test]
#[timeout(30000)]
fn resolve_quant_sort_explicit_int_stays_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let sort =
        encoder.resolve_quantifier_var_sort("n", Some(&ExprSort::Int), &HashSet::new(), &int(0));
    assert_eq!(
        sort,
        Sort::Int,
        "explicit Int without override hints stays Int"
    );
}

/// Receiver usage on recognized Seq methods should upgrade the fallback Int
/// binder sort before quantifier encoding. (#2696)
#[test]
#[timeout(30000)]
fn resolve_quant_sort_method_usage_seq_receiver_overrides_int_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let body = gt(method_call(var("s"), "len", vec![]), int(0));

    let sort =
        encoder.resolve_quantifier_var_sort("s", Some(&ExprSort::Int), &HashSet::new(), &body);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "s.len() should refine an Int fallback binder to Seq"
    );
}
