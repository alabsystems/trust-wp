// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `collect_quantified_var_usage` (encoder::trigger) and
//! `merge_pre_verification_and_post_bootstrap_snapshots` (verify::mod).
//!
//! Both functions had ZERO direct test references prior to this file.
//!
//! `collect_quantified_var_usage` is the engine behind `expr_mentions_any_var`
//! (29 test refs) but its per-variable `mentions()` API was never tested.
//!
//! `merge_pre_verification_and_post_bootstrap_snapshots` is on the
//! soundness-critical demotion path; it determines which unsoundness increments
//! are absorbed vs reported.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use crate::{
    encoder::{
        trigger::collect_quantified_var_usage,
        unsoundness::{self, UnsoundnessCategory},
    },
    tests::helpers::{add, deref, final_expr, int, old, var, var_with_sort, view},
    verify::merge_pre_verification_and_post_bootstrap_snapshots,
};

fn vars(names: &[&str]) -> Vec<String> {
    names.iter().map(std::string::ToString::to_string).collect()
}

// ── collect_quantified_var_usage: basic coverage ───────────────────

#[test]
#[timeout(5000)]
fn usage_single_var_mentioned() {
    let v = vars(&["x"]);
    let usage = collect_quantified_var_usage(&v, &var("x"));
    assert!(usage.mentions("x"));
    assert!(usage.mentions_any());
}

#[test]
#[timeout(5000)]
fn usage_single_var_not_mentioned() {
    let v = vars(&["x"]);
    let usage = collect_quantified_var_usage(&v, &var("y"));
    assert!(!usage.mentions("x"));
    assert!(!usage.mentions_any());
}

#[test]
#[timeout(5000)]
fn usage_no_vars_empty_list() {
    let usage = collect_quantified_var_usage(&[], &var("x"));
    assert!(!usage.mentions_any());
}

#[test]
#[timeout(5000)]
fn usage_literal_mentions_nothing() {
    let v = vars(&["x"]);
    let usage = collect_quantified_var_usage(&v, &int(42));
    assert!(!usage.mentions("x"));
    assert!(!usage.mentions_any());
}

#[test]
#[timeout(5000)]
fn usage_multi_var_selective() {
    let v = vars(&["x", "y"]);
    let expr = add(var("x"), int(1));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"), "x appears in expression");
    assert!(!usage.mentions("y"), "y does not appear");
    assert!(usage.mentions_any());
}

#[test]
#[timeout(5000)]
fn usage_multi_var_both_mentioned() {
    let v = vars(&["x", "y"]);
    let expr = add(var("x"), var("y"));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
    assert!(usage.mentions("y"));
}

#[test]
#[timeout(5000)]
fn usage_through_deref() {
    let v = vars(&["x"]);
    let expr = deref(var("x"));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
}

#[test]
#[timeout(5000)]
fn usage_through_old() {
    let v = vars(&["x"]);
    let expr = old(var("x"));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
}

#[test]
#[timeout(5000)]
fn usage_through_final() {
    let v = vars(&["x"]);
    let expr = final_expr(var("x"));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
}

#[test]
#[timeout(5000)]
fn usage_through_view() {
    let v = vars(&["x"]);
    let expr = view(var("x"));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
}

#[test]
#[timeout(5000)]
fn usage_in_binop_lhs() {
    let v = vars(&["x", "y"]);
    let expr = PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0)));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
    assert!(!usage.mentions("y"));
}

#[test]
#[timeout(5000)]
fn usage_in_binop_rhs() {
    let v = vars(&["x", "y"]);
    let expr = PureExpr::BinOp(Arc::new(int(0)), BinOp::Lt, Arc::new(var("y")));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(!usage.mentions("x"));
    assert!(usage.mentions("y"));
}

#[test]
#[timeout(5000)]
fn usage_in_method_call_receiver() {
    let v = vars(&["s"]);
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("s")),
        method: "len".to_string(),
        args: vec![],
    };
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("s"));
}

#[test]
#[timeout(5000)]
fn usage_in_method_call_arg() {
    let v = vars(&["i"]);
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("other")),
        method: "get".to_string(),
        args: vec![var("i")],
    };
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("i"));
}

#[test]
#[timeout(5000)]
fn usage_in_logic_fn_call() {
    let v = vars(&["x", "y"]);
    let expr = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![var("x"), int(1)],
    };
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
    assert!(!usage.mentions("y"));
}

#[test]
#[timeout(5000)]
fn usage_in_ite_condition() {
    let v = vars(&["c"]);
    let expr = PureExpr::Ite(Arc::new(var("c")), Arc::new(int(1)), Arc::new(int(2)));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("c"));
}

#[test]
#[timeout(5000)]
fn usage_in_ite_branches() {
    let v = vars(&["x", "y"]);
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(var("x")),
        Arc::new(var("y")),
    );
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
    assert!(usage.mentions("y"));
}

#[test]
#[timeout(5000)]
fn usage_annotated_var_still_detected() {
    let v = vars(&["x"]);
    let expr = var_with_sort("x", ExprSort::Int);
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
}

#[test]
#[timeout(5000)]
fn usage_duplicate_var_names_deduplicated() {
    let v = vars(&["x", "x", "y"]);
    let expr = add(var("x"), var("y"));
    let usage = collect_quantified_var_usage(&v, &expr);
    assert!(usage.mentions("x"));
    assert!(usage.mentions("y"));
}

// ── merge_pre_verification_and_post_bootstrap_snapshots ───────────

#[test]
#[timeout(5000)]
fn merge_empty_snapshots() {
    let driver = unsoundness::Snapshot::new();
    let bootstrap = unsoundness::Snapshot::new();
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert!(merged.is_empty());
}

#[test]
#[timeout(5000)]
fn merge_driver_categories_preserved() {
    let mut driver = unsoundness::Snapshot::new();
    driver.insert(UnsoundnessCategory::SortFallbackToInt, 3);
    driver.insert(UnsoundnessCategory::LetAssumeDropped, 1);
    let bootstrap = unsoundness::Snapshot::new();
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&3)
    );
    assert_eq!(merged.get(&UnsoundnessCategory::LetAssumeDropped), Some(&1));
}

#[test]
#[timeout(5000)]
fn merge_logic_fn_fallback_uses_bootstrap_value() {
    let mut driver = unsoundness::Snapshot::new();
    driver.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 2);
    let mut bootstrap = unsoundness::Snapshot::new();
    bootstrap.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 5);
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&5),
        "SortFallbackToIntFromLogicFn must use bootstrap value to absorb false positives"
    );
}

#[test]
#[timeout(5000)]
fn merge_logic_fn_fallback_absent_from_driver_still_overrides() {
    let driver = unsoundness::Snapshot::new();
    let mut bootstrap = unsoundness::Snapshot::new();
    bootstrap.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 7);
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&7),
        "bootstrap value inserted even when driver has no entry for this category"
    );
}

#[test]
#[timeout(5000)]
fn merge_non_logic_fn_categories_not_overridden() {
    let mut driver = unsoundness::Snapshot::new();
    driver.insert(UnsoundnessCategory::SortFallbackToInt, 10);
    let mut bootstrap = unsoundness::Snapshot::new();
    bootstrap.insert(UnsoundnessCategory::SortFallbackToInt, 20);
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&10),
        "non-LogicFn categories must use driver value, not bootstrap"
    );
}

#[test]
#[timeout(5000)]
fn merge_mixed_categories() {
    let mut driver = unsoundness::Snapshot::new();
    driver.insert(UnsoundnessCategory::LetAssumeDropped, 1);
    driver.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 3);
    driver.insert(UnsoundnessCategory::BitwiseUfApproximation, 2);

    let mut bootstrap = unsoundness::Snapshot::new();
    bootstrap.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 8);
    bootstrap.insert(UnsoundnessCategory::OpaqueCallTrueAssumption, 4);

    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(merged.get(&UnsoundnessCategory::LetAssumeDropped), Some(&1));
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&8),
        "only LogicFn category overridden"
    );
    assert_eq!(
        merged.get(&UnsoundnessCategory::BitwiseUfApproximation),
        Some(&2)
    );
    assert_eq!(
        merged.get(&UnsoundnessCategory::OpaqueCallTrueAssumption),
        None,
        "bootstrap-only non-LogicFn categories NOT copied to merged"
    );
}

#[test]
#[timeout(5000)]
fn merge_logic_fn_absent_from_bootstrap_keeps_driver() {
    let mut driver = unsoundness::Snapshot::new();
    driver.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 4);
    let bootstrap = unsoundness::Snapshot::new();
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&4),
        "when bootstrap has no LogicFn entry, driver value is kept"
    );
}
