// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for `filter_logic_fn_indices_for_goal`.
//!
//! Coverage gap: `logic.rs` has extensive tests for the test-only
//! `filter_logic_fns_for_goal` (in `performance_proofs.rs`) but zero
//! tests for the production `filter_logic_fn_indices_for_goal`, which
//! has unique logic: spec axiom reverse inclusion via `ensures` clauses
//! (#1296). These tests cover that production code path.

use std::collections::HashSet;

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use crate::{logic::filter_logic_fn_indices_for_goal, tests::helpers::*};

#[path = "logic_fn_filter_indices_basic.rs"]
mod logic_fn_filter_indices_basic;

/// Build a LogicFnDef whose body calls the named functions.
fn make_fn(name: &str, calls: &[&str]) -> LogicFnDef {
    let body = if calls.is_empty() {
        int(0)
    } else {
        let mut exprs: Vec<_> = calls
            .iter()
            .map(|c| logic_fn_call(c, vec![var("x")]))
            .collect();
        let mut result = exprs.pop().unwrap();
        for e in exprs.into_iter().rev() {
            result = add(e, result);
        }
        result
    };
    LogicFnDef::new(
        name.to_string(),
        format!("crate::test::{name}"),
        vec!["x".to_string()],
        body,
    )
    .with_mode(LogicMode::Open)
}

/// Build a LogicFnDef with ensures clauses that reference the named functions.
fn make_fn_with_ensures(name: &str, body_calls: &[&str], ensures_calls: &[&str]) -> LogicFnDef {
    let mut def = make_fn(name, body_calls);
    let ensures: Vec<_> = ensures_calls
        .iter()
        .map(|c| logic_fn_call(c, vec![var("x")]))
        .collect();
    def.set_ensures(ensures);
    def
}

fn names(s: &[&str]) -> HashSet<String> {
    s.iter().map(std::string::ToString::to_string).collect()
}

// --- Index ordering guarantee ---

#[test]
#[timeout(30000)]
fn indices_preserve_original_order() {
    // Reverse the dependency order in the slice to verify indices
    // come out in slice order, not discovery order.
    let fns = vec![
        make_fn("d", &[]),
        make_fn("c", &["d"]),
        make_fn("b", &["c"]),
        make_fn("a", &["b"]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(
        result,
        vec![0, 1, 2, 3],
        "indices should be in original slice order"
    );
}

// --- Nonexistent initial name ---

#[test]
#[timeout(30000)]
fn nonexistent_initial_name_returns_empty() {
    let fns = vec![make_fn("a", &[]), make_fn("b", &[])];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["nonexistent"]));
    assert!(result.is_empty(), "no function matches → empty result");
}
