// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::*;
// =============================================================================
// Tests for filter_type_invariants_for_goal — "invariant" unqualified path
// =============================================================================

/// When the unqualified name "invariant" appears AND all invariant bodies are
/// trivially true, all invariants should be retained.
#[test]
#[timeout(30000)]
fn filter_type_invariants_retains_all_when_unqualified_invariant_and_all_trivial() {
    let inv_a = make_invariant("TypeA");
    let inv_b = make_invariant("TypeB");

    let ensures = [PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".into(), None)),
        method: "invariant".into(),
        args: vec![],
    }];

    let filtered =
        filter_type_invariants_for_goal(Some(&[inv_a, inv_b]), &[], &ensures, &[]).unwrap();
    assert_eq!(
        filtered.len(),
        2,
        "unqualified 'invariant' with all trivially true -> retain all"
    );
}

/// When the unqualified name "invariant" appears and at least one invariant
/// body is non-trivial, all definitions are still retained. The later encoder
/// phase can resolve the call to a qualified invariant UF from receiver type.
#[test]
#[timeout(30000)]
fn filter_type_invariants_retains_all_when_any_nontrivial() {
    let inv_trivial = make_invariant("TypeA"); // body = Bool(true)
    let inv_nontrivial = make_invariant_with_body(
        "TypeB",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    );

    let ensures = [PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".into(), None)),
        method: "invariant".into(),
        args: vec![],
    }];

    let filtered =
        filter_type_invariants_for_goal(Some(&[inv_trivial, inv_nontrivial]), &[], &ensures, &[])
            .unwrap();
    assert_eq!(
        filtered.len(),
        2,
        "unqualified 'invariant' with non-trivial body should retain all definitions"
    );
}

/// `filter_type_invariants_for_goal` with `None` returns `None`.
#[test]
#[timeout(30000)]
fn filter_type_invariants_none_returns_none() {
    let result = filter_type_invariants_for_goal(None, &[], &[], &[]);
    assert!(result.is_none(), "None input -> None output");
}
