// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ntest::timeout;

use super::*;
// ── #1536: collapse_old_over_mut_ref_currents binder recursion ────────
use crate::verify::mut_borrow::collapse_old_over_mut_ref_currents;

#[test]
#[timeout(30000)]
fn test_collapse_old_recurses_into_forall_body() {
    // old(forall a. a > *v) should collapse the *v inside, not clone verbatim.
    // With v as a mut ref param, old(*v) → *v (identity in postcondition context).
    let mut params = HashSet::new();
    params.insert("v".to_string());

    let expr = old(forall("a", gt(var("a"), deref(var("v")))));
    let result = collapse_old_over_mut_ref_currents(&expr, &params);

    // The old() should be stripped and the body preserved with *v intact
    // (old_body_is_mut_ref_entry_expr returns true for Deref(Var("v"))).
    // The forall structure must be preserved.
    match &result {
        PureExpr::Forall {
            var: bound_var,
            body,
            ..
        } => {
            assert_eq!(bound_var, "a");
            assert_eq!(**body, gt(var("a"), deref(var("v"))));
        }
        _ => panic!("expected Forall after collapse, got: {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_collapse_old_recurses_into_exists_body() {
    let mut params = HashSet::new();
    params.insert("v".to_string());

    let expr = old(exists("a", eq(var("a"), deref(var("v")))));
    let result = collapse_old_over_mut_ref_currents(&expr, &params);

    match &result {
        PureExpr::Exists {
            var: bound_var,
            body,
            ..
        } => {
            assert_eq!(bound_var, "a");
            assert_eq!(**body, eq(var("a"), deref(var("v"))));
        }
        _ => panic!("expected Exists after collapse, got: {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_collapse_old_recurses_into_match_arms() {
    let mut params = HashSet::new();
    params.insert("v".to_string());

    // old(match x { _ => *v }) — the *v in the arm body should be preserved
    let expr = old(match_expr(
        var("x"),
        vec![(Pattern::Wildcard, deref(var("v")))],
    ));
    let result = collapse_old_over_mut_ref_currents(&expr, &params);

    match &result {
        PureExpr::Match { scrutinee, arms } => {
            assert_eq!(scrutinee.as_ref(), &var("x"));
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].body, deref(var("v")));
        }
        _ => panic!("expected Match after collapse, got: {result:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_collapse_old_preserves_bare_mut_ref_in_forall() {
    // old(forall a. a > v) where v IS a mut ref param but NOT dereferenced.
    // Bare mut-ref params without Deref are ambiguous — old() must be preserved.
    let mut params = HashSet::new();
    params.insert("v".to_string());

    let expr = old(forall("a", gt(var("a"), var("v"))));
    let result = collapse_old_over_mut_ref_currents(&expr, &params);

    // old() should remain because bare Var("v") (without Deref) for a mut-ref param
    // is ambiguous — could mean current or final value.
    match &result {
        PureExpr::Old(inner) => match inner.as_ref() {
            PureExpr::Forall { var: bound_var, .. } => assert_eq!(bound_var, "a"),
            _ => panic!("expected Old(Forall(...)), got Old({inner:?})"),
        },
        _ => panic!("expected Old wrapper preserved for bare mut-ref body, got: {result:?}"),
    }
}
