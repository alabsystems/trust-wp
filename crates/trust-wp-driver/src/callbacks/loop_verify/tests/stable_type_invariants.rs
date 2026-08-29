// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::BTreeMap, sync::Arc};

use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

use super::{infer_stable_type_invariant_clauses, ChangedPlaces, ChangedPlacesTree, PureExpr};

// --- infer_stable_type_invariant_clauses tests (#1816 Phase 3) ---

fn make_invariant_method_call(receiver_name: &str, method: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(receiver_name.to_string(), None)),
        method: method.to_string(),
        args: vec![],
    }
}

pub(super) fn make_changed_places(modified: &[&str]) -> ChangedPlaces {
    let mut map = std::collections::HashMap::new();
    for &name in modified {
        map.insert(name.to_string(), ChangedPlacesTree::Changed);
    }
    ChangedPlaces(map)
}

fn field_changed(field_idx: u32) -> ChangedPlacesTree {
    let mut fields = BTreeMap::new();
    fields.insert(field_idx, ChangedPlacesTree::Changed);
    ChangedPlacesTree::Fields(fields)
}

pub(super) fn deref_changed() -> ChangedPlacesTree {
    ChangedPlacesTree::Deref(Box::new(ChangedPlacesTree::Changed))
}

#[test]
fn type_inv_unchanged_receiver_inferred() {
    // x.invariant() where x is unchanged → inferred
    let req = make_invariant_method_call("x", "invariant");
    let changed = make_changed_places(&["i"]);
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert_eq!(
        result.len(),
        1,
        "invariant on unchanged receiver should be inferred"
    );
}

#[test]
fn type_inv_changed_receiver_excluded() {
    // x.invariant() where x is modified → not inferred
    let req = make_invariant_method_call("x", "invariant");
    let changed = make_changed_places(&["x"]);
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "invariant on changed receiver should not be inferred"
    );
}

#[test]
fn type_inv_trust_wp_prefixed_method_inferred() {
    // x.__trust_wp_invariant_Foo() where x is unchanged → inferred
    let req = make_invariant_method_call("x", "__trust_wp_invariant_Foo");
    let changed = make_changed_places(&["i"]);
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert_eq!(
        result.len(),
        1,
        "trust-wp-prefixed invariant on unchanged receiver should be inferred"
    );
}

#[test]
fn type_inv_non_invariant_method_excluded() {
    // x.len() is not an invariant method → not inferred
    let req = make_invariant_method_call("x", "len");
    let changed = make_changed_places(&["i"]);
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "non-invariant method call should not be inferred"
    );
}

#[test]
fn type_inv_with_args_excluded() {
    // x.invariant(y) has args → not inferred (invariant methods are zero-arg)
    let req = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![PureExpr::Var("y".to_string(), None)],
    };
    let changed = make_changed_places(&["i"]);
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "invariant method call with args should not be inferred"
    );
}

#[test]
fn type_inv_dedup_against_existing() {
    // x.invariant() already in existing_invariants → not duplicated
    let req = make_invariant_method_call("x", "invariant");
    let changed = make_changed_places(&["i"]);
    let existing = vec![req.clone()];
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &existing);
    assert!(
        result.is_empty(),
        "already-existing invariant should not be duplicated"
    );
}

#[test]
fn type_inv_complex_receiver_excluded() {
    // (x.get()).invariant() — non-Var receiver → not inferred
    let req = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
            method: "get".to_string(),
            args: vec![],
        }),
        method: "invariant".to_string(),
        args: vec![],
    };
    let changed = make_changed_places(&["i"]);
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "invariant on complex receiver should not be inferred"
    );
}

#[test]
fn type_inv_deref_receiver_respects_deref_changes() {
    let req = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        method: "invariant".to_string(),
        args: vec![],
    };
    let mut changed = ChangedPlaces::default();
    changed.0.insert("x".to_string(), deref_changed());
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "deref(receiver) invariant should be excluded when pointee changes"
    );
}

#[test]
fn type_inv_tuple_field_receiver_unchanged_sibling_inferred() {
    let req = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
        method: "invariant".to_string(),
        args: vec![],
    };
    let mut changed = ChangedPlaces::default();
    changed.0.insert("x".to_string(), field_changed(0));
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert_eq!(
        result.len(),
        1,
        "tuple field receiver should infer when only sibling field changes"
    );
}

#[test]
fn type_inv_tuple_field_receiver_changed_excluded() {
    let req = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
        method: "invariant".to_string(),
        args: vec![],
    };
    let mut changed = ChangedPlaces::default();
    changed.0.insert("x".to_string(), field_changed(0));
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "tuple field receiver should be excluded when that field changes"
    );
}

#[test]
fn type_inv_dotted_var_receiver_tracks_field_path() {
    let req = make_invariant_method_call("self.1", "invariant");
    let mut changed = ChangedPlaces::default();
    changed.0.insert("self".to_string(), field_changed(0));
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert_eq!(
        result.len(),
        1,
        "dotted receiver should infer when only sibling field changes"
    );
}

#[test]
fn type_inv_dotted_var_receiver_changed_field_excluded() {
    let req = make_invariant_method_call("self.0", "invariant");
    let mut changed = ChangedPlaces::default();
    changed.0.insert("self".to_string(), field_changed(0));
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert!(
        result.is_empty(),
        "dotted receiver should be excluded when referenced field changes"
    );
}

#[test]
fn type_inv_empty_changed_places() {
    // No changed places at all → all invariants inferred
    let req = make_invariant_method_call("x", "invariant");
    let changed = ChangedPlaces::default();
    let result = infer_stable_type_invariant_clauses(&[req], &changed, &[]);
    assert_eq!(
        result.len(),
        1,
        "with no changed places, all invariant methods should be inferred"
    );
}
