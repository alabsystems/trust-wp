// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::encoder::state::closure::ClosureState`].
//!
//! Coverage gap: `insert_param_mapping`, `insert_body`, `def_id_for_param`,
//! `get_body`, and `single_body` had zero direct tests despite being
//! `pub(crate)`. The `single_body` method has non-trivial logic
//! (`len() == 1` guard).

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use crate::encoder::{closure_inline::ClosureBodyInfo, ClosureState};

fn make_body_info(body_val: i64) -> ClosureBodyInfo {
    ClosureBodyInfo {
        param_name: None,
        body: Some(PureExpr::Int(body_val)),
        param_names: vec!["x".to_string()],
        capture_names: vec![],
        ensures_exprs: None,
        requires_exprs: None,
    }
}

// --- new / is_empty ---

#[test]
#[timeout(30000)]
fn new_closure_state_is_empty() {
    let state = ClosureState::new();
    assert!(state.is_empty());
}

// --- insert_body / is_empty ---

#[test]
#[timeout(30000)]
fn insert_body_makes_state_non_empty() {
    let mut state = ClosureState::new();
    state.insert_body("def_1".to_string(), make_body_info(42));
    assert!(!state.is_empty());
}

// --- insert_body / get_body ---

#[test]
#[timeout(30000)]
fn get_body_returns_inserted_body() {
    let mut state = ClosureState::new();
    state.insert_body("def_1".to_string(), make_body_info(42));

    let info = state.get_body("def_1").expect("body should exist");
    assert_eq!(info.body, Some(PureExpr::Int(42)));
    assert_eq!(info.param_names, vec!["x"]);
}

#[test]
#[timeout(30000)]
fn get_body_returns_none_for_missing_def_id() {
    let state = ClosureState::new();
    assert!(state.get_body("nonexistent").is_none());
}

#[test]
#[timeout(30000)]
fn insert_body_overwrites_existing_entry() {
    let mut state = ClosureState::new();
    state.insert_body("def_1".to_string(), make_body_info(1));
    state.insert_body("def_1".to_string(), make_body_info(2));

    let info = state.get_body("def_1").unwrap();
    assert_eq!(info.body, Some(PureExpr::Int(2)));
}

// --- insert_param_mapping / def_id_for_param ---

#[test]
#[timeout(30000)]
fn def_id_for_param_returns_mapped_def_id() {
    let mut state = ClosureState::new();
    state.insert_param_mapping("closure_arg".to_string(), "def_99".to_string());

    let def_id = state
        .def_id_for_param("closure_arg")
        .expect("mapping should exist");
    assert_eq!(def_id, "def_99");
}

#[test]
#[timeout(30000)]
fn def_id_for_param_returns_none_for_unmapped_name() {
    let state = ClosureState::new();
    assert!(state.def_id_for_param("unknown").is_none());
}

#[test]
#[timeout(30000)]
fn param_mapping_overwrites_previous_entry() {
    let mut state = ClosureState::new();
    state.insert_param_mapping("p".to_string(), "old_def".to_string());
    state.insert_param_mapping("p".to_string(), "new_def".to_string());

    assert_eq!(state.def_id_for_param("p").unwrap(), "new_def");
}

// --- single_body ---

#[test]
#[timeout(30000)]
fn single_body_returns_body_when_exactly_one() {
    let mut state = ClosureState::new();
    state.insert_body("only".to_string(), make_body_info(7));

    let info = state.single_body().expect("should return single body");
    assert_eq!(info.body, Some(PureExpr::Int(7)));
}

#[test]
#[timeout(30000)]
fn single_body_returns_none_when_empty() {
    let state = ClosureState::new();
    assert!(state.single_body().is_none());
}

#[test]
#[timeout(30000)]
fn single_body_returns_none_when_multiple_bodies() {
    let mut state = ClosureState::new();
    state.insert_body("a".to_string(), make_body_info(1));
    state.insert_body("b".to_string(), make_body_info(2));

    assert!(
        state.single_body().is_none(),
        "multiple bodies should return None"
    );
}

// --- round-trip: param_mapping → get_body ---

#[test]
#[timeout(30000)]
fn param_mapping_to_body_lookup_round_trip() {
    let mut state = ClosureState::new();
    state.insert_body("def_closure_1".to_string(), make_body_info(100));
    state.insert_param_mapping("my_fn".to_string(), "def_closure_1".to_string());

    let def_id = state.def_id_for_param("my_fn").unwrap();
    let info = state
        .get_body(def_id)
        .expect("body lookup via param mapping");
    assert_eq!(info.body, Some(PureExpr::Int(100)));
}

// --- ensures_exprs field ---

#[test]
#[timeout(30000)]
fn body_with_ensures_exprs_preserves_them() {
    let mut state = ClosureState::new();
    let info = ClosureBodyInfo {
        param_name: Some("clos".to_string()),
        body: Some(PureExpr::Bool(true)),
        param_names: vec!["a".to_string()],
        capture_names: vec!["cap".to_string()],
        ensures_exprs: Some(vec![PureExpr::Bool(false)]),
        requires_exprs: None,
    };
    state.insert_body("ens".to_string(), info);

    let stored = state.get_body("ens").unwrap();
    assert_eq!(stored.capture_names, vec!["cap"]);
    let ens = stored
        .ensures_exprs
        .as_ref()
        .expect("ensures should be Some");
    assert_eq!(ens.len(), 1);
    assert_eq!(ens[0], PureExpr::Bool(false));
}

#[test]
#[timeout(30000)]
fn body_info_preserves_missing_body_for_ensures_only_registration() {
    let mut state = ClosureState::new();
    let info = ClosureBodyInfo {
        param_name: None,
        body: None,
        param_names: vec!["x".to_string()],
        capture_names: vec![],
        ensures_exprs: Some(vec![PureExpr::Bool(true)]),
        requires_exprs: None,
    };
    state.insert_body("ensures_only".to_string(), info);

    let stored = state
        .get_body("ensures_only")
        .expect("body info should exist");
    assert_eq!(stored.body, None);
    assert_eq!(stored.param_names, vec!["x"]);
}
