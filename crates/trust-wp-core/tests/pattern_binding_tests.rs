// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `Pattern::binds_name`, `Pattern::bound_names`,
//! `Pattern::rename_binding`, and `Pattern::collect_bindings`.
//!
//! These methods are used by substitution and free-variable analysis to shadow
//! pattern-bound names. Bugs here can cause unsound substitution in match arms.

use std::collections::HashMap;

use trust_wp_core::formula::{Pattern, PureExpr};

// ── binds_name ──────────────────────────────────────────────────

#[test]
fn binds_name_wildcard_never_binds() {
    assert!(!Pattern::Wildcard.binds_name("x"));
}

#[test]
fn binds_name_literal_never_binds() {
    assert!(!Pattern::Literal(PureExpr::Int(42)).binds_name("x"));
    assert!(!Pattern::Literal(PureExpr::Bool(true)).binds_name("true"));
}

#[test]
fn binds_name_binding_matches_exact_name() {
    let pat = Pattern::Binding("x".to_string());
    assert!(pat.binds_name("x"));
    assert!(!pat.binds_name("y"));
}

#[test]
fn binds_name_constructor_without_inner() {
    let pat = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    assert!(!pat.binds_name("x"));
}

#[test]
fn binds_name_constructor_with_inner_binding() {
    let pat = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("val".to_string()))),
    };
    assert!(pat.binds_name("val"));
    assert!(!pat.binds_name("other"));
}

#[test]
fn binds_name_tuple_checks_all_elements() {
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Wildcard,
        Pattern::Binding("b".to_string()),
    ]);
    assert!(pat.binds_name("a"));
    assert!(pat.binds_name("b"));
    assert!(!pat.binds_name("c"));
}

#[test]
fn binds_name_nested_constructor_in_tuple() {
    let pat = Pattern::Tuple(vec![
        Pattern::Constructor {
            name: "Some".to_string(),
            inner: Some(Box::new(Pattern::Binding("inner_val".to_string()))),
        },
        Pattern::Binding("second".to_string()),
    ]);
    assert!(pat.binds_name("inner_val"));
    assert!(pat.binds_name("second"));
    assert!(!pat.binds_name("missing"));
}

// ── bound_names ─────────────────────────────────────────────────

#[test]
fn bound_names_wildcard_empty() {
    assert!(Pattern::Wildcard.bound_names().is_empty());
}

#[test]
fn bound_names_literal_empty() {
    assert!(Pattern::Literal(PureExpr::Int(0)).bound_names().is_empty());
}

#[test]
fn bound_names_binding_returns_name() {
    assert_eq!(Pattern::Binding("x".to_string()).bound_names(), vec!["x"]);
}

#[test]
fn bound_names_constructor_none_inner() {
    let pat = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    assert!(pat.bound_names().is_empty());
}

#[test]
fn bound_names_constructor_with_binding() {
    let pat = Pattern::Constructor {
        name: "Ok".to_string(),
        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
    };
    assert_eq!(pat.bound_names(), vec!["v"]);
}

#[test]
fn bound_names_tuple_collects_all() {
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Binding("b".to_string()),
        Pattern::Wildcard,
    ]);
    assert_eq!(pat.bound_names(), vec!["a", "b"]);
}

#[test]
fn bound_names_nested_preserves_order() {
    // Tuple(Constructor(Binding("inner")), Binding("outer"))
    let pat = Pattern::Tuple(vec![
        Pattern::Constructor {
            name: "Some".to_string(),
            inner: Some(Box::new(Pattern::Binding("inner".to_string()))),
        },
        Pattern::Binding("outer".to_string()),
    ]);
    assert_eq!(pat.bound_names(), vec!["inner", "outer"]);
}

// ── rename_binding ──────────────────────────────────────────────

#[test]
fn rename_binding_wildcard_unchanged() {
    assert_eq!(
        Pattern::Wildcard.rename_binding("x", "y"),
        Pattern::Wildcard
    );
}

#[test]
fn rename_binding_literal_unchanged() {
    let pat = Pattern::Literal(PureExpr::Int(42));
    assert_eq!(pat.rename_binding("x", "y"), pat);
}

#[test]
fn rename_binding_matching_name() {
    let pat = Pattern::Binding("x".to_string());
    assert_eq!(
        pat.rename_binding("x", "x_α0"),
        Pattern::Binding("x_α0".to_string())
    );
}

#[test]
fn rename_binding_non_matching_name() {
    let pat = Pattern::Binding("y".to_string());
    assert_eq!(
        pat.rename_binding("x", "x_α0"),
        Pattern::Binding("y".to_string())
    );
}

#[test]
fn rename_binding_constructor_inner() {
    let pat = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("z".to_string()))),
    };
    assert_eq!(
        pat.rename_binding("z", "z_α0"),
        Pattern::Constructor {
            name: "Some".to_string(),
            inner: Some(Box::new(Pattern::Binding("z_α0".to_string()))),
        }
    );
}

#[test]
fn rename_binding_constructor_none_inner_unchanged() {
    let pat = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    assert_eq!(pat.rename_binding("x", "y"), pat);
}

#[test]
fn rename_binding_tuple_renames_matching() {
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Binding("b".to_string()),
    ]);
    assert_eq!(
        pat.rename_binding("a", "a_α0"),
        Pattern::Tuple(vec![
            Pattern::Binding("a_α0".to_string()),
            Pattern::Binding("b".to_string()),
        ])
    );
}

#[test]
fn rename_binding_nested_constructor_in_tuple() {
    let pat = Pattern::Tuple(vec![
        Pattern::Constructor {
            name: "Some".to_string(),
            inner: Some(Box::new(Pattern::Binding("inner".to_string()))),
        },
        Pattern::Binding("outer".to_string()),
    ]);
    assert_eq!(
        pat.rename_binding("inner", "inner_α0"),
        Pattern::Tuple(vec![
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("inner_α0".to_string()))),
            },
            Pattern::Binding("outer".to_string()),
        ])
    );
}

// ── collect_bindings (shadow removal) ───────────────────────────

#[test]
fn collect_bindings_wildcard_leaves_subs_unchanged() {
    let mut subs = HashMap::from([
        ("x".to_string(), PureExpr::Int(1)),
        ("y".to_string(), PureExpr::Int(2)),
    ]);
    Pattern::Wildcard.collect_bindings(&mut subs);
    assert_eq!(subs.len(), 2);
}

#[test]
fn collect_bindings_literal_leaves_subs_unchanged() {
    let mut subs = HashMap::from([("x".to_string(), PureExpr::Int(1))]);
    Pattern::Literal(PureExpr::Int(0)).collect_bindings(&mut subs);
    assert_eq!(subs.len(), 1);
}

#[test]
fn collect_bindings_binding_removes_matching_name() {
    let mut subs = HashMap::from([
        ("x".to_string(), PureExpr::Int(1)),
        ("y".to_string(), PureExpr::Int(2)),
    ]);
    Pattern::Binding("x".to_string()).collect_bindings(&mut subs);
    assert!(!subs.contains_key("x"), "x should be shadowed (removed)");
    assert!(subs.contains_key("y"), "y should be untouched");
}

#[test]
fn collect_bindings_binding_missing_name_is_noop() {
    let mut subs = HashMap::from([("y".to_string(), PureExpr::Int(2))]);
    Pattern::Binding("x".to_string()).collect_bindings(&mut subs);
    assert_eq!(subs.len(), 1);
}

#[test]
fn collect_bindings_constructor_removes_inner_binding() {
    let mut subs = HashMap::from([
        ("val".to_string(), PureExpr::Int(10)),
        ("other".to_string(), PureExpr::Int(20)),
    ]);
    let pat = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("val".to_string()))),
    };
    pat.collect_bindings(&mut subs);
    assert!(!subs.contains_key("val"), "val should be shadowed");
    assert!(subs.contains_key("other"), "other should be untouched");
}

#[test]
fn collect_bindings_constructor_none_inner_is_noop() {
    let mut subs = HashMap::from([("x".to_string(), PureExpr::Int(1))]);
    let pat = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    pat.collect_bindings(&mut subs);
    assert_eq!(subs.len(), 1);
}

#[test]
fn collect_bindings_tuple_removes_all_bound_names() {
    let mut subs = HashMap::from([
        ("a".to_string(), PureExpr::Int(1)),
        ("b".to_string(), PureExpr::Int(2)),
        ("c".to_string(), PureExpr::Int(3)),
    ]);
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Wildcard,
        Pattern::Binding("c".to_string()),
    ]);
    pat.collect_bindings(&mut subs);
    assert!(!subs.contains_key("a"), "a should be shadowed");
    assert!(subs.contains_key("b"), "b should be untouched");
    assert!(!subs.contains_key("c"), "c should be shadowed");
}

#[test]
fn collect_bindings_nested_pattern_removes_deep_bindings() {
    let mut subs = HashMap::from([
        ("inner".to_string(), PureExpr::Int(1)),
        ("outer".to_string(), PureExpr::Int(2)),
        ("keep".to_string(), PureExpr::Int(3)),
    ]);
    let pat = Pattern::Tuple(vec![
        Pattern::Constructor {
            name: "Some".to_string(),
            inner: Some(Box::new(Pattern::Binding("inner".to_string()))),
        },
        Pattern::Binding("outer".to_string()),
    ]);
    pat.collect_bindings(&mut subs);
    assert!(
        !subs.contains_key("inner"),
        "nested inner should be shadowed"
    );
    assert!(!subs.contains_key("outer"), "outer should be shadowed");
    assert!(subs.contains_key("keep"), "keep should be untouched");
}
