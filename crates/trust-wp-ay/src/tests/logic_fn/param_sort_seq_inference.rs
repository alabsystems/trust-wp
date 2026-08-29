// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq inference nesting coverage for logic function parameter sorts.
//!
//! Verifies that Seq-method receivers are correctly inferred as Seq-sorted
//! even when nested inside Old, Final, Exists, Let, View, LetAssume, and
//! Closure wrappers. (#1552, P1-1050)
//!
//! Split from param_sort_tests.rs per #2251.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Helper: register a logic function and return its FuncDecl domain sorts.
fn register_and_get_domain_sorts(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
) -> Vec<ay_dpll::api::Sort> {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .register_logic_fn(logic_fn)
        .expect("registration should succeed");
    let smt_name = trust_wp_core::logic::logic_fn_smt_name(logic_fn.name());
    let decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .unwrap_or_else(|| {
            panic!(
                "FuncDecl for '{}' (SMT: '{}') should be registered",
                logic_fn.name(),
                smt_name
            )
        });
    decl.domain().to_vec()
}

fn make_open_logic_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
    LogicFnDef::new(
        name.to_string(),
        format!("test::{name}"),
        params.into_iter().map(String::from).collect(),
        body,
    )
    .with_mode(LogicMode::Open)
}

fn is_seq_sort(sort: &ay_dpll::api::Sort) -> bool {
    sort.is_seq()
}

/// s.len() nested inside Old() should still infer s as Seq-sorted.
#[test]
#[timeout(30000)]
fn test_seq_inference_through_old_nesting() {
    let logic_fn = make_open_logic_fn(
        "old_len",
        vec!["s"],
        PureExpr::Old(Arc::new(method_call(var("s"), "len", vec![]))),
    );
    let domain = register_and_get_domain_sorts(&logic_fn);
    assert_eq!(domain.len(), 1, "should have one parameter");
    assert!(
        is_seq_sort(&domain[0]),
        "s should be inferred as Seq after Old nesting, got: {:?}",
        domain[0]
    );
}

/// Final(s.len()) should preserve the Seq receiver sort through registration.
/// This used to panic during axiom encoding; keep the positive assertion as a
/// regression guard for the fixed Final nesting path. (#1552)
#[test]
#[timeout(30000)]
fn test_seq_inference_through_final_nesting_preserves_seq_sort() {
    let logic_fn = make_open_logic_fn(
        "final_len",
        vec!["s"],
        PureExpr::Final(Arc::new(method_call(var("s"), "len", vec![]))),
    );
    let domain = register_and_get_domain_sorts(&logic_fn);
    assert!(
        is_seq_sort(&domain[0]),
        "s should be inferred as Seq after Final nesting, got: {:?}",
        domain[0]
    );
}

/// s.len() nested inside Exists body should still infer s as Seq-sorted.
#[test]
#[timeout(30000)]
fn test_seq_inference_through_exists_nesting() {
    let logic_fn = make_open_logic_fn(
        "has_positive",
        vec!["s"],
        exists(
            "i",
            gt(method_call(var("s"), "index", vec![var("i")]), int(0)),
        ),
    );
    let domain = register_and_get_domain_sorts(&logic_fn);
    assert_eq!(domain.len(), 1);
    assert!(
        is_seq_sort(&domain[0]),
        "s should be inferred as Seq after Exists nesting, got: {:?}",
        domain[0]
    );
}

/// s.len() inside Let value should infer s as Seq-sorted.
#[test]
#[timeout(30000)]
fn test_seq_inference_through_let_value_nesting() {
    let logic_fn = make_open_logic_fn(
        "let_len",
        vec!["s"],
        let_bind("n", method_call(var("s"), "len", vec![]), var("n")),
    );
    let domain = register_and_get_domain_sorts(&logic_fn);
    assert_eq!(domain.len(), 1);
    assert!(
        is_seq_sort(&domain[0]),
        "s should be inferred as Seq after Let value nesting, got: {:?}",
        domain[0]
    );
}

/// Closure bodies in logic functions now fall back to a fresh constant (#985).
/// Previously this returned an error; now it encodes conservatively.
#[test]
#[timeout(30000)]
fn test_seq_inference_closure_unsupported_error() {
    let logic_fn = make_open_logic_fn(
        "closure_len",
        vec!["s"],
        PureExpr::Closure {
            params: vec![("_x".to_string(), None)],
            body: Arc::new(method_call(var("s"), "len", vec![])),
        },
    );
    let mut encoder = AYEncoder::new_with_quantifiers();
    let result = encoder.register_logic_fn(&logic_fn);
    // Registration now succeeds with conservative encoding (#985)
    assert!(
        result.is_ok(),
        "Closure in logic body should now encode conservatively (#985), \
         but registration failed: {result:?}"
    );
}

/// s.len() inside View should infer s as Seq-sorted.
#[test]
#[timeout(30000)]
fn test_seq_inference_through_view_nesting() {
    let logic_fn = make_open_logic_fn(
        "view_len",
        vec!["s"],
        view(method_call(var("s"), "len", vec![])),
    );
    let domain = register_and_get_domain_sorts(&logic_fn);
    assert_eq!(domain.len(), 1);
    assert!(
        is_seq_sort(&domain[0]),
        "s should be inferred as Seq after View nesting, got: {:?}",
        domain[0]
    );
}

/// s.len() inside LetAssume should infer s as Seq-sorted.
#[test]
#[timeout(30000)]
fn test_seq_inference_through_let_assume_nesting() {
    let logic_fn = make_open_logic_fn(
        "assume_len",
        vec!["s"],
        let_assume(
            gt(method_call(var("s"), "len", vec![]), int(0)),
            method_call(var("s"), "len", vec![]),
        ),
    );
    let domain = register_and_get_domain_sorts(&logic_fn);
    assert_eq!(domain.len(), 1);
    assert!(
        is_seq_sort(&domain[0]),
        "s should be inferred as Seq after LetAssume nesting, got: {:?}",
        domain[0]
    );
}
