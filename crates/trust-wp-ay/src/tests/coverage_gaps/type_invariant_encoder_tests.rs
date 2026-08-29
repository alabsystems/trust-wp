// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for encoder type invariant registration and container element
//! invariant assertion functions. Covers pub(crate) functions with
//! zero prior test coverage:
//! - `AYEncoder::register_type_invariant`
//! - `AYEncoder::assert_container_element_invariant`
//! - `AYEncoder::assert_container_element_invariant_body`
//! - `AYEncoder::assert_registered_container_element_invariants_for_index`
//! - `verify::assert_container_element_invariants`

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::{
    encoder::{AYEncoder, ContainerElementInvariantSpec},
    verify::assert_container_element_invariants,
};

/// Helper: create the Seq sort that `get_seq_sort()` returns internally.
fn seq_sort() -> Sort {
    Sort::seq(Sort::Int)
}

/// Helper: build a requires-style MethodCall expression matching
/// `extract_invariant_receiver_var`.
fn invariant_method_call(param_name: &str, method_name: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(param_name.to_string(), None)),
        method: method_name.to_string(),
        args: vec![],
    }
}

#[test]
#[timeout(30000)]
fn test_register_type_invariant_trivial_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let result =
        encoder.register_type_invariant("TrivialType", "self", Sort::Int, &PureExpr::Bool(true));
    assert!(result.is_ok());
    // Trivial invariant should be counted and recorded
    assert_eq!(encoder.decls().type_invariant_count(), 1);
    assert_eq!(encoder.decls().trivial_invariant_count(), 1);
}

#[test]
#[timeout(30000)]
fn test_register_type_invariant_nontrivial_body() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let result = encoder.register_type_invariant("NonZero", "self", Sort::Int, &body);
    assert!(result.is_ok());
    assert_eq!(encoder.decls().type_invariant_count(), 1);
    // Nontrivial invariant should NOT be in the trivial set
    assert!(encoder.decls().trivial_invariants_is_empty());
}

#[test]
#[timeout(30000)]
fn test_register_type_invariant_idempotent() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("NonZero", "self", Sort::Int, &body)
        .unwrap();
    encoder
        .register_type_invariant("NonZero", "self", Sort::Int, &body)
        .unwrap();
    // Should have only registered once (idempotency via logic_fn_axioms check)
    assert_eq!(encoder.decls().type_invariant_count(), 1);
}

#[test]
#[timeout(30000)]
fn test_register_type_invariant_ground_pool_entry() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("NonNeg", "self", Sort::Int, &body)
        .unwrap();
    assert!(
        !encoder.ground_pool_for_test().axioms().is_empty(),
        "ground pool should have the type invariant axiom"
    );
}

#[test]
#[timeout(30000)]
fn test_container_element_invariant_trivial_skips() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .register_type_invariant("TrivElem", "self", Sort::Int, &PureExpr::Bool(true))
        .unwrap();
    encoder.get_or_declare_var("v_view", seq_sort()).unwrap();
    let method_name = trust_wp_core::logic::type_invariant_method_name("TrivElem");
    let result = encoder.assert_container_element_invariant("v_view", &method_name);
    assert!(result.is_ok());
}

#[test]
#[timeout(30000)]
fn test_container_element_invariant_body_trivial_skips() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.get_or_declare_var("v_view", seq_sort()).unwrap();
    let result =
        encoder.assert_container_element_invariant_body("v_view", "self", &PureExpr::Bool(true));
    assert!(result.is_ok());
}

#[test]
#[timeout(30000)]
fn test_container_element_invariant_body_nontrivial() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.get_or_declare_var("v_view", seq_sort()).unwrap();
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let result = encoder.assert_container_element_invariant_body("v_view", "self", &body);
    assert!(result.is_ok());
    assert!(
        encoder.seq_state_for_test().needs_index_ground_terms(),
        "needs_index_ground_terms should be enabled"
    );
}

// ── assert_registered_container_element_invariants_for_index ────

/// No registered invariants → no-op Ok.
#[test]
#[timeout(30000)]
fn test_container_elem_inv_for_index_no_registered_is_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort();
    let seq_term = encoder.solver.fresh_var("s", ss);
    let idx = encoder.solver.int_const(0);
    let elem = encoder.solver.int_const(42);

    let result =
        encoder.assert_registered_container_element_invariants_for_index(seq_term, idx, elem);
    assert!(result.is_ok(), "no registered invariants should be a no-op");
}

/// Method-variant spec: registers an element invariant method and asserts it.
#[test]
#[timeout(30000)]
fn test_container_elem_inv_for_index_method_variant() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort();
    let seq_term = encoder.solver.fresh_var("s", ss);

    encoder.register_container_element_invariant(
        seq_term,
        ContainerElementInvariantSpec::Method {
            element_invariant_method: "is_positive".to_string(),
        },
    );

    let idx = encoder.solver.int_const(0);
    let elem = encoder.solver.int_const(42);

    let result =
        encoder.assert_registered_container_element_invariants_for_index(seq_term, idx, elem);
    assert!(result.is_ok(), "Method-variant spec should succeed");
}

/// Body-variant spec: registers an inline body and asserts it.
#[test]
#[timeout(30000)]
fn test_container_elem_inv_for_index_body_variant() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort();
    let seq_term = encoder.solver.fresh_var("s", ss);

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("elem".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    encoder.register_container_element_invariant(
        seq_term,
        ContainerElementInvariantSpec::Body {
            self_param: "elem".to_string(),
            body,
        },
    );

    let idx = encoder.solver.int_const(0);
    let elem = encoder.solver.int_const(42);

    let result =
        encoder.assert_registered_container_element_invariants_for_index(seq_term, idx, elem);
    assert!(result.is_ok(), "Body-variant spec should succeed");
}

/// Multiple specs registered on the same Seq term are all asserted.
#[test]
#[timeout(30000)]
fn test_container_elem_inv_for_index_multiple_specs() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort();
    let seq_term = encoder.solver.fresh_var("s", ss);

    encoder.register_container_element_invariant(
        seq_term,
        ContainerElementInvariantSpec::Method {
            element_invariant_method: "is_valid".to_string(),
        },
    );

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    encoder.register_container_element_invariant(
        seq_term,
        ContainerElementInvariantSpec::Body {
            self_param: "x".to_string(),
            body,
        },
    );

    let idx = encoder.solver.int_const(1);
    let elem = encoder.solver.int_const(7);

    let result =
        encoder.assert_registered_container_element_invariants_for_index(seq_term, idx, elem);
    assert!(result.is_ok(), "multiple specs should all be asserted");
}

/// Different Seq term has no registered invariants → no-op.
#[test]
#[timeout(30000)]
fn test_container_elem_inv_for_index_wrong_seq_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ss = seq_sort();
    let s1 = encoder.solver.fresh_var("s1", ss.clone());
    let s2 = encoder.solver.fresh_var("s2", ss);

    encoder.register_container_element_invariant(
        s1,
        ContainerElementInvariantSpec::Method {
            element_invariant_method: "is_ok".to_string(),
        },
    );

    let idx = encoder.solver.int_const(0);
    let elem = encoder.solver.int_const(0);
    let result = encoder.assert_registered_container_element_invariants_for_index(s2, idx, elem);
    assert!(result.is_ok(), "unregistered Seq term should be a no-op");
}

// ── assert_container_element_invariants (verify/mod.rs) ────────

/// None type_invariants → Ok.
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_none_invariants_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let result = assert_container_element_invariants(&mut encoder, &[], None);
    assert!(result.is_ok(), "None invariants should be a no-op");
}

/// Empty invariant slice → Ok.
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_empty_slice_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let result = assert_container_element_invariants(&mut encoder, &[], Some(&[]));
    assert!(result.is_ok(), "empty invariant slice should be a no-op");
}

/// Invariant without element_invariant_method → skipped.
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_no_element_method_skipped() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let inv = trust_wp_core::logic::TypeInvariantDef::new(
        "MyType".to_string(),
        "self".to_string(),
        PureExpr::Bool(true),
    );
    let requires = vec![invariant_method_call(
        "v",
        &trust_wp_core::logic::type_invariant_method_name("MyType"),
    )];
    let result = assert_container_element_invariants(&mut encoder, &requires, Some(&[inv]));
    assert!(
        result.is_ok(),
        "missing element_invariant_method should skip"
    );
}

/// Invariant with element_invariant_method but no matching requires → skipped.
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_no_matching_requires_skipped() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let inv = trust_wp_core::logic::TypeInvariantDef::new(
        "Vec".to_string(),
        "self".to_string(),
        PureExpr::Bool(true),
    )
    .with_element_invariant_method(Some("__trust_wp_invariant_Elem".to_string()));
    let requires = vec![invariant_method_call("v", "unrelated_method")];
    let result = assert_container_element_invariants(&mut encoder, &requires, Some(&[inv]));
    assert!(result.is_ok(), "no matching requires should skip");
}

/// Empty requires slice with valid invariant → no assertions (Ok).
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_empty_requires() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let inv = trust_wp_core::logic::TypeInvariantDef::new(
        "Vec".to_string(),
        "self".to_string(),
        PureExpr::Bool(true),
    )
    .with_element_invariant_method(Some("__trust_wp_invariant_Elem".to_string()));
    let result = assert_container_element_invariants(&mut encoder, &[], Some(&[inv]));
    assert!(
        result.is_ok(),
        "empty requires should produce no assertions"
    );
}

/// Matching requires + element invariant body → asserts via body path.
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_matching_body_path() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let elem_body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let elem_inv = trust_wp_core::logic::TypeInvariantDef::new(
        "Positive".to_string(),
        "self".to_string(),
        elem_body,
    );
    let elem_method_name = trust_wp_core::logic::type_invariant_method_name("Positive");

    let container_inv = trust_wp_core::logic::TypeInvariantDef::new(
        "Vec".to_string(),
        "self".to_string(),
        PureExpr::Bool(true),
    )
    .with_element_invariant_method(Some(elem_method_name.clone()));

    let container_method = trust_wp_core::logic::type_invariant_method_name("Vec");
    let requires = vec![invariant_method_call("v", &container_method)];

    encoder.get_or_declare_var("v_view", seq_sort()).unwrap();

    let result = assert_container_element_invariants(
        &mut encoder,
        &requires,
        Some(&[container_inv, elem_inv]),
    );
    assert!(result.is_ok(), "matching body path should succeed");
}

/// Matching requires + element method only (no body def) → asserts via method path.
#[test]
#[timeout(30000)]
fn test_verify_container_elem_inv_matching_method_path() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let elem_method_name = trust_wp_core::logic::type_invariant_method_name("Positive");

    let container_inv = trust_wp_core::logic::TypeInvariantDef::new(
        "Vec".to_string(),
        "self".to_string(),
        PureExpr::Bool(true),
    )
    .with_element_invariant_method(Some(elem_method_name));

    let container_method = trust_wp_core::logic::type_invariant_method_name("Vec");
    let requires = vec![invariant_method_call("v", &container_method)];

    encoder.get_or_declare_var("v_view", seq_sort()).unwrap();
    encoder
        .register_type_invariant("Positive", "self", Sort::Int, &PureExpr::Bool(true))
        .unwrap();

    let result =
        assert_container_element_invariants(&mut encoder, &requires, Some(&[container_inv]));
    assert!(result.is_ok(), "matching method path should succeed");
}

/// After registering a non-trivial type invariant, the `self` parameter's
/// var binding and var_sort must be restored so they don't leak into
/// subsequent encoder state. This covers the save/restore pattern in
/// `register_type_invariant_axiom` (type_invariant.rs:82-97).
#[test]
#[timeout(30000)]
fn test_register_type_invariant_restores_var_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Pre-condition: no binding for "self"
    assert!(
        encoder.var_sort("self").is_none(),
        "self should have no var_sort before registration"
    );

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("NonZero", "self", Sort::Int, &body)
        .expect("non-trivial type invariant should register");

    // Post-condition: self var_sort must be restored to None
    assert!(
        encoder.var_sort("self").is_none(),
        "self var_sort should be restored after type invariant registration"
    );
}

/// Var_sort restoration must also work when the type invariant uses a
/// Datatype sort (not just Int), since the bound variable's sort differs
/// from the default.
#[test]
#[timeout(30000)]
fn test_register_type_invariant_restores_datatype_var_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Use an uninterpreted sort (simulating a user-defined type)
    let custom_sort = Sort::Uninterpreted("NonNullOpt".to_string());

    // Pre-condition: no binding for "self"
    assert!(encoder.var_sort("self").is_none());

    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("self".to_string(), None)),
        BinOp::Ne,
        Arc::new(PureExpr::Int(0)),
    );
    encoder
        .register_type_invariant("NonNullOpt", "self", custom_sort, &body)
        .expect("datatype type invariant should register");

    // Post-condition: self var_sort must be cleaned up
    assert!(
        encoder.var_sort("self").is_none(),
        "self var_sort should be restored after datatype type invariant registration"
    );
}
