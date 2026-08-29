// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `bool_uf.rs` post-encoding invariant fast paths under
//! sort drift (#2620).
//!
//! Covers trivial invariant detection, non-trivial body inlining, and
//! forall-scope axiom materialization after sort drift between
//! `infer_encoded_sort` and actual encoded term sorts.

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::AYEncoder;

#[test]
#[timeout(30000)]
fn hashmap_list_predicate_restores_seq_index_receiver_to_list_sort() {
    let mut encoder = AYEncoder::new_all();
    let list_dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Nil".to_string(),
            fields: vec![],
        }],
    };
    encoder.ensure_datatype_declared(&list_dt);

    let seq_sort = encoder.get_seq_sort();
    encoder
        .get_or_declare_var("buckets", seq_sort)
        .expect("declare buckets seq");
    let bucket = PureExpr::MethodCall {
        receiver: std::sync::Arc::new(PureExpr::Var("buckets".to_string(), Some(ExprSort::Seq))),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };

    let result = encoder
        .encode_bool_method_predicate(&bucket, "no_double_binding", &[], None)
        .expect("predicate encoding should restore Seq element to List");
    let children = encoder.solver.term_children(result);
    assert_eq!(children.len(), 1);
    assert_eq!(
        encoder.solver.get_sort(children[0]),
        Sort::Datatype(list_dt).as_term_sort()
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name == "method_no_double_binding_1_i"),
        "hashmap List predicate should not be declared over erased Int carrier"
    );
}

#[test]
#[timeout(30000)]
fn produces_datatype_visited_carrier_coerces_to_seq() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let list_dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Nil".to_string(),
            fields: vec![DatatypeField {
                name: "tag".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&list_dt);
    let list_sort = Sort::Datatype(list_dt);
    encoder
        .get_or_declare_var("visited", list_sort)
        .expect("declare datatype-backed visited value");

    let produces = PureExpr::MethodCall {
        receiver: Box::new(PureExpr::Var("iter".to_string(), None)).into(),
        method: "produces".to_string(),
        args: vec![
            PureExpr::Var("visited".to_string(), None),
            PureExpr::Var("next".to_string(), None),
        ],
    };

    let result = encoder.encode_pure(&produces);
    assert!(
        result.is_ok(),
        "datatype-backed visited value should be bridged into the Seq slot: {result:?}"
    );
}

/// When `infer_encoded_sort` returns Int but the actual encoded term has a
/// Datatype sort, the pre-encoding symbol (`pre_smt_name`) differs from the
/// post-encoding symbol (`smt_name`). A trivial type invariant registered
/// under the Datatype-sorted symbol should still fire via the post-encoding
/// fast path instead of falling through to UF encoding.
#[test]
#[timeout(30000)]
fn trivial_invariant_found_after_sort_drift() {
    use trust_wp_core::{formula::PureExpr, logic::type_invariant_method_name};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a simple datatype
    let test_dt = DatatypeSort {
        name: "DriftType".to_string(),
        constructors: vec![ay_dpll::api::DatatypeConstructor {
            name: "DriftTypeCtor".to_string(),
            fields: vec![ay_dpll::api::DatatypeField {
                name: "val".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&test_dt);
    let dt_sort = Sort::Datatype(test_dt);

    // Register a trivial (body = true) type invariant under the Datatype sort.
    // This registers the smt_name with the Datatype sort tag, e.g.,
    // "method___trust_wp_invariant_DriftType_1_d<hex>".
    encoder
        .register_type_invariant("DriftType", "self", dt_sort.clone(), &PureExpr::Bool(true))
        .expect("registration should succeed");

    // Create sort drift: the variable's term is Datatype-sorted, but
    // var_sorts records Int. infer_encoded_sort will find Int in var_sorts,
    // producing a pre_smt_name with the Int tag. method_param_sort will
    // see the actual Datatype sort on the term, producing a different smt_name.
    let dt_term = encoder.solver.declare_const("drift_x", dt_sort);
    encoder.insert_var("drift_x".to_string(), dt_term);
    encoder.insert_var_sort("drift_x".to_string(), Sort::Int);

    // Encode a call to the type invariant method.
    let method = type_invariant_method_name("DriftType");
    let receiver = PureExpr::Var("drift_x".to_string(), None);
    let result = encoder
        .encode_bool_method_predicate(&receiver, &method, &[], None)
        .expect("encoding should succeed");

    // The result should be constant `true` from the trivial invariant fast
    // path, not a UF application. Verify by asserting NOT(result) → UNSAT.
    let not_result = encoder.solver.not(result);
    encoder.solver.assert_term(not_result);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, crate::SolveResult::Unsat(_)),
        "trivial invariant should return true even after sort drift, got {sat:?}"
    );
}

/// When sort drift occurs and a non-trivial invariant body is registered
/// under the post-encoding symbol, the post-encoding inline path should
/// find the axiom and inline the body directly (instead of falling through
/// to UF encoding that requires E-matching).
#[test]
#[timeout(30000)]
fn invariant_body_inlined_after_sort_drift() {
    use trust_wp_core::{formula::PureExpr, logic::type_invariant_method_name};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let test_dt = DatatypeSort {
        name: "StrictType".to_string(),
        constructors: vec![ay_dpll::api::DatatypeConstructor {
            name: "StrictTypeCtor".to_string(),
            fields: vec![ay_dpll::api::DatatypeField {
                name: "val".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&test_dt);
    let dt_sort = Sort::Datatype(test_dt);

    // Register a non-trivial invariant with body = `false`. This is
    // non-trivial (not the literal `true`) so the trivial fast path
    // won't fire. The body doesn't reference `self` so it encodes
    // correctly regardless of receiver sort.
    encoder
        .register_type_invariant(
            "StrictType",
            "self",
            dt_sort.clone(),
            &PureExpr::Bool(false),
        )
        .expect("registration should succeed");

    // Create sort drift: var_sorts says Int, but actual term is Datatype.
    let dt_term = encoder.solver.declare_const("strict_x", dt_sort);
    encoder.insert_var("strict_x".to_string(), dt_term);
    encoder.insert_var_sort("strict_x".to_string(), Sort::Int);

    let method = type_invariant_method_name("StrictType");
    let receiver = PureExpr::Var("strict_x".to_string(), None);
    let result = encoder
        .encode_bool_method_predicate(&receiver, &method, &[], None)
        .expect("encoding should succeed");

    // The inlined body is `false`. Asserting it directly should be UNSAT.
    encoder.solver.assert_term(result);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, crate::SolveResult::Unsat(_)),
        "inlined invariant body (false) should make the formula UNSAT, got {sat:?}"
    );
}

/// Forall-only scopes skip the inline fast path but the retry UF should
/// still have a matching quantified axiom via materialization (#2620, AC3).
#[test]
#[timeout(30000)]
fn invariant_axiom_materialized_for_forall_scope_sort_drift() {
    use trust_wp_core::{formula::PureExpr, logic::type_invariant_method_name};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let test_dt = DatatypeSort {
        name: "ForallType".to_string(),
        constructors: vec![ay_dpll::api::DatatypeConstructor {
            name: "ForallTypeCtor".to_string(),
            fields: vec![ay_dpll::api::DatatypeField {
                name: "val".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&test_dt);
    let dt_sort = Sort::Datatype(test_dt);

    // Register a non-trivial invariant with body `false`.
    encoder
        .register_type_invariant(
            "ForallType",
            "self",
            dt_sort.clone(),
            &PureExpr::Bool(false),
        )
        .expect("registration should succeed");

    // Create sort drift
    let dt_term = encoder.solver.declare_const("forall_x", dt_sort);
    encoder.insert_var("forall_x".to_string(), dt_term);
    encoder.insert_var_sort("forall_x".to_string(), Sort::Int);

    // Simulate forall-only scope: quantifier_depth > 0, exists == 0
    encoder.quantifier_state.inc_quantifier_depth();

    let method = type_invariant_method_name("ForallType");
    let receiver = PureExpr::Var("forall_x".to_string(), None);
    let result = encoder
        .encode_bool_method_predicate(&receiver, &method, &[], None)
        .expect("encoding should succeed");

    encoder.quantifier_state.dec_quantifier_depth();

    // Verify: the ground pool has a defining axiom for the retry symbol.
    let method_name = type_invariant_method_name("ForallType");
    let u_tag = AYEncoder::method_sort_tag(&Sort::Uninterpreted("ForallType".to_string()));
    let retry_symbol = format!("method_{method_name}_1_{u_tag}");

    use super::super::ground_pool::AxiomKind;
    let has_retry_axiom = encoder
        .ground_pool
        .axioms()
        .iter()
        .any(|a| a.fn_symbol == retry_symbol && a.kind == AxiomKind::Defining);
    assert!(
        has_retry_axiom,
        "materialize_retry_type_invariant_symbol should register a defining \
         axiom under the retry symbol {retry_symbol}"
    );

    // Assert inv(forall_x) — since the body is `false`, this should be
    // UNSAT via the materialized axiom.
    encoder.solver.assert_term(result);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, crate::SolveResult::Unsat(_)),
        "forall-scope invariant with body `false` should be UNSAT via \
         materialized axiom, got {sat:?}"
    );
}
