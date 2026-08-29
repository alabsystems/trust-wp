// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::*;
// =============================================================================
// Tests for detect_logic_requirements — needs_array_theory path
// =============================================================================

/// Seq index on Final receiver should trigger needs_array_theory.
#[test]
#[timeout(30000)]
fn detect_logic_seq_index_on_final_triggers_array_theory() {
    let seq_idx = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("v".into(), None),
        ))))),
        method: "index_logic".into(),
        args: vec![PureExpr::Int(0)],
    };

    let (_use_q, needs_array, _custom) =
        detect_logic_requirements(&[], &[seq_idx], &[], None, None, None);
    assert!(
        needs_array,
        "Seq index on Final receiver should trigger needs_array_theory (#1317)"
    );
}

/// Pure arithmetic should not trigger needs_array_theory.
#[test]
#[timeout(30000)]
fn detect_logic_arithmetic_does_not_trigger_array_theory() {
    let arith = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let (_use_q, needs_array, _custom) =
        detect_logic_requirements(&[], &[arith], &[], None, None, None);
    assert!(
        !needs_array,
        "plain arithmetic should not set needs_array_theory"
    );
}

/// Empty adt_decls should NOT set needs_custom_sorts (the empty HashMap case).
#[test]
#[timeout(30000)]
fn detect_logic_empty_adt_decls_does_not_trigger_custom_sorts() {
    let empty_decls: std::collections::HashMap<String, trust_wp_core::logic::AdtDecl> =
        std::collections::HashMap::new();

    let (_use_q, _needs_array, needs_custom) =
        detect_logic_requirements(&[], &[], &[], None, None, Some(&empty_decls));
    assert!(
        !needs_custom,
        "empty adt_decls should not set needs_custom_sorts"
    );
}

/// Logic functions with constructor matches in their body should trigger
/// needs_custom_sorts even when goal expressions don't mention constructors.
#[test]
#[timeout(30000)]
fn detect_logic_logic_fn_body_constructor_triggers_custom_sorts() {
    let logic_fn = make_logic_fn_with_adt_param("sum", "self");

    let (_use_q, _needs_array, needs_custom) =
        detect_logic_requirements(&[], &[], &[], Some(&[logic_fn]), None, None);
    assert!(
        needs_custom,
        "logic fn body with constructor match should set needs_custom_sorts (#994)"
    );
}
