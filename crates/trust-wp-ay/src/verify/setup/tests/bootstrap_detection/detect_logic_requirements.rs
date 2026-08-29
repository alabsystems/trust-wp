// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::*;
// =============================================================================
// Tests for detect_logic_requirements coverage gaps
// =============================================================================

/// Test that `needs_array_theory` is set when an expression contains
/// `index_logic` on a `Final(View(var))` receiver. This pattern is produced by
/// IndexMut extern spec postconditions and requires Array store/select. (#1317)
#[test]
#[timeout(30000)]
fn seq_index_on_final_triggers_array_theory_detection() {
    use crate::expr_seq::expr_has_seq_index_on_final;

    // Final(View(Var("v"))).index_logic(Var("i"))
    let index_on_final = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::View(Arc::new(
            PureExpr::Var("v".to_string(), None),
        ))))),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Var("i".to_string(), None)],
    };

    assert!(
        expr_has_seq_index_on_final(&index_on_final),
        "index_logic on Final(View(var)) should be detected"
    );

    let (_use_quantifiers, needs_array_theory, _needs_custom_sorts) =
        detect_logic_requirements(&[], &[index_on_final], &[], None, None, None);
    assert!(
        needs_array_theory,
        "seq index on final receiver should set needs_array_theory (#1317)"
    );
}

/// Negative test: `index_logic` without a `Final` receiver should NOT trigger
/// needs_array_theory (on its own — other detection paths may still fire).
#[test]
#[timeout(30000)]
fn seq_index_without_final_does_not_trigger_array_theory() {
    use crate::expr_seq::expr_has_seq_index_on_final;

    // View(Var("v")).index_logic(Var("i")) — no Final
    let index_no_final = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Var("i".to_string(), None)],
    };

    assert!(
        !expr_has_seq_index_on_final(&index_no_final),
        "index_logic without Final receiver should not be detected"
    );
}

/// Test that `context_exprs` are scanned by `detect_logic_requirements`.
/// All existing tests use empty context_exprs; this verifies the third input path.
#[test]
#[timeout(30000)]
fn context_exprs_trigger_quantifier_detection() {
    use crate::expr::expr_has_closure_spec_method;

    let postcondition_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("result".to_string(), None),
        ],
    };

    // Verify detection predicate fires
    assert!(
        expr_has_closure_spec_method(&postcondition_call),
        "postcondition method should be detected as closure spec"
    );

    // Place the closure spec method in context_exprs only (not requires or ensures)
    let (use_quantifiers, _needs_array, _needs_custom) =
        detect_logic_requirements(&[], &[], &[&postcondition_call], None, None, None);
    assert!(
        use_quantifiers,
        "closure spec method in context_exprs should trigger use_quantifiers"
    );
}

/// Test that tuple function calls (e.g., `__trust_wp_tuple2(a, b)`) in ensures
/// trigger quantifier escalation.
#[test]
#[timeout(30000)]
fn tuple_fn_in_ensures_triggers_quantifier_detection() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let tuple_call = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("b".to_string(), None),
        ],
    };

    let (use_quantifiers, _needs_array, _needs_custom) =
        detect_logic_requirements(&[], &[tuple_call], &[], None, None, None);
    assert!(
        use_quantifiers,
        "tuple function call in ensures should trigger use_quantifiers"
    );
}

/// Test that closure spec method `precondition` in requires triggers detection.
#[test]
#[timeout(30000)]
fn closure_precondition_in_requires_triggers_quantifier_detection() {
    let precondition_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![PureExpr::Var("args".to_string(), None)],
    };

    let (use_quantifiers, _needs_array, _needs_custom) =
        detect_logic_requirements(&[precondition_call], &[], &[], None, None, None);
    assert!(
        use_quantifiers,
        "closure precondition in requires should trigger use_quantifiers"
    );
}

/// Test that `needs_array_theory` remains false when Seq method calls are absent
/// and no index_on_final pattern exists.
#[test]
#[timeout(30000)]
fn no_seq_patterns_leaves_array_theory_false() {
    let simple_ensure = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );

    let (_use_quantifiers, needs_array_theory, _needs_custom) =
        detect_logic_requirements(&[], &[simple_ensure], &[], None, None, None);
    assert!(
        !needs_array_theory,
        "simple arithmetic should not set needs_array_theory"
    );
}
