// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rewrite tests for type invariants.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::{formula::PureExpr, logic::type_invariant_method_name};

use super::{
    super::{
        discharge_trivial_inv_calls_expr, rewrite_parsed_contract_type_invariant_methods,
        rewrite_parsed_contract_type_invariant_methods_with_structural,
        rewrite_type_invariant_methods_expr,
    },
    common::collect_param_method_map,
};

#[test]
fn discharge_trivial_inv_rewrites_bare_inv_for_known_root_to_true() {
    // `inv(*x)` for a known parameter `x` with no registered invariant must
    // become `true` (the faithful semantics for primitives like `&mut i32`).
    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))],
    };
    let mut roots = std::collections::HashSet::new();
    roots.insert("x".to_string());
    assert_eq!(
        discharge_trivial_inv_calls_expr(&expr, &roots),
        PureExpr::Bool(true)
    );
}

#[test]
fn discharge_trivial_inv_rewrites_invariant_method_call_for_known_root() {
    // `x.invariant()` for a known trivial root also collapses to `true`.
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![],
    };
    let mut roots = std::collections::HashSet::new();
    roots.insert("x".to_string());
    assert_eq!(
        discharge_trivial_inv_calls_expr(&expr, &roots),
        PureExpr::Bool(true)
    );
}

#[test]
fn discharge_keeps_a_type_parameter_invariant_on_a_known_root() {
    // A parameter typed by a type parameter is a "trivial" root to the ADT
    // maps, but its invariant is the premise the generic body discharges its
    // own hand-overs with; collapsing it to `true` would leave every such
    // hand-over owing a clause nothing grants.
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("t".to_string(), None)),
        method: trust_wp_core::logic::type_param_invariant_method_name(0, "T"),
        args: vec![],
    };
    let mut roots = std::collections::HashSet::new();
    roots.insert("t".to_string());
    assert_eq!(discharge_trivial_inv_calls_expr(&expr, &roots), expr);
}

#[test]
fn discharge_trivial_inv_leaves_unknown_root_untouched() {
    // A root that is NOT a known trivial parameter is conservatively preserved,
    // so the type-qualified rewrite remains authoritative for invariant-bearing
    // types.
    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Var("z".to_string(), None)],
    };
    let roots = std::collections::HashSet::new(); // z not present
    assert_eq!(discharge_trivial_inv_calls_expr(&expr, &roots), expr);
}

#[test]
fn rewrites_param_invariant_to_type_specific_method() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        method: "invariant".to_string(),
        args: vec![],
    };

    let mut param_methods = HashMap::new();
    param_methods.insert("x".to_string(), type_invariant_method_name("NonZero"));

    let rewritten = rewrite_type_invariant_methods_expr(&expr, &param_methods, None);
    match rewritten {
        PureExpr::MethodCall { method, .. } => {
            assert_eq!(method, type_invariant_method_name("NonZero"));
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

#[test]
fn rewrites_result_invariant_to_type_specific_method() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("result".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![],
    };

    let rewritten = rewrite_type_invariant_methods_expr(
        &expr,
        &HashMap::new(),
        Some(&type_invariant_method_name("SmallNum")),
    );
    match rewritten {
        PureExpr::MethodCall { method, .. } => {
            assert_eq!(method, type_invariant_method_name("SmallNum"));
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

// --- inv(x) -> x.invariant() rewriting tests (#359) ---

#[test]
fn rewrite_inv_call_to_typed_invariant_method() {
    let mut param_methods = HashMap::new();
    param_methods.insert("x".to_string(), "__trust_wp_invariant_Foo".to_string());
    let result_method = None;

    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let result = rewrite_type_invariant_methods_expr(&expr, &param_methods, result_method);
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
            method: "__trust_wp_invariant_Foo".to_string(),
            args: vec![],
        },
        "inv(x) should rewrite to x.__trust_wp_invariant_Foo()"
    );
}

#[test]
fn rewrite_inv_result_to_typed_invariant_method() {
    let param_methods = HashMap::new();
    let result_method = Some("__trust_wp_invariant_Bar");

    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Var("result".to_string(), None)],
    };
    let result = rewrite_type_invariant_methods_expr(&expr, &param_methods, result_method);
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("result".to_string(), None)),
            method: "__trust_wp_invariant_Bar".to_string(),
            args: vec![],
        },
        "inv(result) should rewrite using result_method"
    );
}

#[test]
fn rewrite_inv_unknown_param_unchanged() {
    let param_methods = HashMap::new();
    let result_method: Option<&str> = None;

    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Var("y".to_string(), None)],
    };
    let result = rewrite_type_invariant_methods_expr(&expr, &param_methods, result_method);
    assert_eq!(
        result, expr,
        "inv(y) with no mapping should remain unchanged"
    );
}

#[test]
fn rewrite_inv_through_deref() {
    let mut param_methods = HashMap::new();
    param_methods.insert("x".to_string(), "__trust_wp_invariant_Foo".to_string());
    let result_method = None;

    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))],
    };
    let result = rewrite_type_invariant_methods_expr(&expr, &param_methods, result_method);
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None
            )))),
            method: "__trust_wp_invariant_Foo".to_string(),
            args: vec![],
        },
        "inv(*x) should rewrite through Deref to x.__trust_wp_invariant_Foo()"
    );
}

#[test]
fn rewrite_inv_multi_arg_unchanged() {
    let mut param_methods = HashMap::new();
    param_methods.insert("x".to_string(), "__trust_wp_invariant_Foo".to_string());
    let result_method = None;

    let expr = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("y".to_string(), None),
        ],
    };
    let result = rewrite_type_invariant_methods_expr(&expr, &param_methods, result_method);
    assert_eq!(
        result, expr,
        "inv(x, y) with multiple args should remain unchanged"
    );
}

#[test]
fn rewrite_type_invariants_preserves_forall_var_sort() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(trust_wp_core::formula::ExprSort::Seq),
        body: Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
            method: "invariant".to_string(),
            args: vec![],
        }),
        triggers: vec![vec![PureExpr::Var("x".to_string(), None)]],
    };

    let mut param_methods = HashMap::new();
    param_methods.insert("x".to_string(), "__trust_wp_invariant_Foo".to_string());

    let result = rewrite_type_invariant_methods_expr(&expr, &param_methods, None);
    match result {
        PureExpr::Forall { var_sort, body, .. } => {
            assert_eq!(var_sort, Some(trust_wp_core::formula::ExprSort::Seq));
            assert!(matches!(
                body.as_ref(),
                PureExpr::MethodCall { method, .. } if method == "__trust_wp_invariant_Foo"
            ));
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn rewrite_type_invariants_preserves_exists_var_sort() {
    let expr = PureExpr::Exists {
        var: "result".to_string(),
        var_sort: Some(trust_wp_core::formula::ExprSort::Int),
        body: Arc::new(PureExpr::LogicFnCall {
            name: "inv".to_string(),
            args: vec![PureExpr::Var("result".to_string(), None)],
        }),
        triggers: vec![],
    };

    let result = rewrite_type_invariant_methods_expr(
        &expr,
        &HashMap::new(),
        Some("__trust_wp_invariant_Result"),
    );
    match result {
        PureExpr::Exists { var_sort, body, .. } => {
            assert_eq!(var_sort, Some(trust_wp_core::formula::ExprSort::Int));
            assert!(matches!(
                body.as_ref(),
                PureExpr::MethodCall { method, .. } if method == "__trust_wp_invariant_Result"
            ));
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn rewrite_contract_covers_all_parsed_contract_expr_fields() {
    use crate::mir_analysis::{IndexedWrite, MutBorrowBody, SpannedBodyExpr};

    let invariant_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        method: "invariant".to_string(),
        args: vec![],
    };

    let expected = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        method: "__trust_wp_invariant_Foo".to_string(),
        args: vec![],
    };

    let final_values = HashMap::from([("x".to_string(), invariant_call.clone())]);

    let mut parsed = super::super::super::parsing::ParsedContract {
        requires: vec![invariant_call.clone()],
        ensures: vec![invariant_call.clone()],
        result_expr: Some(invariant_call.clone()),
        result_expr_spanned: Some(SpannedBodyExpr::unspanned(invariant_call.clone())),
        arg_names: vec![],
        call_assumptions: vec![invariant_call.clone()],
        pre_loop_call_assumptions: vec![invariant_call.clone()],
        call_obligations: vec![invariant_call.clone()],
        pre_loop_call_obligations: vec![invariant_call.clone()],
        post_loop_call_obligations: vec![invariant_call.clone()],
        returning_path_facts: Vec::new(),
        extraction_fail_closed_reason: None,
        panic_unreachability_obligations: 0,
        user_written_false_obligations: 0,
        proved_dead_edges: Default::default(),
        loop_fields: super::super::super::parsing::LoopFields {
            invariants: vec![invariant_call.clone()],
            per_loop_invariants: vec![(10, 20, vec![invariant_call.clone()])],
            per_loop_variants: vec![(10, 20, vec![invariant_call.clone()])],
            all_loop_spans: vec![],
            variants: vec![invariant_call.clone()],
            loop_analysis: None,
            loop_obligation_groups: vec![super::super::super::parsing::LoopObligationGroup {
                loop_index: Some(0),
                condition_unstated: None,
                pre_loop_stored_names: Default::default(),
                unstated_entry_values: Default::default(),
                injected_fail_closed: false,
                assumptions: Vec::new(),
                obligations: vec![invariant_call.clone()],
                condition: Some(invariant_call.clone()),
            }],
        },
        mut_borrow: super::super::super::parsing::MutBorrowFields {
            mut_borrow_body: Some(MutBorrowBody {
                final_values,
                indexed_writes: vec![IndexedWrite {
                    param_name: "x".to_string(),
                    index: invariant_call.clone(),
                    value: invariant_call.clone(),
                }],
                resolve_results: None,
                finality: std::collections::HashMap::new(),
                borrow_id_origins: std::collections::HashMap::new(),
                delayed_writeback_assumptions: vec![],
                mutation_continued_params: std::collections::HashSet::new(),
                nested_slot_resolutions: vec![],
                nested_transfer_params: std::collections::HashSet::new(),
                lent_path_resolutions: vec![],
            }),
            mut_ref_param_names: std::collections::HashSet::new(),
            state_params: std::collections::HashSet::new(),
            projected_final_pins: Vec::new(),
            stale_call_final_params: std::collections::HashSet::new(),
        },
        reborrow_prophecy: None,
    };

    let mut param_methods = HashMap::new();
    param_methods.insert("x".to_string(), "__trust_wp_invariant_Foo".to_string());

    rewrite_parsed_contract_type_invariant_methods(&mut parsed, &param_methods, None);

    assert_eq!(
        parsed.requires,
        vec![expected.clone()],
        "requires should be rewritten"
    );
    assert_eq!(
        parsed.ensures,
        vec![expected.clone()],
        "ensures should be rewritten"
    );
    assert_eq!(
        parsed.loop_fields.per_loop_invariants,
        vec![(10, 20, vec![expected.clone()])],
        "per_loop_invariants should be rewritten"
    );
    assert_eq!(
        parsed.loop_fields.invariants,
        vec![expected.clone()],
        "invariants should be rewritten"
    );
    assert_eq!(
        parsed.loop_fields.variants,
        vec![expected.clone()],
        "variants should be rewritten"
    );
    assert_eq!(
        parsed.loop_fields.per_loop_variants,
        vec![(10, 20, vec![expected.clone()])],
        "per_loop_variants should be rewritten"
    );
    assert_eq!(
        parsed.result_expr,
        Some(expected.clone()),
        "result_expr should be rewritten"
    );
    assert_eq!(
        parsed
            .result_expr_spanned
            .as_ref()
            .map(|spanned| spanned.expr.clone()),
        Some(expected.clone()),
        "result_expr_spanned.expr should stay in sync with result_expr"
    );
    assert_eq!(
        parsed.call_assumptions,
        vec![expected.clone()],
        "call_assumptions should be rewritten"
    );
    assert_eq!(
        parsed.call_obligations,
        vec![expected.clone()],
        "call_obligations should be rewritten"
    );
    assert_eq!(
        parsed.loop_fields.loop_obligation_groups.len(),
        1,
        "expected one loop obligation group"
    );
    let loop_group = &parsed.loop_fields.loop_obligation_groups[0];
    assert_eq!(
        loop_group.obligations,
        vec![expected.clone()],
        "loop_obligation_groups[*].obligations should be rewritten"
    );
    assert_eq!(
        loop_group.condition,
        Some(expected.clone()),
        "loop_obligation_groups[*].condition should be rewritten"
    );
    assert_eq!(
        parsed
            .mut_borrow
            .mut_borrow_body
            .as_ref()
            .unwrap()
            .final_values
            .get("x")
            .unwrap(),
        &expected,
        "mut_borrow_body.final_values should be rewritten"
    );
    let indexed_write = &parsed
        .mut_borrow
        .mut_borrow_body
        .as_ref()
        .unwrap()
        .indexed_writes[0];
    assert_eq!(
        indexed_write.index, expected,
        "mut_borrow_body.indexed_writes[*].index should be rewritten"
    );
    assert_eq!(
        indexed_write.value, expected,
        "mut_borrow_body.indexed_writes[*].value should be rewritten"
    );
}

#[test]
fn rewrite_contract_covers_all_parsed_contract_expr_fields_for_structural_inv() {
    use crate::mir_analysis::{IndexedWrite, MutBorrowBody, SpannedBodyExpr};

    let invariant_call = PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };

    let expected = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(trust_wp_core::formula::Pattern::Binding(
                        "$inv_some_field0".to_string(),
                    ))),
                },
                body: PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("$inv_some_field0".to_string(), None)),
                    method: "__trust_wp_invariant_NonZero".to_string(),
                    args: vec![],
                },
            },
            trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: PureExpr::Bool(true),
            },
        ],
    };

    let final_values = HashMap::from([("x".to_string(), invariant_call.clone())]);

    let mut parsed = super::super::super::parsing::ParsedContract {
        requires: vec![invariant_call.clone()],
        ensures: vec![invariant_call.clone()],
        result_expr: Some(invariant_call.clone()),
        result_expr_spanned: Some(SpannedBodyExpr::unspanned(invariant_call.clone())),
        arg_names: vec![],
        call_assumptions: vec![invariant_call.clone()],
        pre_loop_call_assumptions: vec![invariant_call.clone()],
        call_obligations: vec![invariant_call.clone()],
        pre_loop_call_obligations: vec![invariant_call.clone()],
        post_loop_call_obligations: vec![invariant_call.clone()],
        returning_path_facts: Vec::new(),
        extraction_fail_closed_reason: None,
        panic_unreachability_obligations: 0,
        user_written_false_obligations: 0,
        proved_dead_edges: Default::default(),
        loop_fields: super::super::super::parsing::LoopFields {
            invariants: vec![invariant_call.clone()],
            per_loop_invariants: vec![(10, 20, vec![invariant_call.clone()])],
            per_loop_variants: vec![(10, 20, vec![invariant_call.clone()])],
            all_loop_spans: vec![],
            variants: vec![invariant_call.clone()],
            loop_analysis: None,
            loop_obligation_groups: vec![super::super::super::parsing::LoopObligationGroup {
                loop_index: Some(0),
                condition_unstated: None,
                pre_loop_stored_names: Default::default(),
                unstated_entry_values: Default::default(),
                injected_fail_closed: false,
                assumptions: Vec::new(),
                obligations: vec![invariant_call.clone()],
                condition: Some(invariant_call.clone()),
            }],
        },
        mut_borrow: super::super::super::parsing::MutBorrowFields {
            mut_borrow_body: Some(MutBorrowBody {
                final_values,
                indexed_writes: vec![IndexedWrite {
                    param_name: "x".to_string(),
                    index: invariant_call.clone(),
                    value: invariant_call.clone(),
                }],
                resolve_results: None,
                finality: std::collections::HashMap::new(),
                borrow_id_origins: std::collections::HashMap::new(),
                delayed_writeback_assumptions: vec![],
                mutation_continued_params: std::collections::HashSet::new(),
                nested_slot_resolutions: vec![],
                nested_transfer_params: std::collections::HashSet::new(),
                lent_path_resolutions: vec![],
            }),
            mut_ref_param_names: std::collections::HashSet::new(),
            state_params: std::collections::HashSet::new(),
            projected_final_pins: Vec::new(),
            stale_call_final_params: std::collections::HashSet::new(),
        },
        reborrow_prophecy: None,
    };

    let param_structural_exprs = HashMap::from([("x".to_string(), expected.clone())]);

    rewrite_parsed_contract_type_invariant_methods_with_structural(
        &mut parsed,
        &HashMap::new(),
        None,
        &param_structural_exprs,
        None,
    );

    assert_eq!(
        parsed.requires,
        vec![expected.clone()],
        "requires should use the structural rewrite"
    );
    assert_eq!(
        parsed.loop_fields.per_loop_invariants,
        vec![(10, 20, vec![expected.clone()])],
        "per_loop_invariants should use the structural rewrite"
    );
    assert_eq!(
        parsed.result_expr,
        Some(expected.clone()),
        "result_expr should use the structural rewrite"
    );
    assert_eq!(
        parsed
            .result_expr_spanned
            .as_ref()
            .map(|spanned| spanned.expr.clone()),
        Some(expected.clone()),
        "result_expr_spanned.expr should stay in sync with result_expr"
    );
    assert_eq!(
        parsed.call_obligations,
        vec![expected.clone()],
        "call_obligations should use the structural rewrite"
    );
    assert_eq!(
        parsed
            .mut_borrow
            .mut_borrow_body
            .as_ref()
            .unwrap()
            .final_values
            .get("x"),
        Some(&expected),
        "mut_borrow_body.final_values should use the structural rewrite"
    );
    assert_eq!(
        parsed
            .mut_borrow
            .mut_borrow_body
            .as_ref()
            .unwrap()
            .indexed_writes[0]
            .value,
        expected,
        "mut_borrow_body.indexed_writes[*].value should use the structural rewrite"
    );
}

#[test]
fn build_type_invariant_method_map_maps_direct_invariant_param() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn direct(x: Sum10) {
let _ = x;
}
"#;

    let map = collect_param_method_map(source, "direct", &["x"]);
    let method = map
        .get("x")
        .expect("direct Sum10 parameter should map to an invariant method");
    assert!(
        method.contains("Sum10"),
        "expected method to reference Sum10, got {method}"
    );
}

#[test]
fn build_type_invariant_method_map_skips_transitive_wrapper_param() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

#[allow(dead_code)]
pub struct Wrapper<T>(T);

pub fn wrapped(x: Wrapper<Sum10>) {
let _ = x;
}
"#;

    let map = collect_param_method_map(source, "wrapped", &["x"]);
    assert!(
        !map.contains_key("x"),
        "wrapper parameter should not get an auto-generated invariant method"
    );
}
