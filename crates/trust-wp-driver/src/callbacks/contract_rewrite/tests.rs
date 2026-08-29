// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for contract rewriting — extracted from inline tests (#1669).

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    contract_parser::TURBOFISH_ARG_WRAPPER_NAME,
    formula::{intern_sort_name, BinOp, ExprSort, MatchArm, Pattern, PureExpr},
};

use super::{
    annotate_var_sorts, erase_box_deref_expr, is_newtype_param_expr,
    normalize_turbofish_logic_fn_expr, reorder_named_fields_to_positional,
    rewrite_logic_method_calls_expr, rewrite_named_field_access_expr, rewrite_named_struct_pattern,
    simplify_newtype_field_access_expr,
};

#[test]
fn rewrites_logic_method_call_to_logic_fn_call() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
        method: "sub_pre".to_string(),
        args: vec![PureExpr::Var("rhs".to_string(), None)],
    };

    let mut logic_method_names = HashSet::new();
    logic_method_names.insert("sub_pre".to_string());

    let rewritten = rewrite_logic_method_calls_expr(&expr, &logic_method_names);
    match rewritten {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "sub_pre");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], PureExpr::Var("self".to_string(), None));
            assert_eq!(args[1], PureExpr::Var("rhs".to_string(), None));
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

#[test]
fn does_not_rewrite_builtin_method_calls() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        method: "len".to_string(),
        args: vec![],
    };

    let mut logic_method_names = HashSet::new();
    logic_method_names.insert("len".to_string());

    let rewritten = rewrite_logic_method_calls_expr(&expr, &logic_method_names);
    match rewritten {
        PureExpr::MethodCall { method, .. } => {
            assert_eq!(method, "len");
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

mod tuple_get_simplification;

mod named_field_access_rewriting;

mod named_struct_constructor_reordering;

mod annotate_var_sorts;
mod final_guard_regressions;
mod var_sort_preservation;

mod erase_box_deref;
mod receiver_root_var_name;
