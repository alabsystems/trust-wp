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
    simplify_newtype_field_access_expr, FieldOrderTables,
};
use crate::callbacks::struct_field_map::{CtorCandidates, CtorFieldOrder, DeclaredFields};

/// The empty constructor table, for the tests that exercise the flat
/// name->index map on its own.
fn empty_ctors() -> &'static CtorFieldOrder {
    static EMPTY: std::sync::OnceLock<CtorFieldOrder> = std::sync::OnceLock::new();
    EMPTY.get_or_init(CtorFieldOrder::default)
}

/// Tables that carry only the flat field map (no constructor declarations).
fn flat_tables(flat: &HashMap<String, usize>) -> FieldOrderTables<'_> {
    FieldOrderTables::new(flat, empty_ctors())
}

/// Tables that also declare `type_name`'s fields in declaration order.
fn ctor_tables<'a>(
    flat: &'a HashMap<String, usize>,
    ctors: &'a CtorFieldOrder,
) -> FieldOrderTables<'a> {
    FieldOrderTables::new(flat, ctors)
}

/// A one-constructor declaration table.
fn ctors_for(type_name: &str, fields: &[&str]) -> CtorFieldOrder {
    ctors_with_candidates(type_name, &[fields])
}

/// A declaration table where several constructors answer to `type_name`.
///
/// Built through `CtorCandidates::record_declared`, the same entry point the
/// driver uses for a constructor that merely answers to a spelling, so the cap
/// behaves in the test exactly as it does in production.
fn ctors_with_candidates(type_name: &str, candidates: &[&[&str]]) -> CtorFieldOrder {
    let mut map = CtorFieldOrder::new();
    let entry = map.entry(type_name.to_string()).or_default();
    for fields in candidates {
        CtorCandidates::record_declared(entry, DeclaredFields::from_names_for_test(fields));
    }
    map
}

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

mod placement_kernel;

mod annotate_var_sorts;
mod final_guard_regressions;
mod var_sort_preservation;

mod erase_box_deref;
mod receiver_root_var_name;
