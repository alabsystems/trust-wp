// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, PureExpr,
};

use super::{
    build_positional_param_renaming, build_trait_spec_table, conjoin_exprs,
    extraction::{
        effective_user_specs_for_extraction, ensures_uses_reserved_result_name,
        format_context_extraction_warning,
    },
    parse_and_extract_contract, parse_contract_clauses, ExtractionContext,
};
use crate::{
    callbacks::{
        copy_mir_bodies,
        discovery::{find_contract_functions, find_trait_contracts},
        thread_locals::clear_caches,
    },
    contracts::FunctionContract,
    mir_analysis::{
        diagnostics::{ExtractionDiagKind, ExtractionDiagnostics},
        resolver::ReborrowWriteback,
    },
};

static PARSING_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

#[test]
fn conjoin_exprs_empty_returns_true() {
    let result = conjoin_exprs(&[]);
    assert_eq!(result, PureExpr::Bool(true));
}

#[test]
fn conjoin_exprs_single_returns_unchanged() {
    let exprs = vec![PureExpr::Var("x".to_string(), None)];
    let result = conjoin_exprs(&exprs);
    assert_eq!(result, PureExpr::Var("x".to_string(), None));
}

#[test]
fn conjoin_exprs_two_creates_and() {
    let exprs = vec![
        PureExpr::Var("a".to_string(), None),
        PureExpr::Var("b".to_string(), None),
    ];
    let result = conjoin_exprs(&exprs);
    match result {
        PureExpr::BinOp(left, BinOp::And, right) => {
            assert_eq!(*left, PureExpr::Var("a".to_string(), None));
            assert_eq!(*right, PureExpr::Var("b".to_string(), None));
        }
        other => panic!("expected BinOp(And), got {other:?}"),
    }
}

#[test]
fn conjoin_exprs_three_left_associates() {
    let exprs = vec![
        PureExpr::Bool(true),
        PureExpr::Bool(false),
        PureExpr::Var("c".to_string(), None),
    ];
    let result = conjoin_exprs(&exprs);
    // Should be ((true && false) && c)
    match &result {
        PureExpr::BinOp(left_tree, BinOp::And, right) => {
            assert_eq!(right.as_ref(), &PureExpr::Var("c".to_string(), None));
            match left_tree.as_ref() {
                PureExpr::BinOp(l, BinOp::And, r) => {
                    assert_eq!(l.as_ref(), &PureExpr::Bool(true));
                    assert_eq!(r.as_ref(), &PureExpr::Bool(false));
                }
                other => panic!("expected inner BinOp(And), got {other:?}"),
            }
        }
        other => panic!("expected BinOp(And), got {other:?}"),
    }
}

#[test]
fn parse_contract_clauses_valid_expressions() {
    let clauses = vec!["x > 0".to_string(), "y < 10".to_string()];
    let result = parse_contract_clauses(&clauses, "requires", "test_fn");
    assert!(
        result.is_ok(),
        "valid clauses should parse: {:?}",
        result.err()
    );
    let exprs = result.unwrap();
    assert_eq!(exprs.len(), 2, "should have 2 parsed expressions");
}

#[test]
fn parse_contract_clauses_empty_returns_empty() {
    let clauses: Vec<String> = vec![];
    let result = parse_contract_clauses(&clauses, "requires", "test_fn");
    let exprs = result.expect("empty clause list should parse successfully");
    assert!(
        exprs.is_empty(),
        "empty clause list should produce empty output"
    );
}

#[test]
fn parse_contract_clauses_invalid_reports_context() {
    let clauses = vec!["!!!invalid!!!".to_string()];
    let result = parse_contract_clauses(&clauses, "ensures", "my_function");
    assert!(result.is_err(), "invalid clause should fail to parse");
    let err = result.unwrap_err();
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("ensures"),
        "error should mention clause kind: {err_msg}"
    );
    assert!(
        err_msg.contains("my_function"),
        "error should mention context: {err_msg}"
    );
}

fn names(list: &[&str]) -> Vec<String> {
    list.iter().map(|name| (*name).to_string()).collect()
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

#[test]
fn positional_renaming_renames_both_sides_to_the_same_names() {
    let renaming = build_positional_param_renaming(&names(&["x", "y"]), &names(&["a", "b"]))
        .expect("injective");
    assert_eq!(renaming.names, names(&["__trust_wp_p0", "__trust_wp_p1"]));
    assert_eq!(renaming.trait_subs.get("x"), Some(&var("__trust_wp_p0")));
    assert_eq!(renaming.trait_subs.get("y"), Some(&var("__trust_wp_p1")));
    assert_eq!(renaming.impl_subs.get("a"), Some(&var("__trust_wp_p0")));
    assert_eq!(renaming.impl_subs.get("b"), Some(&var("__trust_wp_p1")));
}

#[test]
fn positional_renaming_keeps_a_self_receiver() {
    let renaming = build_positional_param_renaming(&names(&["self", "x"]), &names(&["self", "y"]))
        .expect("injective");
    assert_eq!(renaming.names, names(&["self", "__trust_wp_p1"]));
    assert!(!renaming.trait_subs.contains_key("self"));
    assert!(!renaming.impl_subs.contains_key("self"));
}

/// Review F1: a trait `_` parameter at position 0 named `arg0` next to a real
/// parameter `arg0` gave two impl parameters the same trait name.
#[test]
fn positional_renaming_refuses_duplicate_names_on_either_side() {
    for (trait_names, impl_names) in [
        (names(&["arg0", "arg0"]), names(&["x", "y"])),
        (names(&["x", "y"]), names(&["arg1", "arg1"])),
    ] {
        assert!(
            build_positional_param_renaming(&trait_names, &impl_names).is_err(),
            "{trait_names:?} / {impl_names:?}"
        );
    }
}

/// Review F1: a swap that the old impl-onto-trait renaming merged.
#[test]
fn positional_renaming_is_injective_under_swaps() {
    let renaming = build_positional_param_renaming(&names(&["x", "y"]), &names(&["y", "x"]))
        .expect("injective");
    assert_eq!(renaming.trait_subs.get("x"), Some(&var("__trust_wp_p0")));
    assert_eq!(renaming.impl_subs.get("y"), Some(&var("__trust_wp_p0")));
    assert_eq!(renaming.impl_subs.get("x"), Some(&var("__trust_wp_p1")));
}

/// Review F2: `result` as a parameter name is refused on both sides.
#[test]
fn positional_renaming_refuses_result_and_reserved_names() {
    for (trait_names, impl_names) in [
        (names(&["result"]), names(&["x"])),
        (names(&["x"]), names(&["result"])),
        (names(&["__trust_wp_p1", "y"]), names(&["a", "b"])),
    ] {
        assert!(
            build_positional_param_renaming(&trait_names, &impl_names).is_err(),
            "{trait_names:?} / {impl_names:?}"
        );
    }
}

#[test]
fn positional_renaming_refuses_arity_mismatch() {
    assert!(build_positional_param_renaming(&names(&["x"]), &names(&["a", "b"])).is_err());
}

mod assoc_const_contracts;
mod bodyless_trait_and_two_phase;
mod closure_capture_result_exprs;
mod recursive_self_spec;
mod reserved_result_name;

fn install_mir_borrowck_cache(config: &mut Config) {
    config.override_queries = Some(|_sess, providers| {
        crate::callbacks::spec_typecheck::install_spec_tc_mir_built_erasure(providers);
        providers.queries.mir_borrowck = |tcx, local_id| {
            if tcx.hir_node_by_def_id(local_id).body_id().is_none() {
                let guar = tcx.dcx().span_delayed_bug(
                    tcx.def_span(local_id),
                    "mir_borrowck called for item without HIR body",
                );
                return Err(guar);
            }
            copy_mir_bodies(tcx, local_id);
            (rustc_interface::DEFAULT_QUERY_PROVIDERS
                .queries
                .mir_borrowck)(tcx, local_id)
        };
    });
}
