// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for sort hint collection composition via `collect_all_sort_hints`.
//!
//! Tests the canonical hint collection patterns that drive the sort hint pipeline.
//! Key findings documented by these tests:
//! - Seq-only methods (`push_back`, `concat`) register the `_view` derived name, not the bare name
//! - Bool fn names use SMT-prefixed names (`logic_<name>`), not bare names
//! - And/Or logical context classifies vars as Bool via `collect_names_as_bool`
//! - Eq/Gt operands are NOT classified as Bool (they are comparison, not logical)

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr, UnOp};

use crate::{
    encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator},
    tests::helpers::{
        deref, exists_with_sort, forall_with_sort, int, method_call, not, var, var_with_sort, view,
    },
};

fn hints_for(expr: &PureExpr) -> SortHintAccumulator {
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(expr, &mut acc);
    acc
}

fn hints_for_exprs(exprs: &[PureExpr]) -> SortHintAccumulator {
    let mut acc = SortHintAccumulator::new();
    for expr in exprs {
        collect_all_sort_hints(expr, &mut acc);
    }
    acc
}

// ── Bool var detection ─────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn not_classifies_var_as_bool() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(var("x")));
    let acc = hints_for(&expr);
    assert!(
        acc.bool_vars.contains("x"),
        "Not(Var) → Bool; got {:?}",
        acc.bool_vars
    );
}

#[test]
#[timeout(5000)]
fn and_classifies_both_operands_as_bool() {
    let expr = PureExpr::BinOp(Arc::new(var("a")), BinOp::And, Arc::new(var("b")));
    let acc = hints_for(&expr);
    assert!(acc.bool_vars.contains("a"));
    assert!(acc.bool_vars.contains("b"));
}

#[test]
#[timeout(5000)]
fn or_classifies_both_operands_as_bool() {
    let expr = PureExpr::BinOp(Arc::new(var("p")), BinOp::Or, Arc::new(var("q")));
    let acc = hints_for(&expr);
    assert!(acc.bool_vars.contains("p"));
    assert!(acc.bool_vars.contains("q"));
}

#[test]
#[timeout(5000)]
fn implies_classifies_both_operands_as_bool() {
    let expr = PureExpr::BinOp(Arc::new(var("h")), BinOp::Implies, Arc::new(var("c")));
    let acc = hints_for(&expr);
    assert!(acc.bool_vars.contains("h"));
    assert!(acc.bool_vars.contains("c"));
}

#[test]
#[timeout(5000)]
fn eq_does_not_classify_operands_as_bool() {
    let expr = PureExpr::BinOp(Arc::new(var("x")), BinOp::Eq, Arc::new(int(0)));
    let acc = hints_for(&expr);
    assert!(
        !acc.bool_vars.contains("x"),
        "Eq operands should NOT be Bool-classified"
    );
}

#[test]
#[timeout(5000)]
fn gt_does_not_classify_operands_as_bool() {
    let expr = PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0)));
    let acc = hints_for(&expr);
    assert!(!acc.bool_vars.contains("x"));
}

// ── Bool fn detection ──────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn logic_fn_in_not_context_uses_smt_prefixed_name() {
    // Logic fn names are stored with SMT prefix: "logic_<name>"
    let expr = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::LogicFnCall {
            name: "is_valid".to_string(),
            args: vec![var("x")],
        }),
    );
    let acc = hints_for(&expr);
    assert!(
        acc.bool_fns.contains("logic_is__valid"),
        "LogicFnCall in Not context → Bool fn with SMT name; got {:?}",
        acc.bool_fns
    );
}

// ── Seq detection via methods ──────────────────────────────────────

#[test]
#[timeout(5000)]
fn push_back_registers_view_derived_name() {
    // push_back is a seq-only method; the receiver's _view name gets added to seqs
    let expr = method_call(var("s"), "push_back", vec![int(1)]);
    let acc = hints_for(&expr);
    assert!(
        acc.seqs.contains("s_view"),
        "push_back registers receiver_view name; seqs={:?}",
        acc.seqs
    );
}

#[test]
#[timeout(5000)]
fn concat_registers_view_derived_name() {
    let expr = method_call(var("s"), "concat", vec![var("t")]);
    let acc = hints_for(&expr);
    assert!(
        acc.seqs.contains("s_view"),
        "concat registers receiver_view name; seqs={:?}",
        acc.seqs
    );
}

#[test]
#[timeout(5000)]
fn subsequence_registers_view_derived_name() {
    let expr = method_call(var("s"), "subsequence", vec![int(0), int(3)]);
    let acc = hints_for(&expr);
    assert!(
        acc.seqs.contains("s_view"),
        "subsequence registers receiver_view; seqs={:?}",
        acc.seqs
    );
}

// ── FMap detection via methods ─────────────────────────────────────

#[test]
#[timeout(5000)]
fn lookup_method_classifies_receiver_as_fmap() {
    let expr = method_call(var("m"), "lookup", vec![var("k")]);
    let acc = hints_for(&expr);
    assert!(
        acc.fmaps.contains("m"),
        "lookup → FMap; fmaps={:?}",
        acc.fmaps
    );
}

#[test]
#[timeout(5000)]
fn merge_method_classifies_receiver_as_fmap() {
    let expr = method_call(var("m"), "merge", vec![var("other")]);
    let acc = hints_for(&expr);
    assert!(
        acc.fmaps.contains("m"),
        "merge → FMap; fmaps={:?}",
        acc.fmaps
    );
}

// ── Ambiguous methods ──────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn len_on_bare_var_is_ambiguous_or_classified() {
    let expr = method_call(var("v"), "len", vec![]);
    let acc = hints_for(&expr);
    let classified =
        acc.seqs.contains("v") || acc.fmaps.contains("v") || acc.ambiguous_seqs.contains("v");
    assert!(
        classified,
        "len on bare Var should be classified or ambiguous; seqs={:?}, fmaps={:?}, ambiguous={:?}",
        acc.seqs, acc.fmaps, acc.ambiguous_seqs
    );
}

#[test]
#[timeout(5000)]
fn get_on_bare_var_is_ambiguous_or_classified() {
    let expr = method_call(var("c"), "get", vec![int(0)]);
    let acc = hints_for(&expr);
    let classified =
        acc.seqs.contains("c") || acc.fmaps.contains("c") || acc.ambiguous_seqs.contains("c");
    assert!(
        classified,
        "get on bare Var should be classified or ambiguous; seqs={:?}, fmaps={:?}, ambiguous={:?}",
        acc.seqs, acc.fmaps, acc.ambiguous_seqs
    );
}

// ── Edge cases ─────────────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn literal_produces_no_hints() {
    let acc = hints_for(&int(42));
    assert!(acc.seqs.is_empty());
    assert!(acc.fmaps.is_empty());
    assert!(acc.bool_vars.is_empty());
    assert!(acc.bool_fns.is_empty());
    assert!(acc.mappings.is_empty());
}

#[test]
#[timeout(5000)]
fn bool_literal_produces_no_hints() {
    let acc = hints_for(&PureExpr::Bool(true));
    assert!(
        acc.bool_vars.is_empty(),
        "Bool literal should not produce var hints"
    );
}

#[test]
#[timeout(5000)]
fn multiple_exprs_accumulate_from_methods() {
    let exprs = [
        PureExpr::UnOp(UnOp::Not, Arc::new(var("flag"))),
        method_call(var("map"), "lookup", vec![var("k")]),
    ];
    let acc = hints_for_exprs(&exprs);
    assert!(acc.bool_vars.contains("flag"), "Bool from Not");
    assert!(acc.fmaps.contains("map"), "FMap from lookup");
}

#[test]
#[timeout(5000)]
fn nested_bool_in_and_expr() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(var("valid")))),
        BinOp::And,
        Arc::new(var("ready")),
    );
    let acc = hints_for(&expr);
    assert!(acc.bool_vars.contains("valid"), "nested Not var");
    assert!(acc.bool_vars.contains("ready"), "And operand");
}

#[test]
#[timeout(5000)]
fn not_on_method_call_records_receiver_qualified_bool_key() {
    let expr = not(method_call(var("cell"), "index_logic", vec![var("k")]));
    let acc = hints_for(&expr);
    assert!(
        acc.bool_fns.contains("cell.index_logic"),
        "Bool method hints on bare receivers should be receiver-qualified; bool_fns={:?}",
        acc.bool_fns
    );
}

#[test]
#[timeout(5000)]
fn wrapped_receiver_method_call_keeps_base_receiver_in_bool_key() {
    let expr = not(method_call(
        view(deref(var("cell"))),
        "index_logic",
        vec![var("k")],
    ));
    let acc = hints_for(&expr);
    assert!(
        acc.bool_fns.contains("cell.index_logic"),
        "View/Deref wrappers should peel back to the base receiver name; bool_fns={:?}",
        acc.bool_fns
    );
}

#[test]
#[timeout(5000)]
fn forall_bool_var_sort_registers_bool_hint() {
    let expr = forall_with_sort("flag", ExprSort::Bool, var("flag"));
    let acc = hints_for(&expr);
    assert!(
        acc.bool_vars.contains("flag"),
        "forall<bool> should record the bound var as Bool; bool_vars={:?}",
        acc.bool_vars
    );
}

#[test]
#[timeout(5000)]
fn exists_fmap_var_sort_registers_fmap_hint() {
    let expr = exists_with_sort("m", ExprSort::FMap, var("m"));
    let acc = hints_for(&expr);
    assert!(
        acc.fmaps.contains("m"),
        "exists<FMap> should record the bound var as FMap; fmaps={:?}",
        acc.fmaps
    );
}

#[test]
#[timeout(5000)]
fn mapping_view_annotation_registers_mapping_hint() {
    let expr = view(var_with_sort(
        "map",
        ExprSort::Datatype(intern_sort_name("Mapping")),
    ));
    let acc = hints_for(&expr);
    assert!(
        acc.mappings.contains("map_view"),
        "view(mapping) should register the derived mapping name; mappings={:?}",
        acc.mappings
    );
}
