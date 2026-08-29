// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::FuncDecl;
use ntest::timeout;

use super::*;

// ── collect_cross_fn_seq_params tests ────────────────────────────

fn make_func_decl(smt_name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    encoder.solver.declare_fun(smt_name, domain, range)
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_basic() {
    let mut declared_fns = HashMap::new();
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl = make_func_decl("logic_f", &[seq_sort], Sort::Int);
    declared_fns.insert("logic_f".to_string(), func_decl);

    let param_names: HashSet<&str> = ["s"].into_iter().collect();
    let mut out = HashSet::new();

    let expr = logic_fn_call("f", vec![var("s")]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(out.contains("s"), "s at Seq position should be inferred");
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_non_seq_domain_ignored() {
    let mut declared_fns = HashMap::new();
    let func_decl = make_func_decl("logic_f", &[Sort::Int], Sort::Int);
    declared_fns.insert("logic_f".to_string(), func_decl);

    let param_names: HashSet<&str> = ["s"].into_iter().collect();
    let mut out = HashSet::new();

    let expr = logic_fn_call("f", vec![var("s")]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(out.is_empty(), "Int-domain param should not infer Seq");
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_undeclared_fn_ignored() {
    let declared_fns = HashMap::new();
    let param_names: HashSet<&str> = ["s"].into_iter().collect();
    let mut out = HashSet::new();

    let expr = logic_fn_call("g", vec![var("s")]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.is_empty(),
        "undeclared function should not trigger inference"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_non_param_arg_ignored() {
    let mut declared_fns = HashMap::new();
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl = make_func_decl("logic_f", &[seq_sort], Sort::Int);
    declared_fns.insert("logic_f".to_string(), func_decl);

    let param_names: HashSet<&str> = ["x"].into_iter().collect();
    let mut out = HashSet::new();

    let expr = logic_fn_call("f", vec![var("local_var")]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(out.is_empty(), "non-param arg should not be inferred");
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_second_arg_seq() {
    let mut declared_fns = HashMap::new();
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl = make_func_decl("logic_f", &[Sort::Int, seq_sort], Sort::Int);
    declared_fns.insert("logic_f".to_string(), func_decl);

    let param_names: HashSet<&str> = ["x", "s"].into_iter().collect();
    let mut out = HashSet::new();

    let expr = logic_fn_call("f", vec![var("x"), var("s")]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.contains("s"),
        "second arg at Seq position should be inferred"
    );
    assert!(
        !out.contains("x"),
        "first arg at Int position should NOT be inferred"
    );
}

// ── collect_cross_fn_seq_params nesting coverage ────────────────

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_nested_call() {
    let mut declared_fns = HashMap::new();
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl_f = make_func_decl("logic_f", &[seq_sort], Sort::Int);
    let func_decl_g = make_func_decl("logic_g", &[Sort::Int], Sort::Int);
    declared_fns.insert("logic_f".to_string(), func_decl_f);
    declared_fns.insert("logic_g".to_string(), func_decl_g);

    let param_names: HashSet<&str> = ["s"].into_iter().collect();
    let mut out = HashSet::new();

    let expr = logic_fn_call("g", vec![logic_fn_call("f", vec![var("s")])]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.contains("s"),
        "s in nested f(s) should be found recursively"
    );
}

fn make_seq_env() -> (HashMap<String, FuncDecl>, HashSet<&'static str>) {
    let mut declared_fns = HashMap::new();
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl = make_func_decl("logic_f", &[seq_sort], Sort::Int);
    declared_fns.insert("logic_f".to_string(), func_decl);
    let param_names: HashSet<&str> = ["s"].into_iter().collect();
    (declared_fns, param_names)
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_ite() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(logic_fn_call("f", vec![var("s")])),
        Arc::new(int(0)),
    );
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.contains("s"),
        "f(s) inside Ite then-branch should infer s"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_method_call_receiver() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = method_call(logic_fn_call("f", vec![var("s")]), "unwrap", vec![]);
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.contains("s"),
        "f(s) inside method_call receiver should infer s"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_forall() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(logic_fn_call("f", vec![var("s")])),
        triggers: vec![],
    };
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(out.contains("s"), "f(s) inside Forall body should infer s");
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_forall_trigger() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![logic_fn_call("f", vec![var("s")])]],
    };
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.contains("s"),
        "f(s) inside Forall trigger should infer s"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_match_arm() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = match_expr(
        var("x"),
        vec![(
            Pattern::Binding("v".to_string()),
            logic_fn_call("f", vec![var("s")]),
        )],
    );
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(
        out.contains("s"),
        "f(s) inside Match arm body should infer s"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_let_value() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = PureExpr::Let {
        var: "n".to_string(),
        value: Arc::new(logic_fn_call("f", vec![var("s")])),
        body: Arc::new(var("n")),
    };
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(out.contains("s"), "f(s) inside Let value should infer s");
}

#[test]
#[timeout(30000)]
fn test_collect_cross_fn_seq_params_in_closure() {
    let (declared_fns, param_names) = make_seq_env();
    let mut out = HashSet::new();
    let expr = PureExpr::Closure {
        params: vec![("_".to_string(), None)],
        body: Arc::new(logic_fn_call("f", vec![var("s")])),
    };
    collect_cross_fn_seq_params(&expr, &param_names, &declared_fns, &mut out);
    assert!(out.contains("s"), "f(s) inside Closure body should infer s");
}
