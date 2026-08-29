// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// collect_seq_view_names tests
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_len() {
    // v@.len() should register "v_view" as Seq
    let expr = method_call(view(var("v")), "len", vec![]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "v@ used as .len() receiver should be Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_index() {
    // v@.index(0) should register "v_view" as Seq
    let expr = method_call(view(var("v")), "index", vec![int(0)]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "v@.index() should register v_view as Seq, got: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_index_logic() {
    // v@.index_logic(i) should register "v_view" as Seq
    let expr = method_call(view(var("v")), "index_logic", vec![var("i")]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "v@.index_logic() should register v_view as Seq, got: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_push_back() {
    // v@.push_back(x) should register "v_view" as Seq
    let expr = method_call(view(var("v")), "push_back", vec![var("x")]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "v@.push_back() should register v_view as Seq, got: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_ext_eq_views() {
    // v@.ext_eq(w@) should register both views as Seq (#962)
    let expr = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "v@.ext_eq(w@) should register v_view, got: {names:?}"
    );
    assert!(
        names.contains("w_view"),
        "v@.ext_eq(w@) should register w_view, got: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_ext_eq_bare_vars_ignored() {
    // x.ext_eq(y) should remain untyped during pre-scan (non-Seq fallback path)
    let expr = method_call(var("x"), "ext_eq", vec![var("y")]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.is_empty(),
        "bare var ext_eq should not register any Seq names, got: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_method_call_ext_eq_nested_view_arg() {
    // v@.ext_eq(if c then w@ else z@) should mark all views as Seq.
    let nested = ite(var("c"), view(var("w")), view(var("z")));
    let expr = method_call(view(var("v")), "ext_eq", vec![nested]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "nested ext_eq should register v_view, got: {names:?}"
    );
    assert!(
        names.contains("w_view"),
        "nested ext_eq should register w_view, got: {names:?}"
    );
    assert!(
        names.contains("z_view"),
        "nested ext_eq should register z_view, got: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_non_seq_method_ignored() {
    // v@.contains(x) should NOT register "v_view" (not a Seq method)
    let expr = method_call(view(var("v")), "contains", vec![var("x")]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.is_empty(),
        "Non-Seq method should not register view as Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_len_on_bare_var_ignored() {
    // fmap.len() should NOT register "fmap_view" as Seq (#756)
    let expr = method_call(var("fmap"), "len", vec![]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.is_empty(),
        "bare var receiver on ambiguous len() should not be pre-tagged Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_index_on_bare_var_ignored() {
    // fmap.index(k) should NOT register "fmap_view" as Seq (#756)
    let expr = method_call(var("fmap"), "index", vec![int(0)]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.is_empty(),
        "bare var receiver on ambiguous index() should not be pre-tagged Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_get_on_bare_var_ignored() {
    // mapping.get(k) should NOT register "mapping_view" as Seq (#756)
    let expr = method_call(var("mapping"), "get", vec![int(0)]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.is_empty(),
        "bare var receiver on ambiguous get() should not be pre-tagged Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_equality_propagation() {
    // v@ == push_back(w@, x) => v@ should be Seq
    let push = method_call(view(var("w")), "push_back", vec![var("x")]);
    let expr = eq(view(var("v")), push);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "View in equality with Seq-producing expr should be Seq"
    );
    assert!(names.contains("w_view"), "push_back receiver should be Seq");
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_old() {
    // old(v@).len() should register "old_v_view" as Seq
    let expr = method_call(old(view(var("v"))), "len", vec![]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("old_v_view"),
        "old(v@) used as .len() receiver should register old_v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_ite() {
    // if c then v@.len() else w@.len()
    let t = method_call(view(var("v")), "len", vec![]);
    let e = method_call(view(var("w")), "len", vec![]);
    let expr = ite(var("c"), t, e);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(names.contains("v_view"));
    assert!(names.contains("w_view"));
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_forall() {
    // forall i. v@.index(i) > 0
    let body = gt(method_call(view(var("v")), "index", vec![var("i")]), int(0));
    let expr = forall("i", body);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method inside forall should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_exists() {
    // exists i. v@.index(i) == 42
    let body = eq(
        method_call(view(var("v")), "index", vec![var("i")]),
        int(42),
    );
    let expr = exists("i", body);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method inside exists should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_logic_fn_call() {
    // my_fn(v@.len())
    let len_call = method_call(view(var("v")), "len", vec![]);
    let expr = logic_fn_call("my_fn", vec![len_call]);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method in logic fn arg should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_let() {
    // let x = v@.len() in x > 0
    let len_call = method_call(view(var("v")), "len", vec![]);
    let expr = let_bind("x", len_call, gt(var("x"), int(0)));
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method in Let value should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_let_body() {
    // let x = 0 in v@.len()
    let len_call = method_call(view(var("v")), "len", vec![]);
    let expr = let_bind("x", int(0), len_call);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method in Let body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_leaf_exprs_empty() {
    // Leaf expressions (Var, Int, Bool) produce no Seq names
    for expr in [var("x"), int(42), bool_expr(true)] {
        let mut names = HashSet::new();
        collect_seq_view_names(&expr, &mut names);
        assert!(names.is_empty(), "Leaf expr should produce no Seq names");
    }
}

// =============================================================================
