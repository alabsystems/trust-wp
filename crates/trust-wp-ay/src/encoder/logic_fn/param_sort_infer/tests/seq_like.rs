// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::*;

// ── infer_seq_like_params tests ──────────────────────────────────

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_len_method_on_param() {
    let logic_fn = simple_logic_fn("my_len", vec!["s"], method_call(var("s"), "len", vec![]));
    let result = infer_seq_like_params(&logic_fn);
    assert!(result.contains("s"), "s.len() should infer s as Seq-like");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_index_method_on_param() {
    let logic_fn = simple_logic_fn(
        "get_at",
        vec!["s", "i"],
        method_call(var("s"), "index", vec![var("i")]),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.index(i) should infer s as Seq-like"
    );
    assert!(!result.contains("i"), "i is not a Seq receiver");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_push_back_method() {
    let logic_fn = simple_logic_fn(
        "append",
        vec!["s", "v"],
        method_call(var("s"), "push_back", vec![var("v")]),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.push_back(v) should infer s as Seq-like"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_subsequence_method() {
    let logic_fn = simple_logic_fn(
        "slice",
        vec!["s"],
        method_call(var("s"), "subsequence", vec![int(0), int(5)]),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.subsequence(0,5) should infer s as Seq-like"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_non_seq_method_ignored() {
    let logic_fn = simple_logic_fn("custom", vec!["s"], method_call(var("s"), "foo", vec![]));
    let result = infer_seq_like_params(&logic_fn);
    assert!(result.is_empty(), "s.foo() should not infer Seq");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_non_param_receiver_ignored() {
    let logic_fn = simple_logic_fn(
        "non_param",
        vec!["x"],
        method_call(var("local_var"), "len", vec![]),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.is_empty(),
        "non-param receiver should not be inferred"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_requires() {
    let mut logic_fn = simple_logic_fn("req_fn", vec!["s"], int(0));
    logic_fn.requires_mut().push(PureExpr::BinOp(
        Arc::new(method_call(var("s"), "len", vec![])),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(int(0)),
    ));
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() in requires should infer s as Seq-like"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_ensures() {
    let mut logic_fn = simple_logic_fn("ens_fn", vec!["s", "v"], int(0));
    logic_fn
        .ensures_mut()
        .push(method_call(var("s"), "contains", vec![var("v")]));
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.contains(v) in ensures should infer s as Seq-like"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_nested_in_ite() {
    let logic_fn = simple_logic_fn(
        "nested",
        vec!["s"],
        PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(method_call(var("s"), "len", vec![])),
            Arc::new(int(0)),
        ),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() nested in Ite should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_all_seq_methods() {
    let methods = [
        "len",
        "index",
        "index_logic",
        "subsequence",
        "push_back",
        "set",
        "concat",
        "contains",
    ];
    for method in methods {
        let logic_fn = simple_logic_fn(
            &format!("test_{method}"),
            vec!["s"],
            method_call(var("s"), method, vec![]),
        );
        let result = infer_seq_like_params(&logic_fn);
        assert!(
            result.contains("s"),
            "s.{method}() should infer s as Seq-like"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_concat_arg_param() {
    let logic_fn = simple_logic_fn(
        "concat_params",
        vec!["ab", "bc"],
        method_call(var("ab"), "concat", vec![var("bc")]),
    );

    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("ab"),
        "concat receiver parameter should infer as Seq"
    );
    assert!(
        result.contains("bc"),
        "concat argument parameter should infer as Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_forall_body() {
    let logic_fn = simple_logic_fn(
        "all_positive",
        vec!["s"],
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(method_call(var("s"), "index", vec![var("i")])),
                trust_wp_core::formula::BinOp::Gt,
                Arc::new(int(0)),
            )),
            triggers: vec![],
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.index(i) inside forall body should infer s"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_match_arm() {
    let logic_fn = simple_logic_fn(
        "match_fn",
        vec!["s", "x"],
        match_expr(
            var("x"),
            vec![(
                ctor_pattern("Ctor", Some(Pattern::Binding("v".to_string()))),
                method_call(var("s"), "len", vec![]),
            )],
        ),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() inside match arm should infer s"
    );
}

// ── infer_seq_like_params nesting coverage ─────────────────────

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_old() {
    let logic_fn = simple_logic_fn(
        "old_len",
        vec!["s"],
        PureExpr::Old(Arc::new(method_call(var("s"), "len", vec![]))),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(result.contains("s"), "s.len() inside Old should be found");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_deref() {
    let logic_fn = simple_logic_fn(
        "deref_len",
        vec!["s"],
        PureExpr::Deref(Arc::new(method_call(var("s"), "len", vec![]))),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(result.contains("s"), "s.len() inside Deref should be found");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_final() {
    let logic_fn = simple_logic_fn(
        "final_len",
        vec!["s"],
        PureExpr::Final(Arc::new(method_call(var("s"), "len", vec![]))),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(result.contains("s"), "s.len() inside Final should be found");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_view() {
    let logic_fn = simple_logic_fn(
        "view_len",
        vec!["s"],
        PureExpr::View(Arc::new(method_call(var("s"), "len", vec![]))),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(result.contains("s"), "s.len() inside View should be found");
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_exists_body() {
    let logic_fn = simple_logic_fn(
        "any_positive",
        vec!["s"],
        PureExpr::Exists {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(method_call(var("s"), "index", vec![var("i")])),
            triggers: vec![],
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.index(i) inside Exists body should infer s"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_let_value() {
    use trust_wp_core::formula::PureExpr;

    let logic_fn = simple_logic_fn(
        "let_val",
        vec!["s"],
        PureExpr::Let {
            var: "n".to_string(),
            value: Arc::new(method_call(var("s"), "len", vec![])),
            body: Arc::new(var("n")),
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() inside Let value should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_let_body() {
    use trust_wp_core::formula::PureExpr;

    let logic_fn = simple_logic_fn(
        "let_body",
        vec!["s"],
        PureExpr::Let {
            var: "n".to_string(),
            value: Arc::new(int(0)),
            body: Arc::new(method_call(var("s"), "len", vec![])),
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() inside Let body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_let_assume() {
    let logic_fn = simple_logic_fn(
        "assume_len",
        vec!["s"],
        PureExpr::LetAssume {
            assumption: Arc::new(method_call(var("s"), "len", vec![])),
            body: Arc::new(int(0)),
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() inside LetAssume should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_let_obligation() {
    let logic_fn = simple_logic_fn(
        "obligation_len",
        vec!["s"],
        PureExpr::LetObligation {
            obligation: Arc::new(method_call(var("s"), "len", vec![])),
            body: Arc::new(int(0)),
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() inside LetObligation should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_in_closure_body() {
    let logic_fn = simple_logic_fn(
        "closure_len",
        vec!["s"],
        PureExpr::Closure {
            params: vec![("_x".to_string(), None)],
            body: Arc::new(method_call(var("s"), "len", vec![])),
        },
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.len() inside Closure body should be found"
    );
}

// ── FSet-only method exclusion tests (#2701) ─────────────────────

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_fset_peek_excludes_from_seq() {
    // A parameter that uses `peek` (FSet-only) and `contains` (shared)
    // should NOT be classified as Seq. This is the root cause of the
    // bug/vcgen.rs regression: set_max's `s` parameter was misclassified
    // as Seq because `s.contains(result)` appeared in ensures.
    let mut logic_fn = simple_logic_fn("set_fn", vec!["s"], method_call(var("s"), "peek", vec![]));
    logic_fn
        .ensures_mut()
        .push(method_call(var("s"), "contains", vec![var("result")]));
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        !result.contains("s"),
        "s.peek() (FSet-only) should exclude s from Seq inference \
         even when s.contains() (shared method) is present"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_fset_remove_excludes_from_seq() {
    let logic_fn = simple_logic_fn(
        "remove_fn",
        vec!["s"],
        method_call(var("s"), "remove", vec![var("x")]),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        !result.contains("s"),
        "s.remove(x) (FSet-only) should exclude s from Seq inference"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_fset_is_empty_excludes_from_seq() {
    let mut logic_fn = simple_logic_fn("empty_fn", vec!["s"], int(0));
    logic_fn.requires_mut().push(PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    ));
    // Even though the body uses len (shared method), the requires uses
    // is_empty (FSet-only), so s should not be Seq.
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        !result.contains("s"),
        "s.is_empty() (FSet-only) in requires should exclude s from Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_set_max_pattern() {
    // Exact pattern from bug/vcgen.rs set_max function.
    // Body uses: s.peek(), s.remove(x), s.is_empty()
    // Ensures: s.contains(result)
    // Requires: !s.is_empty()
    // All of peek, remove, is_empty are FSet-only => s should NOT be Seq.
    let body = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(method_call(var("s"), "peek", vec![])),
        body: Arc::new(PureExpr::Let {
            var: "s2".to_string(),
            value: Arc::new(method_call(var("s"), "remove", vec![var("x")])),
            body: Arc::new(PureExpr::Ite(
                Arc::new(method_call(var("s2"), "is_empty", vec![])),
                Arc::new(var("x")),
                Arc::new(var("x")),
            )),
        }),
    };
    let mut logic_fn = simple_logic_fn("set_max", vec!["s"], body);
    logic_fn.set_requires(vec![PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    )]);
    logic_fn.set_ensures(vec![method_call(var("s"), "contains", vec![var("result")])]);
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        !result.contains("s"),
        "set_max's `s` parameter uses FSet-only methods (peek, remove, is_empty) \
         and should not be classified as Seq despite s.contains() in ensures"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_pure_seq_still_inferred() {
    // A parameter that ONLY uses Seq methods (no FSet-only methods)
    // should still be classified as Seq.
    let logic_fn = simple_logic_fn(
        "seq_fn",
        vec!["s"],
        method_call(var("s"), "push_back", vec![int(42)]),
    );
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("s"),
        "s.push_back() (Seq-only) should still infer s as Seq-like"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_seq_like_params_mixed_seq_and_fset_different_params() {
    // Two params: one using Seq methods, one using FSet methods.
    // Each should be classified independently.
    let body = PureExpr::BinOp(
        Arc::new(method_call(var("seq_param"), "len", vec![])),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(method_call(var("fset_param"), "peek", vec![])),
    );
    let logic_fn = simple_logic_fn("mixed", vec!["seq_param", "fset_param"], body);
    let result = infer_seq_like_params(&logic_fn);
    assert!(
        result.contains("seq_param"),
        "seq_param with only len() should be Seq"
    );
    assert!(
        !result.contains("fset_param"),
        "fset_param with peek() should NOT be Seq"
    );
}
