// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::expr_seq`] Seq-related expression analysis.
//!
//! Coverage gap: `expr_seq.rs` (208 LOC) has zero `#[cfg(test)]` blocks.
//! Two pub(crate) functions detect Seq patterns in PureExpr trees:
//! `expr_has_seq_index_on_final` and `expr_has_seq_method_needing_quantifiers`.
//! Existing tests (18 references) are performance/depth-guard proofs;
//! no direct correctness tests for the method-name matching or receiver patterns.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use crate::expr_seq::{expr_has_seq_index_on_final, expr_has_seq_method_needing_quantifiers};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

// --- expr_has_seq_index_on_final ---

#[test]
#[timeout(30000)]
fn index_on_final_direct_pattern() {
    // Final(View(x)).index_logic(i)
    let receiver = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(var("x")))));
    let expr = method_call(receiver, "index_logic", vec![var("i")]);
    assert!(expr_has_seq_index_on_final(&expr));
}

#[test]
#[timeout(30000)]
fn index_on_final_with_index_method() {
    // Final(x).index(i) should also trigger
    let receiver = PureExpr::Final(Arc::new(var("x")));
    let expr = method_call(receiver, "index", vec![var("i")]);
    assert!(expr_has_seq_index_on_final(&expr));
}

#[test]
#[timeout(30000)]
fn index_on_final_false_for_non_final() {
    // View(x).index_logic(i) — no Final
    let receiver = PureExpr::View(Arc::new(var("x")));
    let expr = method_call(receiver, "index_logic", vec![var("i")]);
    assert!(!expr_has_seq_index_on_final(&expr));
}

#[test]
#[timeout(30000)]
fn index_on_final_false_for_bare_var() {
    // x.index_logic(i) — no Final
    let expr = method_call(var("x"), "index_logic", vec![var("i")]);
    assert!(!expr_has_seq_index_on_final(&expr));
}

#[test]
#[timeout(30000)]
fn index_on_final_false_for_non_index_method() {
    // Final(x).len() — index-like receiver but wrong method
    let receiver = PureExpr::Final(Arc::new(var("x")));
    let expr = method_call(receiver, "len", vec![]);
    assert!(!expr_has_seq_index_on_final(&expr));
}

#[test]
#[timeout(30000)]
fn index_on_final_nested_in_binop() {
    // x == Final(View(v)).index_logic(i)
    let receiver = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(var("v")))));
    let index_call = method_call(receiver, "index_logic", vec![var("i")]);
    let expr = PureExpr::BinOp(
        Arc::new(var("x")),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(index_call),
    );
    assert!(expr_has_seq_index_on_final(&expr));
}

#[test]
#[timeout(30000)]
fn index_on_final_false_for_literal() {
    assert!(!expr_has_seq_index_on_final(&PureExpr::Int(42)));
}

#[test]
#[timeout(30000)]
fn index_on_final_false_for_bool() {
    assert!(!expr_has_seq_index_on_final(&PureExpr::Bool(true)));
}

#[test]
#[timeout(30000)]
fn index_on_final_deref_then_final() {
    // Deref(Final(View(x))).index_logic(i) — Final inside Deref
    let inner = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(var("x")))));
    let receiver = PureExpr::Deref(Arc::new(inner));
    let expr = method_call(receiver, "index_logic", vec![var("i")]);
    assert!(expr_has_seq_index_on_final(&expr));
}

// --- expr_has_seq_method_needing_quantifiers ---

#[test]
#[timeout(30000)]
fn quantifiers_reverse() {
    let expr = method_call(var("s"), "reverse", vec![]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_sum() {
    let expr = method_call(var("s"), "sum", vec![]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_contains() {
    let expr = method_call(var("s"), "contains", vec![var("x")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_concat() {
    let expr = method_call(var("s"), "concat", vec![var("t")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_subsequence() {
    let expr = method_call(var("s"), "subsequence", vec![var("i"), var("j")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_ext_eq() {
    let expr = method_call(var("s"), "ext_eq", vec![var("t")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_push_back() {
    let expr = method_call(var("s"), "push_back", vec![var("x")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_push_front() {
    let expr = method_call(var("s"), "push_front", vec![var("x")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_push_front_ghost() {
    let expr = method_call(var("s"), "push_front_ghost", vec![var("x")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_set() {
    let expr = method_call(var("s"), "set", vec![var("i"), var("x")]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_to_owned_seq() {
    let expr = method_call(var("s"), "to_owned_seq", vec![]);
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_false_for_len() {
    // len doesn't require quantified axioms
    let expr = method_call(var("s"), "len", vec![]);
    assert!(!expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_false_for_index_logic() {
    // index_logic uses Array store/select, not quantified axioms
    let expr = method_call(var("s"), "index_logic", vec![var("i")]);
    assert!(!expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_false_for_get() {
    let expr = method_call(var("s"), "get", vec![var("i")]);
    assert!(!expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_false_for_literal() {
    assert!(!expr_has_seq_method_needing_quantifiers(&PureExpr::Int(0)));
}

#[test]
#[timeout(30000)]
fn quantifiers_nested_in_ite() {
    // if cond then s.reverse() else t
    let reverse = method_call(var("s"), "reverse", vec![]);
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(reverse),
        Arc::new(var("t")),
    );
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_logic_fn_seq_macro() {
    // LogicFnCall { name: "seq", args: [1, 2] } — the seq![] macro
    let expr = PureExpr::LogicFnCall {
        name: "seq".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(2)],
    };
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_logic_fn_non_seq() {
    // LogicFnCall { name: "my_fn", args: [] } — not seq
    let expr = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![],
    };
    assert!(!expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_nested_in_forall() {
    let reverse = method_call(var("s"), "reverse", vec![]);
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        triggers: vec![],
        body: Arc::new(reverse),
    };
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}

#[test]
#[timeout(30000)]
fn quantifiers_in_let_body() {
    let concat = method_call(var("s"), "concat", vec![var("t")]);
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(0)),
        body: Arc::new(concat),
    };
    assert!(expr_has_seq_method_needing_quantifiers(&expr));
}
