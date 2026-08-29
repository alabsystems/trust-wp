// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for sort-aware dispatch fallback in ambiguous method encoding (#994).
//!
//! When annotation/hint-based classifiers (`is_seq_receiver`, `is_fmap_receiver`)
//! fail to determine the collection type for ambiguous methods (len, contains,
//! is_empty), the dispatch must check `infer_encoded_sort` as a safety net to
//! prevent misrouting Seq/FMap receivers to FSet operations (which expect
//! Sort::Int domain).
//!
//! Key scenarios:
//! - Seq model types surfaced through Datatype annotations (Vec, VecDeque)
//! - Loop-generated variables that lose their original annotations
//! - FMap-sorted variables that structurally produce FMap results
//!
//! Companion to the production fix in `method_call/mod.rs`.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::intern_sort_name;

use super::*;

fn seq_sort() -> Sort {
    Sort::seq(Sort::Int)
}

fn fmap_sort() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

// ── Datatype annotation → Seq inference ─────────────────────────────────

/// `Datatype(VecDeque)` annotation on a Var expression should be detected as Seq
/// by the sort inference path that backs `infer_encoded_sort`. (#994)
///
/// This exercises the Datatype-backed Seq path without relying on the bare-name
/// `List` alias, which collides with user-defined ADTs in compat fixtures.
#[test]
#[timeout(30000)]
fn test_datatype_vecdeque_var_infers_seq_sort() {
    let id = intern_sort_name("VecDeque");
    let expr = PureExpr::Var("list".to_string(), Some(ExprSort::Datatype(id)));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "Var with Datatype(VecDeque) annotation should infer to Seq sort"
    );
}

/// `Datatype(Vec)` — the standard Seq model type.
#[test]
#[timeout(30000)]
fn test_datatype_vec_var_infers_seq_sort() {
    let id = intern_sort_name("Vec");
    let expr = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "Var with Datatype(Vec) annotation should infer to Seq sort"
    );
}

/// `Datatype(Seq)` remains on the canonical Seq carrier.
#[test]
#[timeout(30000)]
fn test_datatype_seq_var_infers_seq_sort() {
    let id = intern_sort_name("Seq");
    let expr = PureExpr::Var("d".to_string(), Some(ExprSort::Datatype(id)));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "Var with Datatype(Seq) annotation should infer to Seq sort"
    );
}

/// `Ref(Datatype(VecDeque))` annotation also infers Seq.
#[test]
#[timeout(30000)]
fn test_ref_datatype_vecdeque_var_infers_seq_sort() {
    let id = intern_sort_name("VecDeque");
    let expr = PureExpr::Var(
        "l".to_string(),
        Some(ExprSort::Ref(Box::new(ExprSort::Datatype(id)))),
    );
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "Var with Ref(Datatype(VecDeque)) should infer to Seq sort"
    );
}

/// `Deref(Var("l", Ref(Datatype(VecDeque))))` — the common wrapper pattern.
#[test]
#[timeout(30000)]
fn test_deref_ref_datatype_vecdeque_infers_seq_sort() {
    let id = intern_sort_name("VecDeque");
    let inner = PureExpr::Var(
        "l".to_string(),
        Some(ExprSort::Ref(Box::new(ExprSort::Datatype(id)))),
    );
    let expr = PureExpr::Deref(Arc::new(inner));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "Deref(Var with Ref(Datatype(VecDeque))) should infer to Seq sort"
    );
}

/// `Final(Var("l", Ref(Datatype(VecDeque))))` — the pattern for `^l` (final value
/// of a mutable borrow) in postconditions and loop invariants.
#[test]
#[timeout(30000)]
fn test_final_ref_datatype_vecdeque_infers_seq_sort() {
    let id = intern_sort_name("VecDeque");
    let inner = PureExpr::Var(
        "l".to_string(),
        Some(ExprSort::Ref(Box::new(ExprSort::Datatype(id)))),
    );
    let expr = PureExpr::Final(Arc::new(inner));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "Final(Var with Ref(Datatype(VecDeque))) should infer to Seq sort"
    );
}

// ── Non-Seq Datatype annotations must NOT infer Seq ─────────────────────

/// `Datatype(HashMap)` must infer FMap, NOT Seq.
#[test]
#[timeout(30000)]
fn test_datatype_hashmap_infers_fmap_not_seq() {
    let id = intern_sort_name("HashMap");
    let expr = PureExpr::Var("m".to_string(), Some(ExprSort::Datatype(id)));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        fmap_sort(),
        "Datatype(HashMap) should infer as FMap, not Seq"
    );
}

/// `Datatype(String)` is not a collection — should NOT infer Seq or FMap.
#[test]
#[timeout(30000)]
fn test_datatype_string_infers_uninterpreted() {
    let id = intern_sort_name("String");
    let expr = PureExpr::Var("s".to_string(), Some(ExprSort::Datatype(id)));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_ne!(inferred, seq_sort(), "String must not infer as Seq");
    assert_ne!(inferred, fmap_sort(), "String must not infer as FMap");
}

// ── FMap structural detection ───────────────────────────────────────────

/// FMap constructor LogicFnCalls should infer FMap sort.
#[test]
#[timeout(30000)]
fn test_fmap_empty_logic_fn_infers_fmap_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "fmap_empty".to_string(),
        args: vec![],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        fmap_sort(),
        "fmap_empty should infer as FMap sort"
    );
}

/// `insert` with 1 arg is FSet, not FMap. Sort inference should NOT return FMap.
#[test]
#[timeout(30000)]
fn test_fset_insert_1arg_does_not_infer_fmap() {
    let receiver = PureExpr::Var("s".to_string(), None);
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "insert".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_ne!(
        inferred,
        fmap_sort(),
        "1-arg insert (FSet) should NOT infer as FMap"
    );
}

/// Bare `ExprSort::Seq` annotation infers Seq (baseline).
#[test]
#[timeout(30000)]
fn test_bare_expr_sort_seq_infers_seq() {
    let expr = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "ExprSort::Seq annotation should infer Seq"
    );
}

/// Unannotated variable (None annotation) defaults to Int.
#[test]
#[timeout(30000)]
fn test_unannotated_var_infers_int() {
    let expr = PureExpr::Var("x".to_string(), None);
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(inferred, Sort::Int, "Unannotated var should default to Int");
}

// ── Seq constructor LogicFnCalls ──────────────────────────────────────────

/// `seq_empty` should infer Seq sort (constructor for empty sequence).
#[test]
#[timeout(30000)]
fn test_seq_empty_logic_fn_infers_seq_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(inferred, seq_sort(), "seq_empty should infer as Seq sort");
}

/// `Seq::empty` should infer Seq sort.
#[test]
#[timeout(30000)]
fn test_seq_ns_empty_logic_fn_infers_seq_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "Seq::empty".to_string(),
        args: vec![],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(inferred, seq_sort(), "Seq::empty should infer as Seq sort");
}

// ── MethodCall receiver sort propagation for non-excluded methods ──────────

/// A non-excluded method (e.g., `push_back`) on a `Datatype(Vec)` receiver
/// should propagate the receiver's Seq sort. (#994 Phase 2c)
#[test]
#[timeout(30000)]
fn test_method_on_datatype_vec_push_back_propagates_seq_sort() {
    let id = intern_sort_name("Vec");
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "push_back".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        seq_sort(),
        "push_back on Datatype(Vec) receiver should propagate Seq sort"
    );
}

/// `len` is in the exclusion list — it returns Int even when the receiver
/// has a Datatype(Vec) annotation. This is by design: len measures sequence
/// length and always returns an integer.
#[test]
#[timeout(30000)]
fn test_method_on_datatype_vec_len_excluded_returns_int() {
    let id = intern_sort_name("Vec");
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "len".to_string(),
        args: vec![],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_ne!(
        inferred,
        seq_sort(),
        "len on Datatype(Vec) should NOT propagate Seq sort"
    );
}

// ── Ghost block root cause documentation tests ─────────────────────────

/// Unknown LogicFnCall names default to Int with sort_fallback_to_int_from_logic_fn.
/// This is the root cause of ghost_vec's 17 fallback_from_logic_fn hits:
/// ghost block operations like `pop_back_ghost`, `get_ghost` are lowered to
/// LogicFnCall nodes whose names don't match any known constructor pattern.
#[test]
#[timeout(30000)]
fn test_unknown_logic_fn_call_defaults_to_int() {
    let expr = PureExpr::LogicFnCall {
        name: "some_unknown_ghost_op".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        Sort::Int,
        "Unknown LogicFnCall should default to Int (documents ghost_vec root cause)"
    );
}

/// Tuple constructors infer their tuple sort.
#[test]
#[timeout(30000)]
fn test_tuple_constructor_logic_fn_infers_tuple_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple2".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("b".to_string(), None),
        ],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        Sort::Uninterpreted("Tuple2".to_string()),
        "Tuple2 constructor should infer Tuple2 sort"
    );
}

// ── Ghost helper method sort inference (#2671) ────────────────────────

fn option_int_sort() -> Sort {
    use crate::encoder::match_enc::SwitchTarget;
    Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name)
}

fn unit_sort() -> Sort {
    Sort::Uninterpreted("Unit".to_string())
}

/// `len_ghost` should infer Int (returns length, always integer).
#[test]
#[timeout(30000)]
fn test_ghost_len_ghost_infers_int() {
    let expr = PureExpr::LogicFnCall {
        name: "len_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(inferred, Sort::Int, "len_ghost should infer Int");
}

/// `is_empty_ghost` should infer Bool.
#[test]
#[timeout(30000)]
fn test_ghost_is_empty_ghost_infers_bool() {
    let expr = PureExpr::LogicFnCall {
        name: "is_empty_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(inferred, Sort::Bool, "is_empty_ghost should infer Bool");
}

/// `contains_ghost` should infer Bool.
#[test]
#[timeout(30000)]
fn test_ghost_contains_ghost_infers_bool() {
    let expr = PureExpr::LogicFnCall {
        name: "contains_ghost".to_string(),
        args: vec![PureExpr::Var("s".to_string(), None), PureExpr::Int(1)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(inferred, Sort::Bool, "contains_ghost should infer Bool");
}

/// `get_ghost` should infer OptionInt (returns Option<T>).
#[test]
#[timeout(30000)]
fn test_ghost_get_ghost_infers_option() {
    let expr = PureExpr::LogicFnCall {
        name: "get_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None), PureExpr::Int(0)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        option_int_sort(),
        "get_ghost should infer OptionInt"
    );
}

/// `get_mut_ghost` should infer OptionInt (returns Option<&mut T>).
#[test]
#[timeout(30000)]
fn test_ghost_get_mut_ghost_infers_option() {
    let expr = PureExpr::LogicFnCall {
        name: "get_mut_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None), PureExpr::Int(0)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        option_int_sort(),
        "get_mut_ghost should infer OptionInt"
    );
}

/// `pop_back_ghost` should infer OptionInt (returns Option<T>).
#[test]
#[timeout(30000)]
fn test_ghost_pop_back_ghost_infers_option() {
    let expr = PureExpr::LogicFnCall {
        name: "pop_back_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        option_int_sort(),
        "pop_back_ghost should infer OptionInt"
    );
}

/// `pop_front_ghost` should infer OptionInt (returns Option<T>).
#[test]
#[timeout(30000)]
fn test_ghost_pop_front_ghost_infers_option() {
    let expr = PureExpr::LogicFnCall {
        name: "pop_front_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        option_int_sort(),
        "pop_front_ghost should infer OptionInt"
    );
}

/// `push_back_ghost` should infer unit sort (returns ()).
#[test]
#[timeout(30000)]
fn test_ghost_push_back_ghost_infers_unit() {
    let expr = PureExpr::LogicFnCall {
        name: "push_back_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None), PureExpr::Int(42)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        unit_sort(),
        "push_back_ghost should infer unit sort"
    );
}

/// `push_front_ghost` should infer unit sort (returns ()).
#[test]
#[timeout(30000)]
fn test_ghost_push_front_ghost_infers_unit() {
    let expr = PureExpr::LogicFnCall {
        name: "push_front_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None), PureExpr::Int(42)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        unit_sort(),
        "push_front_ghost should infer unit sort"
    );
}

/// `insert_ghost` should default to OptionInt (FMap path).
#[test]
#[timeout(30000)]
fn test_ghost_insert_ghost_infers_option() {
    let expr = PureExpr::LogicFnCall {
        name: "insert_ghost".to_string(),
        args: vec![
            PureExpr::Var("m".to_string(), None),
            PureExpr::Int(1),
            PureExpr::Int(2),
        ],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        option_int_sort(),
        "insert_ghost should default to OptionInt (FMap common case)"
    );
}

/// `remove_ghost` should default to OptionInt (FMap path).
#[test]
#[timeout(30000)]
fn test_ghost_remove_ghost_infers_option() {
    let expr = PureExpr::LogicFnCall {
        name: "remove_ghost".to_string(),
        args: vec![PureExpr::Var("m".to_string(), None), PureExpr::Int(1)],
    };
    let inferred = crate::encoder::sort_context::infer_expr_sort(&expr);
    assert_eq!(
        inferred,
        option_int_sort(),
        "remove_ghost should default to OptionInt (FMap common case)"
    );
}
