// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `iterator_spec_rewrite::helpers` sort detection functions.

use std::sync::Arc;

use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use super::super::helpers::{
    is_fmap_backed_iterator, is_logical_fmap_iter, is_seq_backed_iterator, receiver_datatype_id,
    receiver_root_sort,
};

fn datatype_var(name: &str, sort_name: &str) -> PureExpr {
    let id = intern_sort_name(sort_name);
    PureExpr::Var(name.to_string(), Some(ExprSort::Datatype(id)))
}

// --- receiver_root_sort ---

#[test]
fn test_receiver_root_sort_direct_var() {
    let v = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    assert_eq!(receiver_root_sort(&v), Some(&ExprSort::Int));
}

#[test]
fn test_receiver_root_sort_nested_wrappers() {
    let inner = PureExpr::Var("it".to_string(), Some(ExprSort::Seq));
    let wrapped = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(PureExpr::Old(Arc::new(
        PureExpr::Deref(Arc::new(inner)),
    ))))));
    assert_eq!(receiver_root_sort(&wrapped), Some(&ExprSort::Seq));
}

#[test]
fn test_receiver_root_sort_no_sort() {
    let v = PureExpr::Var("x".to_string(), None);
    assert_eq!(receiver_root_sort(&v), None);
}

#[test]
fn test_receiver_root_sort_non_var_returns_none() {
    assert_eq!(receiver_root_sort(&PureExpr::Int(42)), None);
}

#[test]
fn test_receiver_root_sort_method_call_returns_none() {
    let mc = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), Some(ExprSort::Seq))),
        method: "len".to_string(),
        args: vec![],
    };
    assert_eq!(receiver_root_sort(&mc), None);
}

// --- receiver_datatype_id ---

#[test]
fn test_receiver_datatype_id_datatype_var() {
    let v = datatype_var("it", "alloc::vec::into_iter::IntoIter");
    let id = receiver_datatype_id(&v);
    assert!(id.is_some());
    assert_eq!(
        id.unwrap(),
        intern_sort_name("alloc::vec::into_iter::IntoIter")
    );
}

#[test]
fn test_receiver_datatype_id_non_datatype_returns_none() {
    let v = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    assert_eq!(receiver_datatype_id(&v), None);
}

#[test]
fn test_receiver_datatype_id_through_wrappers() {
    let inner = datatype_var("it", "core::ops::range::Range");
    let wrapped = PureExpr::Old(Arc::new(inner));
    assert!(receiver_datatype_id(&wrapped).is_some());
}

#[test]
fn test_receiver_datatype_id_strips_ref_like_sorts() {
    let id = intern_sort_name("core::ops::range::Range");
    let v = PureExpr::Var(
        "it".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(id)))),
    );
    assert_eq!(receiver_datatype_id(&v), Some(id));
}

// --- is_seq_backed_iterator ---

#[test]
fn test_is_seq_backed_iterator_seq_iter() {
    let v = datatype_var("it", "trust_wp_std::logic::seq::SeqIter");
    assert!(is_seq_backed_iterator(&v));
}

#[test]
fn test_is_seq_backed_iterator_vec_into_iter() {
    let v = datatype_var("it", "alloc::vec::into_iter::IntoIter");
    assert!(is_seq_backed_iterator(&v));
}

#[test]
fn test_is_seq_backed_iterator_range_returns_false() {
    let v = datatype_var("it", "core::ops::range::Range");
    assert!(!is_seq_backed_iterator(&v));
}

#[test]
fn test_is_seq_backed_iterator_int_returns_false() {
    let v = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    assert!(!is_seq_backed_iterator(&v));
}

#[test]
fn test_is_seq_backed_iterator_through_wrappers() {
    let inner = datatype_var("it", "trust_wp_std::logic::seq::SeqIter");
    let wrapped = PureExpr::View(Arc::new(PureExpr::Old(Arc::new(inner))));
    assert!(is_seq_backed_iterator(&wrapped));
}

// --- is_fmap_backed_iterator ---

#[test]
fn test_is_fmap_backed_fmap_iter() {
    let v = datatype_var("it", "trust_wp_std::logic::fmap::FMapIter");
    assert!(is_fmap_backed_iterator(&v));
}

#[test]
fn test_is_fmap_backed_hash_map_into_iter() {
    let v = datatype_var("it", "std::collections::hash_map::IntoIter");
    assert!(is_fmap_backed_iterator(&v));
}

#[test]
fn test_is_fmap_backed_hash_map_iter() {
    let v = datatype_var("it", "std::collections::hash_map::Iter");
    assert!(is_fmap_backed_iterator(&v));
}

#[test]
fn test_is_fmap_backed_hash_map_iter_mut() {
    let v = datatype_var("it", "std::collections::hash_map::IterMut");
    assert!(is_fmap_backed_iterator(&v));
}

#[test]
fn test_is_fmap_backed_vec_into_iter_returns_false() {
    let v = datatype_var("it", "alloc::vec::into_iter::IntoIter");
    assert!(!is_fmap_backed_iterator(&v));
}

#[test]
fn test_is_fmap_backed_hash_set_returns_false() {
    let v = datatype_var("it", "std::collections::hash_set::IntoIter");
    assert!(!is_fmap_backed_iterator(&v));
}

// --- is_logical_fmap_iter ---

#[test]
fn test_is_logical_fmap_iter_fmap_iter() {
    let v = datatype_var("it", "trust_wp_std::logic::fmap::FMapIter");
    assert!(is_logical_fmap_iter(&v));
}

#[test]
fn test_is_logical_fmap_iter_hash_map_into_iter_returns_false() {
    let v = datatype_var("it", "std::collections::hash_map::IntoIter");
    assert!(
        !is_logical_fmap_iter(&v),
        "HashMap::IntoIter is fmap-backed but NOT logical FMapIter"
    );
}

#[test]
fn test_is_logical_fmap_iter_hash_map_iter_returns_false() {
    let v = datatype_var("it", "std::collections::hash_map::Iter");
    assert!(!is_logical_fmap_iter(&v));
}

#[test]
fn test_is_logical_fmap_iter_creusot_alias() {
    let v = datatype_var("it", "creusot_std::logic::fmap::Iter");
    assert!(is_logical_fmap_iter(&v));
}
