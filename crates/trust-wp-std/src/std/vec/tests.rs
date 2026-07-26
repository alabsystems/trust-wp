// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Vec specification trait.

use super::*;
use crate::logic::Int;

#[test]
fn test_vec_view_spec() {
    let v = vec![1, 2, 3];
    let seq = v.view_spec();
    assert_eq!(seq.len(), Int(3));
}

#[test]
fn test_vec_len_spec() {
    let v: Vec<i32> = vec![1, 2, 3];
    assert_eq!(v.len_spec(), 3);
}

#[test]
fn test_vec_is_empty_spec() {
    let empty: Vec<i32> = Vec::new();
    let non_empty = vec![1];
    assert!(empty.is_empty_spec());
    assert!(!non_empty.is_empty_spec());
}

#[test]
fn test_vec_push_spec() {
    let mut v = vec![1, 2];
    v.push_spec(3);
    assert_eq!(v, vec![1, 2, 3]);
}

#[test]
fn test_vec_pop_spec() {
    let mut v = vec![1, 2, 3];
    assert_eq!(v.pop_spec(), Some(3));
    assert_eq!(v, vec![1, 2]);

    let mut empty: Vec<i32> = Vec::new();
    assert_eq!(empty.pop_spec(), None);
}

#[test]
fn test_vec_clear_spec() {
    let mut v = vec![1, 2, 3];
    v.clear_spec();
    assert!(v.is_empty_spec());
}

#[test]
fn test_vec_first_last_spec() {
    let v = vec![1, 2, 3];
    assert_eq!(v.first_spec(), Some(&1));
    assert_eq!(v.last_spec(), Some(&3));

    let empty: Vec<i32> = Vec::new();
    assert_eq!(empty.first_spec(), None);
    assert_eq!(empty.last_spec(), None);
}

#[test]
fn test_vec_get_specs() {
    let mut v = vec![1, 2, 3];
    assert_eq!(v.get_spec(1), Some(&2));
    assert_eq!(v.get_spec(10), None);
    if let Some(slot) = v.get_mut_spec(2) {
        *slot = 99;
    }
    assert_eq!(v, vec![1, 2, 99]);
}

#[test]
fn test_vec_capacity_specs() {
    let mut v: Vec<i32> = Vec::new();
    let initial_capacity = v.capacity_spec();
    v.reserve_spec(10);
    assert!(v.capacity_spec() >= initial_capacity);
    assert!(v.capacity_spec() >= v.len() + 10);
}

#[test]
fn test_vec_shrink_to_fit_spec() {
    let mut v = vec![1, 2, 3];
    v.shrink_to_fit_spec();
    assert_eq!(v, vec![1, 2, 3]);
}

#[test]
fn test_vec_truncate_spec() {
    let mut v = vec![1, 2, 3];
    v.truncate_spec(1);
    assert_eq!(v, vec![1]);
}

#[test]
fn test_vec_resize_spec() {
    let mut v = vec![1, 2];
    v.resize_spec(4, 9);
    assert_eq!(v, vec![1, 2, 9, 9]);
    v.resize_spec(1, 0);
    assert_eq!(v, vec![1]);
}

#[test]
fn test_vec_insert_remove_spec() {
    let mut v = vec![1, 3];
    v.insert_spec(1, 2);
    assert_eq!(v, vec![1, 2, 3]);
    assert_eq!(v.remove_spec(1), 2);
    assert_eq!(v, vec![1, 3]);
}

#[test]
fn test_vec_swap_spec() {
    let mut v = vec![1, 2, 3];
    v.swap_spec(0, 2);
    assert_eq!(v, vec![3, 2, 1]);
    // Swap same index is no-op
    v.swap_spec(1, 1);
    assert_eq!(v, vec![3, 2, 1]);
}

#[test]
fn test_vec_contains_spec() {
    let v = vec![1, 2, 3];
    assert!(v.contains_spec(&2));
    assert!(!v.contains_spec(&4));
    let empty: Vec<i32> = Vec::new();
    assert!(!empty.contains_spec(&1));
}
