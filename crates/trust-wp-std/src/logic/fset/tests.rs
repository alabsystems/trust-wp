// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for FSet (finite set) logical type.

use super::*;
use crate::logic::{Int, Mapping};

#[test]
fn test_fset_empty() {
    let set: FSet<i32> = FSet::empty();
    assert!(set.clone().is_empty());
    assert_eq!(set.len(), Int(0));
}

#[test]
fn test_fset_singleton() {
    let set = FSet::singleton(42);
    assert!(!set.clone().is_empty());
    assert_eq!(set.clone().len(), Int(1));
    assert!(set.clone().contains(42));
    assert!(!set.contains(0));
}

#[test]
fn test_fset_insert() {
    let set: FSet<i32> = FSet::empty();
    let set = set.insert(1).insert(2).insert(3);
    assert_eq!(set.clone().len(), Int(3));
    assert!(set.clone().contains(1));
    assert!(set.clone().contains(2));
    assert!(set.clone().contains(3));
    assert!(!set.contains(4));
}

#[test]
fn test_fset_contains_borrowed_value() {
    let value = String::from("alpha");
    let set = FSet::empty().insert(value.clone());

    assert!(set.contains(&value));
    assert!(set.contains(value));
}

#[test]
fn test_fset_insert_duplicate() {
    let set = FSet::singleton(42);
    let set = set.insert(42);
    assert_eq!(set.len(), Int(1)); // No change - 42 was already present
}

#[test]
fn test_fset_remove() {
    let set = FSet::empty().insert(1).insert(2).insert(3);
    let set = set.remove(&2);
    assert_eq!(set.clone().len(), Int(2));
    assert!(set.clone().contains(1));
    assert!(!set.clone().contains(2));
    assert!(set.contains(3));
}

#[test]
fn test_fset_union() {
    let set1 = FSet::empty().insert(1).insert(2);
    let set2 = FSet::empty().insert(2).insert(3);
    let union = set1.union(set2);
    assert_eq!(union.clone().len(), Int(3));
    assert!(union.clone().contains(1));
    assert!(union.clone().contains(2));
    assert!(union.contains(3));
}

#[test]
fn test_fset_intersection() {
    let set1 = FSet::empty().insert(1).insert(2).insert(3);
    let set2 = FSet::empty().insert(2).insert(3).insert(4);
    let inter = set1.intersection(set2);
    assert_eq!(inter.clone().len(), Int(2));
    assert!(!inter.clone().contains(1));
    assert!(inter.clone().contains(2));
    assert!(inter.clone().contains(3));
    assert!(!inter.contains(4));
}

#[test]
fn test_fset_difference() {
    let set1 = FSet::empty().insert(1).insert(2).insert(3);
    let set2 = FSet::empty().insert(2).insert(4);
    let diff = set1.difference(set2);
    assert_eq!(diff.clone().len(), Int(2));
    assert!(diff.clone().contains(1));
    assert!(!diff.clone().contains(2));
    assert!(diff.contains(3));
}

#[test]
fn test_fset_subset() {
    let set1 = FSet::empty().insert(1).insert(2);
    let set2 = FSet::empty().insert(1).insert(2).insert(3);
    assert!(set1.clone().is_subset(set2.clone()));
    assert!(!set2.clone().is_subset(set1.clone()));
    assert!(set2.is_superset(set1));
}

#[test]
fn test_fset_disjoint() {
    let set1 = FSet::empty().insert(1).insert(2);
    let set2 = FSet::empty().insert(3).insert(4);
    let set3 = FSet::empty().insert(2).insert(5);
    assert!(set1.clone().disjoint(set2));
    assert!(!set1.disjoint(set3));
}

#[test]
fn test_fset_peek() {
    let empty: FSet<i32> = FSet::empty();
    assert!(empty.peek().is_none());

    let singleton = FSet::singleton(42);
    assert_eq!(singleton.peek(), Some(42));
}

#[test]
fn test_fset_ext_eq() {
    let s1 = FSet::empty().insert(1).insert(2).insert(3);
    let s2 = FSet::empty().insert(3).insert(1).insert(2);
    let s3 = FSet::empty().insert(1).insert(2);
    assert!(s1.clone().ext_eq(s2));
    assert!(!s1.ext_eq(s3));

    // Empty sets
    let e1: FSet<i32> = FSet::empty();
    let e2: FSet<i32> = FSet::empty();
    assert!(e1.ext_eq(e2));
}

#[test]
fn test_fset_filter() {
    let set = FSet::empty()
        .insert(1)
        .insert(2)
        .insert(3)
        .insert(4)
        .insert(5);
    // Keep only even numbers
    let even: Mapping<i32, bool> = Mapping::cst(false).set(2, true).set(4, true);
    let filtered = set.filter(even);
    assert_eq!(filtered.clone().len(), Int(2));
    assert!(filtered.clone().contains(2));
    assert!(filtered.clone().contains(4));
    assert!(!filtered.contains(1));
}

#[test]
fn test_fset_filter_empty() {
    let set: FSet<i32> = FSet::empty();
    let f: Mapping<i32, bool> = Mapping::cst(true);
    let filtered = set.filter(f);
    assert!(filtered.is_empty());
}

#[test]
fn test_fset_filter_all() {
    let set = FSet::empty().insert(1).insert(2).insert(3);
    let all_true: Mapping<i32, bool> = Mapping::cst(true);
    let filtered = set.clone().filter(all_true);
    assert_eq!(filtered.len(), Int(3));

    let all_false: Mapping<i32, bool> = Mapping::cst(false);
    let filtered = set.filter(all_false);
    assert!(filtered.is_empty());
}

#[test]
fn test_fset_map() {
    let set = FSet::empty().insert(1).insert(2).insert(3);
    // Double each element
    let double: Mapping<i32, i32> = Mapping::cst(0).set(1, 2).set(2, 4).set(3, 6);
    let mapped = set.map(double);
    assert_eq!(mapped.clone().len(), Int(3));
    assert!(mapped.clone().contains(2));
    assert!(mapped.clone().contains(4));
    assert!(mapped.contains(6));
}

#[test]
fn test_fset_map_collapsing() {
    // When mapping is not injective, result set may be smaller
    let set = FSet::empty().insert(1).insert(2).insert(3);
    // Map everything to the same value
    let collapse: Mapping<i32, i32> = Mapping::cst(42);
    let mapped = set.map(collapse);
    assert_eq!(mapped.clone().len(), Int(1));
    assert!(mapped.contains(42));
}

#[test]
fn test_fset_map_empty() {
    let set: FSet<i32> = FSet::empty();
    let f: Mapping<i32, i32> = Mapping::cst(0);
    let mapped = set.map(f);
    assert!(mapped.is_empty());
}

#[test]
fn test_fset_unions() {
    let set = FSet::empty().insert(1).insert(2);
    // 1 -> {10, 11}, 2 -> {20, 21}, default -> {}
    let f: Mapping<i32, FSet<i32>> = Mapping::cst(FSet::empty())
        .set(1, FSet::empty().insert(10).insert(11))
        .set(2, FSet::empty().insert(20).insert(21));
    let result = set.unions(f);
    assert_eq!(result.clone().len(), Int(4));
    assert!(result.clone().contains(10));
    assert!(result.clone().contains(11));
    assert!(result.clone().contains(20));
    assert!(result.contains(21));
}

#[test]
fn test_fset_unions_overlapping() {
    let set = FSet::empty().insert(1).insert(2);
    // Both map to sets containing 99
    let f: Mapping<i32, FSet<i32>> = Mapping::cst(FSet::empty())
        .set(1, FSet::empty().insert(10).insert(99))
        .set(2, FSet::empty().insert(20).insert(99));
    let result = set.unions(f);
    assert_eq!(result.clone().len(), Int(3)); // {10, 20, 99} — 99 not duplicated
    assert!(result.clone().contains(10));
    assert!(result.clone().contains(20));
    assert!(result.contains(99));
}

#[test]
fn test_fset_unions_empty() {
    let set: FSet<i32> = FSet::empty();
    let f: Mapping<i32, FSet<i32>> = Mapping::cst(FSet::singleton(42));
    let result = set.unions(f);
    assert!(result.is_empty());
}
