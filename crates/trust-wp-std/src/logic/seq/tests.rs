// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    logic::{ops::IndexLogic, Int, Mapping},
    seq,
};

// ── seq! macro tests ────────────────────────────────────────────

#[test]
fn test_seq_macro_empty() {
    let s: Seq<i32> = seq![];
    assert!(s.is_empty());
    assert_eq!(s.len(), Int(0));
}

#[test]
fn test_seq_macro_single() {
    let s = seq![42];
    assert_eq!(s.len(), Int(1));
    assert_eq!(Vec::from(s), vec![42]);
}

#[test]
fn test_seq_macro_single_trailing_comma() {
    let s = seq![42,];
    assert_eq!(s.len(), Int(1));
    assert_eq!(Vec::from(s), vec![42]);
}

#[test]
fn test_seq_macro_multiple() {
    let s = seq![1, 2, 3];
    assert_eq!(s.len(), Int(3));
    assert_eq!(Vec::from(s), vec![1, 2, 3]);
}

#[test]
fn test_seq_macro_multiple_trailing_comma() {
    let s = seq![10, 20, 30,];
    assert_eq!(s.len(), Int(3));
    assert_eq!(Vec::from(s), vec![10, 20, 30]);
}

// ── Existing tests ──────────────────────────────────────────────

#[test]
fn test_seq_empty() {
    let seq: Seq<i32> = Seq::empty();
    assert!(seq.clone().is_empty());
    assert_eq!(seq.len(), Int(0));
}

#[test]
fn test_seq_singleton() {
    let seq = Seq::singleton(42);
    assert!(!seq.clone().is_empty());
    assert_eq!(seq.clone().len(), Int(1));
    assert_eq!(seq.get(Int(0)), Some(42));
}

#[test]
fn test_seq_push_back() {
    let seq: Seq<i32> = Seq::empty();
    let seq = seq.push_back(1).push_back(2).push_back(3);
    assert_eq!(seq.clone().len(), Int(3));
    assert_eq!(seq.clone().index_logic(Int(0)), 1);
    assert_eq!(seq.clone().index_logic(Int(1)), 2);
    assert_eq!(seq.index_logic(Int(2)), 3);
}

#[test]
fn test_seq_push_front() {
    let seq: Seq<i32> = Seq::empty();
    let seq = seq.push_front(3).push_front(2).push_front(1);
    assert_eq!(seq.clone().len(), Int(3));
    assert_eq!(seq.clone().index_logic(Int(0)), 1);
    assert_eq!(seq.clone().index_logic(Int(1)), 2);
    assert_eq!(seq.index_logic(Int(2)), 3);
}

#[test]
fn test_seq_pop_back() {
    let seq = Seq::from(vec![1, 2, 3]);
    let seq = seq.pop_back();
    assert_eq!(seq.clone().len(), Int(2));
    assert_eq!(seq.clone().index_logic(Int(0)), 1);
    assert_eq!(seq.index_logic(Int(1)), 2);
}

#[test]
fn test_seq_tail() {
    let seq = Seq::from(vec![1, 2, 3]);
    let seq = seq.tail();
    assert_eq!(seq.clone().len(), Int(2));
    assert_eq!(seq.clone().index_logic(Int(0)), 2);
    assert_eq!(seq.index_logic(Int(1)), 3);
}

#[test]
fn test_seq_pop_front() {
    let seq = Seq::from(vec![1, 2, 3]);
    let seq = seq.pop_front();
    assert_eq!(seq.clone().len(), Int(2));
    assert_eq!(seq.index_logic(Int(0)), 2);
}

#[test]
fn test_seq_concat() {
    let seq1 = Seq::from(vec![1, 2]);
    let seq2 = Seq::from(vec![3, 4]);
    let seq = seq1.concat(seq2);
    assert_eq!(seq.clone().len(), Int(4));
    assert_eq!(Vec::from(seq), vec![1, 2, 3, 4]);
}

#[test]
fn test_seq_subsequence() {
    let seq = Seq::from(vec![0, 1, 2, 3, 4]);
    let sub = seq.subsequence(Int(1), Int(4));
    assert_eq!(Vec::from(sub), vec![1, 2, 3]);
}

#[test]
fn test_seq_set() {
    let seq = Seq::from(vec![1, 2, 3]);
    let seq = seq.set(Int(1), 42);
    assert_eq!(seq.clone().index_logic(Int(0)), 1);
    assert_eq!(seq.clone().index_logic(Int(1)), 42);
    assert_eq!(seq.index_logic(Int(2)), 3);
}

#[test]
fn test_seq_contains() {
    let seq = Seq::from(vec![1, 2, 3]);
    assert!(seq.clone().contains(2));
    assert!(!seq.contains(42));
}

#[test]
fn test_seq_contains_borrowed_value() {
    let value = String::from("beta");
    let seq = Seq::from(vec![value.clone(), "gamma".to_string()]);

    assert!(seq.contains(&value));
}

#[test]
fn test_seq_contains_pair() {
    let seq = Seq::from(vec![(1, "one"), (2, "two")]);

    assert!(seq.contains_pair(&1, &"one"));
    assert!(!seq.contains_pair(&2, &"three"));
}

#[test]
fn test_seq_matches_map() {
    let seq = Seq::from(vec![(1, "one"), (2, "two")]);
    let mut map = std::collections::HashMap::new();
    map.insert(1, "one");
    map.insert(2, "two");

    assert!(seq.matches_map(&map));

    map.insert(2, "deux");
    assert!(!seq.matches_map(&map));
}

#[test]
fn test_seq_sorted() {
    let sorted = Seq::from(vec![1, 2, 3, 4, 5]);
    let unsorted = Seq::from(vec![3, 1, 4, 1, 5]);
    assert!(sorted.sorted());
    assert!(!unsorted.sorted());

    // Edge cases: empty and single-element sequences are sorted
    let empty: Seq<i32> = Seq::empty();
    let single = Seq::singleton(42);
    assert!(empty.sorted());
    assert!(single.sorted());
}

#[test]
fn test_seq_sorted_range() {
    let seq = Seq::from(vec![5, 1, 2, 3, 9]);
    // Elements 1, 2, 3 at indices 1..4 are sorted
    assert!(seq.clone().sorted_range(Int(1), Int(4)));
    // Full sequence is not sorted
    assert!(!seq.sorted());
}

#[test]
fn test_seq_permutation_of() {
    let s1 = Seq::from(vec![1, 2, 3]);
    let s2 = Seq::from(vec![3, 1, 2]);
    let s3 = Seq::from(vec![1, 2, 4]);
    assert!(s1.clone().permutation_of(s2));
    assert!(!s1.clone().permutation_of(s3));

    // Edge cases
    let empty1: Seq<i32> = Seq::empty();
    let empty2: Seq<i32> = Seq::empty();
    assert!(empty1.permutation_of(empty2));

    // Different lengths are not permutations
    let short = Seq::from(vec![1, 2]);
    assert!(!s1.permutation_of(short));
}

#[test]
fn test_seq_count() {
    let seq = Seq::from(vec![1, 2, 2, 3, 2, 1]);
    assert_eq!(seq.clone().count(1), Int(2));
    assert_eq!(seq.clone().count(2), Int(3));
    assert_eq!(seq.clone().count(3), Int(1));
    assert_eq!(seq.count(42), Int(0));
}

#[test]
fn test_seq_exchange() {
    let s1 = Seq::from(vec![1, 2, 3]);
    let s2 = Seq::from(vec![3, 2, 1]);
    let s3 = Seq::from(vec![2, 1, 3]);
    assert!(s1.clone().exchange(s2.clone(), Int(0), Int(2))); // swap first and last
    assert!(s1.clone().exchange(s3, Int(0), Int(1))); // swap first two
    assert!(!s1.clone().exchange(s2.clone(), Int(0), Int(1))); // wrong swap indices

    // Edge case: same index (no-op swap, sequences must be equal)
    assert!(s1.clone().exchange(s1.clone(), Int(1), Int(1)));
    assert!(!s1.exchange(s2, Int(1), Int(1)));
}

#[test]
fn test_seq_reverse() {
    let seq = Seq::from(vec![1, 2, 3]);
    let rev = seq.reverse();
    assert_eq!(Vec::from(rev), vec![3, 2, 1]);

    // Empty and singleton reverse
    let empty: Seq<i32> = Seq::empty();
    assert!(empty.reverse().is_empty());
    let single = Seq::singleton(42);
    assert_eq!(Vec::from(single.reverse()), vec![42]);
}

#[test]
fn test_seq_cons() {
    let seq = Seq::from(vec![2, 3]);
    let seq = Seq::cons(1, seq);
    assert_eq!(Vec::from(seq), vec![1, 2, 3]);

    // cons onto empty
    let seq = Seq::cons(42, Seq::empty());
    assert_eq!(seq.clone().len(), Int(1));
    assert_eq!(seq.index_logic(Int(0)), 42);
}

#[test]
fn test_seq_ext_eq() {
    let s1 = Seq::from(vec![1, 2, 3]);
    let s2 = Seq::from(vec![1, 2, 3]);
    let s3 = Seq::from(vec![1, 2, 4]);
    assert!(s1.clone().ext_eq(s2));
    assert!(!s1.ext_eq(s3));

    // Empty sequences
    let e1: Seq<i32> = Seq::empty();
    let e2: Seq<i32> = Seq::empty();
    assert!(e1.ext_eq(e2));
}

#[test]
fn test_seq_permut() {
    let s1 = Seq::from(vec![1, 2, 3, 4, 5]);
    let s2 = Seq::from(vec![1, 3, 2, 4, 5]);
    // Permutation only in range [1, 3)
    assert!(s1.clone().permut(s2.clone(), Int(1), Int(3)));
    // Full range permutation
    assert!(s1.clone().permut(s2.clone(), Int(0), Int(5)));
    // Not a permutation if restricted to [0, 2) — element 0 differs
    assert!(!s1.clone().permut(s2, Int(0), Int(2)));

    // Edge: same sequence is always a permutation
    assert!(s1.clone().permut(s1.clone(), Int(0), Int(5)));
    assert!(s1.clone().permut(s1, Int(2), Int(4)));
}

#[test]
fn test_seq_index_logic_unsized() {
    let seq = Seq::from(vec![10, 20, 30]);
    assert_eq!(seq.index_logic_unsized(Int(0)), &10);
    assert_eq!(seq.index_logic_unsized(Int(1)), &20);
    assert_eq!(seq.index_logic_unsized(Int(2)), &30);
}

#[test]
fn test_seq_create() {
    // Create [0, 2, 4, 6, 8] via mapping i -> i*2
    let m: Mapping<Int, i32> = Mapping::cst(0)
        .set(Int(0), 0)
        .set(Int(1), 2)
        .set(Int(2), 4)
        .set(Int(3), 6)
        .set(Int(4), 8);
    let seq = Seq::create(Int(5), m);
    assert_eq!(seq.clone().len(), Int(5));
    assert_eq!(Vec::from(seq), vec![0, 2, 4, 6, 8]);
}

#[test]
fn test_seq_create_empty() {
    let m: Mapping<Int, i32> = Mapping::cst(42);
    let seq = Seq::create(Int(0), m);
    assert!(seq.is_empty());
}

#[test]
fn test_seq_create_constant() {
    // All elements should be the default value
    let m: Mapping<Int, i32> = Mapping::cst(7);
    let seq = Seq::create(Int(3), m);
    assert_eq!(Vec::from(seq), vec![7, 7, 7]);
}

#[test]
fn test_seq_map() {
    let seq = Seq::from(vec![1, 2, 3]);
    // Mapping: 1->10, 2->20, 3->30, default->0
    let m: Mapping<i32, i32> = Mapping::cst(0).set(1, 10).set(2, 20).set(3, 30);
    let mapped = seq.map(m);
    assert_eq!(mapped.clone().len(), Int(3));
    assert_eq!(Vec::from(mapped), vec![10, 20, 30]);
}

#[test]
fn test_seq_map_preserves_length() {
    let seq = Seq::from(vec![1, 2, 3, 4, 5]);
    let m: Mapping<i32, bool> = Mapping::cst(false).set(2, true).set(4, true);
    let mapped = seq.map(m);
    assert_eq!(mapped.clone().len(), Int(5));
    assert_eq!(Vec::from(mapped), vec![false, true, false, true, false]);
}

#[test]
fn test_seq_map_empty() {
    let seq: Seq<i32> = Seq::empty();
    let m: Mapping<i32, i32> = Mapping::cst(0);
    let mapped = seq.map(m);
    assert!(mapped.is_empty());
}

#[test]
fn test_seq_flat_map() {
    let seq = Seq::from(vec![1, 2, 3]);
    // Mapping: 1->[10], 2->[20, 21], 3->[30, 31, 32], default->[]
    let m: Mapping<i32, Seq<i32>> = Mapping::cst(Seq::empty())
        .set(1, Seq::from(vec![10]))
        .set(2, Seq::from(vec![20, 21]))
        .set(3, Seq::from(vec![30, 31, 32]));
    let result = seq.flat_map(m);
    assert_eq!(Vec::from(result), vec![10, 20, 21, 30, 31, 32]);
}

#[test]
fn test_seq_flat_map_empty_input() {
    let seq: Seq<i32> = Seq::empty();
    let m: Mapping<i32, Seq<i32>> = Mapping::cst(Seq::from(vec![99]));
    let result = seq.flat_map(m);
    assert!(result.is_empty());
}

#[test]
fn test_seq_flat_map_singleton() {
    // flat_map of singleton(x, f) == f.get(x)  (Creusot lemma)
    let seq = Seq::singleton(42);
    let expected = Seq::from(vec![1, 2, 3]);
    let m: Mapping<i32, Seq<i32>> = Mapping::cst(Seq::empty()).set(42, expected.clone());
    let result = seq.flat_map(m);
    assert_eq!(Vec::from(result), Vec::from(expected));
}

// ── to_owned_seq tests ──────────────────────────────────────────

#[test]
fn test_seq_to_owned_seq() {
    let values = vec![1, 2, 3];
    let refs: Vec<&i32> = values.iter().collect();
    let seq_refs = Seq::from(refs);
    let seq_owned = seq_refs.to_owned_seq();
    assert_eq!(seq_owned.len(), Int(3));
    assert_eq!(Vec::from(seq_owned), vec![1, 2, 3]);
}

#[test]
fn test_seq_to_owned_seq_empty() {
    let seq_refs: Seq<&i32> = Seq::empty();
    let seq_owned = seq_refs.to_owned_seq();
    assert!(seq_owned.is_empty());
}

#[test]
fn test_seq_to_owned_seq_preserves_order() {
    let values = vec![10, 20, 30, 40, 50];
    let refs: Vec<&i32> = values.iter().collect();
    let seq_refs = Seq::from(refs);
    let seq_owned = seq_refs.to_owned_seq();
    assert_eq!(seq_owned.clone().index_logic(Int(0)), 10);
    assert_eq!(seq_owned.clone().index_logic(Int(2)), 30);
    assert_eq!(seq_owned.index_logic(Int(4)), 50);
}

// ── IndexLogic trait implementation tests ───────────────────────

#[test]
fn test_seq_index_logic_int() {
    let s = Seq::from(vec![10, 20, 30]);
    assert_eq!(IndexLogic::index_logic(s, Int(1)), 20);
}

#[test]
fn test_seq_index_logic_range_int() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, Int(1)..Int(4));
    assert_eq!(Vec::from(sub), vec![20, 30, 40]);
}

#[test]
fn test_seq_index_logic_range_inclusive_int() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, Int(1)..=Int(3));
    assert_eq!(Vec::from(sub), vec![20, 30, 40]);
}

#[test]
fn test_seq_index_logic_range_full() {
    let s = Seq::from(vec![10, 20, 30]);
    let full: Seq<i32> = IndexLogic::index_logic(s.clone(), ..);
    assert_eq!(Vec::from(full), vec![10, 20, 30]);
}

#[test]
fn test_seq_index_logic_range_from_int() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, Int(2)..);
    assert_eq!(Vec::from(sub), vec![30, 40, 50]);
}

#[test]
fn test_seq_index_logic_range_to_int() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, ..Int(3));
    assert_eq!(Vec::from(sub), vec![10, 20, 30]);
}

#[test]
fn test_seq_index_logic_range_to_inclusive_int() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, ..=Int(2));
    assert_eq!(Vec::from(sub), vec![10, 20, 30]);
}

#[test]
fn test_seq_index_logic_range_usize() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, 1..4);
    assert_eq!(Vec::from(sub), vec![20, 30, 40]);
}

#[test]
fn test_seq_index_logic_range_from_usize() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, 2..);
    assert_eq!(Vec::from(sub), vec![30, 40, 50]);
}

#[test]
fn test_seq_index_logic_range_to_usize() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, ..3);
    assert_eq!(Vec::from(sub), vec![10, 20, 30]);
}

#[test]
fn test_seq_index_logic_range_inclusive_usize() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, 1..=3);
    assert_eq!(Vec::from(sub), vec![20, 30, 40]);
}

#[test]
fn test_seq_index_logic_range_to_inclusive_usize() {
    let s = Seq::from(vec![10, 20, 30, 40, 50]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, ..=2);
    assert_eq!(Vec::from(sub), vec![10, 20, 30]);
}

#[test]
fn test_seq_index_logic_empty_range() {
    let s = Seq::from(vec![10, 20, 30]);
    let sub: Seq<i32> = IndexLogic::index_logic(s, Int(1)..Int(1));
    assert!(sub.is_empty());
}

#[test]
fn test_seq_index_logic_full_range_equals_original() {
    let s = Seq::from(vec![10, 20, 30]);
    let via_from: Seq<i32> = IndexLogic::index_logic(s.clone(), Int(0)..);
    let via_to: Seq<i32> = IndexLogic::index_logic(s.clone(), ..Int(3));
    let via_full: Seq<i32> = IndexLogic::index_logic(s, ..);
    assert_eq!(Vec::from(via_from.clone()), Vec::from(via_to.clone()));
    assert_eq!(Vec::from(via_to), Vec::from(via_full));
}
