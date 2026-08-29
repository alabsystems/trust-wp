// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::encoder::seq::classification`] Seq method classifiers.
//!
//! Coverage gap: `classification.rs` (71 LOC) defines the authoritative
//! `method_produces_seq`, `method_produces_seq_unconditional`, and
//! `is_seq_only_method` predicates used by sort inference, prescan, and
//! encoding dispatch — with zero direct unit tests.

use ntest::timeout;

use crate::encoder::seq::{
    classification::method_produces_seq, is_seq_only_method, method_produces_seq_unconditional,
};

// --- method_produces_seq ---

#[test]
#[timeout(30000)]
fn produces_seq_push_back() {
    assert!(method_produces_seq("push_back"));
}

#[test]
#[timeout(30000)]
fn produces_seq_push_back_ghost() {
    assert!(method_produces_seq("push_back_ghost"));
}

#[test]
#[timeout(30000)]
fn produces_seq_push_front() {
    assert!(method_produces_seq("push_front"));
}

#[test]
#[timeout(30000)]
fn produces_seq_push_front_ghost() {
    assert!(method_produces_seq("push_front_ghost"));
}

#[test]
#[timeout(30000)]
fn produces_seq_pop_front() {
    assert!(method_produces_seq("pop_front"));
}

#[test]
#[timeout(30000)]
fn produces_seq_pop_front_ghost() {
    assert!(method_produces_seq("pop_front_ghost"));
}

#[test]
#[timeout(30000)]
fn produces_seq_pop_back() {
    assert!(method_produces_seq("pop_back"));
}

#[test]
#[timeout(30000)]
fn produces_seq_pop_back_ghost() {
    assert!(method_produces_seq("pop_back_ghost"));
}

#[test]
#[timeout(30000)]
fn produces_seq_tail() {
    assert!(method_produces_seq("tail"));
}

#[test]
#[timeout(30000)]
fn produces_seq_reverse() {
    assert!(method_produces_seq("reverse"));
}

#[test]
#[timeout(30000)]
fn produces_seq_to_owned_seq() {
    assert!(method_produces_seq("to_owned_seq"));
}

#[test]
#[timeout(30000)]
fn produces_seq_concat() {
    assert!(method_produces_seq("concat"));
}

#[test]
#[timeout(30000)]
fn produces_seq_subsequence() {
    assert!(method_produces_seq("subsequence"));
}

#[test]
#[timeout(30000)]
fn produces_seq_set() {
    assert!(method_produces_seq("set"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_len() {
    assert!(!method_produces_seq("len"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_get() {
    assert!(!method_produces_seq("get"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_index_logic() {
    assert!(!method_produces_seq("index_logic"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_contains() {
    assert!(!method_produces_seq("contains"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_insert() {
    assert!(!method_produces_seq("insert"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_len_logic() {
    assert!(!method_produces_seq("len_logic"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_ext_eq() {
    assert!(!method_produces_seq("ext_eq"));
}

#[test]
#[timeout(30000)]
fn produces_seq_false_for_into_seq() {
    assert!(!method_produces_seq("into_seq"));
}

// --- method_produces_seq_unconditional ---

#[test]
#[timeout(30000)]
fn unconditional_excludes_set() {
    // set is ambiguous between Seq and FSet
    assert!(!method_produces_seq_unconditional("set"));
}

#[test]
#[timeout(30000)]
fn unconditional_includes_push_back() {
    assert!(method_produces_seq_unconditional("push_back"));
}

#[test]
#[timeout(30000)]
fn unconditional_includes_concat() {
    assert!(method_produces_seq_unconditional("concat"));
}

#[test]
#[timeout(30000)]
fn unconditional_includes_tail() {
    assert!(method_produces_seq_unconditional("tail"));
}

#[test]
#[timeout(30000)]
fn unconditional_includes_reverse() {
    assert!(method_produces_seq_unconditional("reverse"));
}

#[test]
#[timeout(30000)]
fn unconditional_includes_subsequence() {
    assert!(method_produces_seq_unconditional("subsequence"));
}

#[test]
#[timeout(30000)]
fn unconditional_false_for_len() {
    assert!(!method_produces_seq_unconditional("len"));
}

#[test]
#[timeout(30000)]
fn unconditional_false_for_into_seq() {
    assert!(!method_produces_seq_unconditional("into_seq"));
}

// --- is_seq_only_method ---

#[test]
#[timeout(30000)]
fn seq_only_includes_len_logic() {
    // len_logic is Seq-only but doesn't produce a Seq result
    assert!(is_seq_only_method("len_logic"));
}

#[test]
#[timeout(30000)]
fn seq_only_includes_push_back() {
    assert!(is_seq_only_method("push_back"));
}

#[test]
#[timeout(30000)]
fn seq_only_includes_tail() {
    assert!(is_seq_only_method("tail"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_set() {
    // set is ambiguous between Seq and FSet
    assert!(!is_seq_only_method("set"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_index_logic() {
    // index_logic is ambiguous between Seq and FMap (#967)
    assert!(!is_seq_only_method("index_logic"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_sum() {
    // sum is excluded — user-defined ADTs can define it (#1965, #2002)
    assert!(!is_seq_only_method("sum"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_len() {
    // len (without _logic) is ambiguous
    assert!(!is_seq_only_method("len"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_into_seq() {
    // into_seq produces a Seq result but the receiver is an FMap, not a Seq.
    assert!(!is_seq_only_method("into_seq"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_contains() {
    // contains is ambiguous between Seq/FMap/FSet (#2155)
    assert!(!is_seq_only_method("contains"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_lookup() {
    // lookup is FMap-only
    assert!(!is_seq_only_method("lookup"));
}

#[test]
#[timeout(30000)]
fn seq_only_excludes_merge() {
    // merge is FMap-only
    assert!(!is_seq_only_method("merge"));
}

// --- Relationship invariants ---

#[test]
#[timeout(30000)]
fn unconditional_is_subset_of_produces_seq() {
    // Every method that produces_seq_unconditional also produces_seq
    let methods = [
        "push_back",
        "push_back_ghost",
        "push_front",
        "push_front_ghost",
        "pop_front",
        "pop_front_ghost",
        "pop_back",
        "pop_back_ghost",
        "tail",
        "reverse",
        "to_owned_seq",
        "concat",
        "subsequence",
    ];
    for m in &methods {
        assert!(
            method_produces_seq(m),
            "unconditional method {m} should also pass method_produces_seq"
        );
        assert!(
            method_produces_seq_unconditional(m),
            "{m} should pass method_produces_seq_unconditional"
        );
    }
}

#[test]
#[timeout(30000)]
fn seq_only_is_superset_of_unconditional() {
    // Every unconditional method is also seq_only
    let methods = [
        "push_back",
        "push_back_ghost",
        "push_front",
        "push_front_ghost",
        "pop_front",
        "pop_front_ghost",
        "pop_back",
        "pop_back_ghost",
        "tail",
        "reverse",
        "to_owned_seq",
        "concat",
        "subsequence",
    ];
    for m in &methods {
        assert!(
            is_seq_only_method(m),
            "unconditional method {m} should also pass is_seq_only_method"
        );
    }
}
