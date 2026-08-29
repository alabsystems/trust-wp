// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::encoder::closure_sorts`] pure free functions.
//!
//! Coverage gap: `closure_sorts.rs` (327 LOC) has zero `#[cfg(test)]` blocks.
//! The two pure free functions `closure_symbol_suffix` and `closure_env_sort_name`
//! are tested here; the remaining functions are AYEncoder methods requiring solver
//! state and are covered indirectly by closure integration tests.

use ay_dpll::api::{DatatypeConstructor, DatatypeSort, Sort};
use ntest::timeout;

use crate::encoder::closure_sorts::{closure_env_sort_name, closure_symbol_suffix};

// --- closure_symbol_suffix ---

#[test]
#[timeout(30000)]
fn suffix_is_16_hex_chars() {
    let suffix = closure_symbol_suffix("test::my_closure");
    assert_eq!(suffix.len(), 16, "FNV-1a hash should be 16 hex chars");
    assert!(
        suffix.chars().all(|c| c.is_ascii_hexdigit()),
        "suffix should be hex: {suffix}"
    );
}

#[test]
#[timeout(30000)]
fn suffix_deterministic() {
    let a = closure_symbol_suffix("my::closure::def_id");
    let b = closure_symbol_suffix("my::closure::def_id");
    assert_eq!(a, b, "same input should produce same hash");
}

#[test]
#[timeout(30000)]
fn suffix_different_inputs_different_hashes() {
    let a = closure_symbol_suffix("closure_a");
    let b = closure_symbol_suffix("closure_b");
    assert_ne!(a, b, "different inputs should produce different hashes");
}

#[test]
#[timeout(30000)]
fn suffix_empty_string() {
    let suffix = closure_symbol_suffix("");
    assert_eq!(suffix.len(), 16);
    assert!(suffix.chars().all(|c| c.is_ascii_hexdigit()));
}

#[test]
#[timeout(30000)]
fn suffix_unicode_input() {
    let suffix = closure_symbol_suffix("test::closure_αβγ");
    assert_eq!(suffix.len(), 16);
    assert!(suffix.chars().all(|c| c.is_ascii_hexdigit()));
}

#[test]
#[timeout(30000)]
fn suffix_long_path() {
    let long = "a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::closure_123456";
    let suffix = closure_symbol_suffix(long);
    assert_eq!(suffix.len(), 16);
}

#[test]
#[timeout(30000)]
fn suffix_avoids_punctuation() {
    // The point of hashing is to avoid leaking punctuation into SMT symbols
    let suffix = closure_symbol_suffix("foo::bar<T>::{closure#0}");
    assert!(
        suffix.chars().all(|c| c.is_ascii_hexdigit()),
        "should contain no punctuation: {suffix}"
    );
}

// --- closure_env_sort_name ---

#[test]
#[timeout(30000)]
fn sort_name_from_uninterpreted_closure() {
    let sort = Sort::Uninterpreted("ClosureEnv_abc123".to_string());
    assert_eq!(closure_env_sort_name(&sort), Some("ClosureEnv_abc123"));
}

#[test]
#[timeout(30000)]
fn sort_name_from_datatype_closure() {
    let dt = DatatypeSort::new(
        "ClosureEnv_def456".to_string(),
        vec![DatatypeConstructor::new(
            "mk_closure_env_def456".to_string(),
            vec![],
        )],
    );
    let sort = Sort::Datatype(dt);
    assert_eq!(closure_env_sort_name(&sort), Some("ClosureEnv_def456"));
}

#[test]
#[timeout(30000)]
fn sort_name_none_for_int() {
    assert_eq!(closure_env_sort_name(&Sort::Int), None);
}

#[test]
#[timeout(30000)]
fn sort_name_none_for_bool() {
    assert_eq!(closure_env_sort_name(&Sort::Bool), None);
}

#[test]
#[timeout(30000)]
fn sort_name_none_for_non_closure_uninterpreted() {
    let sort = Sort::Uninterpreted("MyEnum".to_string());
    assert_eq!(closure_env_sort_name(&sort), None);
}

#[test]
#[timeout(30000)]
fn sort_name_none_for_non_closure_datatype() {
    let dt = DatatypeSort::new(
        "OptionInt".to_string(),
        vec![DatatypeConstructor::new("None".to_string(), vec![])],
    );
    let sort = Sort::Datatype(dt);
    assert_eq!(closure_env_sort_name(&sort), None);
}

#[test]
#[timeout(30000)]
fn sort_name_none_for_partial_prefix() {
    // "Closure" without "Env_" should not match
    let sort = Sort::Uninterpreted("ClosureStruct_abc".to_string());
    assert_eq!(closure_env_sort_name(&sort), None);
}

#[test]
#[timeout(30000)]
fn sort_name_exact_prefix_boundary() {
    // "ClosureEnv_" with empty suffix is still a valid match
    let sort = Sort::Uninterpreted("ClosureEnv_".to_string());
    assert_eq!(closure_env_sort_name(&sort), Some("ClosureEnv_"));
}

// --- Integration: suffix -> sort name round-trip ---

#[test]
#[timeout(30000)]
fn suffix_round_trip_through_uninterpreted_sort() {
    let def_id = "my_crate::my_fn::{closure#0}";
    let suffix = closure_symbol_suffix(def_id);
    let sort_name = format!("ClosureEnv_{suffix}");
    let sort = Sort::Uninterpreted(sort_name.clone());
    assert_eq!(closure_env_sort_name(&sort), Some(sort_name.as_str()));
}

#[test]
#[timeout(30000)]
fn suffix_round_trip_through_datatype_sort() {
    let def_id = "another::closure::def";
    let suffix = closure_symbol_suffix(def_id);
    let sort_name = format!("ClosureEnv_{suffix}");
    let dt = DatatypeSort::new(
        sort_name.clone(),
        vec![DatatypeConstructor::new(
            format!("mk_closure_env_{suffix}"),
            vec![],
        )],
    );
    let sort = Sort::Datatype(dt);
    assert_eq!(closure_env_sort_name(&sort), Some(sort_name.as_str()));
}
