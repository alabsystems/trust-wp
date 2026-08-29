// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

mod get_or_declare_var;

// normalize_sort coverage through get_or_declare_var
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_rust_vec_to_seq() {
    // Sort::Uninterpreted("std::vec::Vec") should be normalized to
    // Sort::Seq(Int) by normalize_sort. (#1965, #2080)
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("v", Sort::Uninterpreted("std::vec::Vec".to_string()));
    assert!(first.is_ok(), "Vec normalization should succeed");

    // The sort should be normalized to Seq
    assert_eq!(
        encoder.var_sort("v"),
        Some(&Sort::seq(Sort::Int)),
        "std::vec::Vec should be normalized to Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_duration_to_int() {
    // Sort::Uninterpreted("std::time::Duration") is an Int-model type —
    // canonical_sort classifies it as CanonicalSort::Int. (#1965)
    let mut encoder = AYEncoder::new();

    let first =
        encoder.get_or_declare_var("d", Sort::Uninterpreted("std::time::Duration".to_string()));
    assert!(first.is_ok(), "Duration normalization should succeed");

    // Duration models as integer (time in nanoseconds), so it normalizes to Int.
    assert_eq!(
        encoder.var_sort("d"),
        Some(&Sort::Int),
        "std::time::Duration should be normalized to Int (Int-model type)"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_qualified_user_type_to_bare() {
    // Sort::Uninterpreted("my_crate::MyStruct") with module path should have
    // the path stripped to the bare type name ("MyStruct") by normalize_sort,
    // since it's not a recognized canonical sort (Seq, FMap, Int, etc.).
    let mut encoder = AYEncoder::new();

    let first =
        encoder.get_or_declare_var("s", Sort::Uninterpreted("my_crate::MyStruct".to_string()));
    assert!(first.is_ok(), "MyStruct normalization should succeed");

    // Module path stripped to bare name
    assert_eq!(
        encoder.var_sort("s"),
        Some(&Sort::Uninterpreted("MyStruct".to_string())),
        "my_crate::MyStruct should be normalized to bare MyStruct"
    );
}
