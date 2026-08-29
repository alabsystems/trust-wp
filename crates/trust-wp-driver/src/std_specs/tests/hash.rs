// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Hash/Hasher/BuildHasher trait spec lookup.

use super::super::*;

#[test]
fn test_hash_hash_spec_lookup() {
    let spec = lookup_std_spec("core::hash::Hash::hash").unwrap();
    assert!(!spec.ensures.is_empty(), "Hash::hash should have ensures");
    assert!(
        spec.ensures[0].contains("Hash::hash.postcondition"),
        "Hash::hash should use postcondition predicate, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_hash_hash_std_path() {
    let spec = lookup_std_spec("std::hash::Hash::hash").unwrap();
    assert!(!spec.ensures.is_empty());
}

#[test]
fn test_hash_slice_spec_lookup() {
    let spec = lookup_std_spec("core::hash::Hash::hash_slice").unwrap();
    assert!(!spec.ensures.is_empty());
    assert!(
        spec.ensures[0].contains("hash_slice"),
        "Hash::hash_slice should reference hash_slice, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_hasher_finish_spec_lookup() {
    let spec = lookup_std_spec("core::hash::Hasher::finish").unwrap();
    assert!(!spec.ensures.is_empty());
    assert!(spec.ensures[0].contains("finish"));
}

#[test]
fn test_hasher_write_spec_lookup() {
    let spec = lookup_std_spec("core::hash::Hasher::write").unwrap();
    assert!(!spec.ensures.is_empty());
}

#[test]
fn test_hasher_write_usize_spec_lookup() {
    let spec = lookup_std_spec("core::hash::Hasher::write_usize").unwrap();
    assert!(!spec.ensures.is_empty());
    assert!(spec.ensures[0].contains("write_usize"));
}

#[test]
fn test_build_hasher_spec_lookup() {
    let spec = lookup_std_spec("core::hash::BuildHasher::build_hasher").unwrap();
    assert!(!spec.ensures.is_empty());
    assert!(spec.ensures[0].contains("build_hasher"));
}

#[test]
fn test_hasher_write_typed_variants() {
    // All typed write methods should be registered
    for method in &[
        "write_u8",
        "write_u16",
        "write_u32",
        "write_u64",
        "write_i8",
        "write_i16",
        "write_i32",
        "write_i64",
        "write_usize",
        "write_isize",
    ] {
        let path = format!("core::hash::Hasher::{method}");
        let spec = lookup_std_spec(&path);
        assert!(spec.is_some(), "Hasher::{method} should have a spec entry");
    }
}
