// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_ops_deref() {
    let core_spec = lookup_std_spec("core::ops::Deref::deref").unwrap();
    let std_spec = lookup_std_spec("std::ops::Deref::deref").unwrap();

    assert_eq!(core_spec.requires, std_spec.requires);
    assert_eq!(core_spec.ensures, std_spec.ensures);
    assert_eq!(core_spec.param_names, std_spec.param_names);
    assert_eq!(core_spec.requires.len(), 1);
    assert_eq!(core_spec.ensures.len(), 1);
    assert_param_names(&core_spec, &["self"], "Deref::deref");
    assert!(core_spec.requires[0].contains("deref.precondition"));
    assert!(core_spec.ensures[0].contains("deref.postcondition"));
}

#[test]
fn test_lookup_ops_deref_mut() {
    let core_spec = lookup_std_spec("core::ops::DerefMut::deref_mut").unwrap();
    let std_spec = lookup_std_spec("std::ops::DerefMut::deref_mut").unwrap();

    assert_eq!(core_spec.requires, std_spec.requires);
    assert_eq!(core_spec.ensures, std_spec.ensures);
    assert_eq!(core_spec.param_names, std_spec.param_names);
    assert_eq!(core_spec.requires.len(), 1);
    assert_eq!(core_spec.ensures.len(), 1);
    assert_param_names(&core_spec, &["self"], "DerefMut::deref_mut");
    assert!(core_spec.requires[0].contains("deref_mut.precondition"));
    assert!(core_spec.ensures[0].contains("deref_mut.postcondition"));
}

// Fn/FnMut/FnOnce closure call specs (#1062)

#[test]
fn test_lookup_fn_call() {
    let core_spec = lookup_std_spec("core::ops::Fn::call").unwrap();
    let std_spec = lookup_std_spec("std::ops::Fn::call").unwrap();

    assert_eq!(core_spec.requires, std_spec.requires);
    assert_eq!(core_spec.ensures, std_spec.ensures);
    assert_eq!(core_spec.requires.len(), 1);
    assert_eq!(core_spec.ensures.len(), 1);
    assert!(
        core_spec.requires[0].contains("precondition"),
        "Fn::call requires should reference precondition, got: {}",
        core_spec.requires[0]
    );
    assert!(
        core_spec.ensures[0].contains("postcondition"),
        "Fn::call ensures should reference postcondition, got: {}",
        core_spec.ensures[0]
    );
}

#[test]
fn test_lookup_fn_once_call_once() {
    let core_spec = lookup_std_spec("core::ops::FnOnce::call_once").unwrap();
    let std_spec = lookup_std_spec("std::ops::FnOnce::call_once").unwrap();

    assert_eq!(core_spec.requires, std_spec.requires);
    assert_eq!(core_spec.ensures, std_spec.ensures);
    assert_eq!(core_spec.requires.len(), 1);
    assert_eq!(core_spec.ensures.len(), 1);
    assert!(
        core_spec.requires[0].contains("precondition"),
        "FnOnce::call_once requires should reference precondition, got: {}",
        core_spec.requires[0]
    );
    assert!(
        core_spec.ensures[0].contains("postcondition_once"),
        "FnOnce::call_once ensures should reference postcondition_once, got: {}",
        core_spec.ensures[0]
    );
}

#[test]
fn test_lookup_fn_mut_call_mut() {
    let core_spec = lookup_std_spec("core::ops::FnMut::call_mut").unwrap();
    let std_spec = lookup_std_spec("std::ops::FnMut::call_mut").unwrap();

    assert_eq!(core_spec.requires, std_spec.requires);
    assert_eq!(core_spec.ensures, std_spec.ensures);
    assert_eq!(core_spec.requires.len(), 1);
    assert_eq!(core_spec.ensures.len(), 1);
    assert!(
        core_spec.requires[0].contains("precondition"),
        "FnMut::call_mut requires should reference precondition, got: {}",
        core_spec.requires[0]
    );
    assert!(
        core_spec.ensures[0].contains("postcondition_mut"),
        "FnMut::call_mut ensures should reference postcondition_mut, got: {}",
        core_spec.ensures[0]
    );
}

// Slice spec content tests (#1062)

#[test]
fn test_generic_index_trait_has_postcondition_fallback() {
    // Generic Index::index now has a trait-level fallback with postcondition
    // predicate, so type-specific behavior is still handled correctly. (#2689)
    let spec = lookup_std_spec("core::ops::Index::index")
        .expect("generic Index::index should have trait fallback spec");
    assert!(
        spec.ensures[0].contains("index.postcondition"),
        "generic Index should use postcondition predicate, got: {}",
        spec.ensures[0]
    );
    let std_spec = lookup_std_spec("std::ops::Index::index")
        .expect("generic std Index::index should have trait fallback spec");
    assert!(
        std_spec.ensures[0].contains("index.postcondition"),
        "generic std Index should use postcondition predicate, got: {}",
        std_spec.ensures[0]
    );
}

#[test]
fn test_generic_index_mut_trait_has_postcondition_fallback() {
    // Generic IndexMut::index_mut now has a trait-level fallback. (#2689)
    let spec = lookup_std_spec("core::ops::IndexMut::index_mut")
        .expect("generic IndexMut::index_mut should have trait fallback spec");
    assert!(
        spec.ensures[0].contains("index_mut.postcondition"),
        "generic IndexMut should use postcondition predicate, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_vec_index_concrete_paths_still_work() {
    let spec =
        lookup_std_spec("alloc::vec::Vec::index").expect("concrete Vec::index path should match");
    assert_param_names(&spec, &["self", "ix"], "Vec::index");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "Vec::index");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "Vec::index");
}

#[test]
fn test_vec_index_trait_qualified_path_works() {
    let spec = lookup_std_spec("<alloc::vec::Vec as core::ops::Index>::index")
        .expect("trait-qualified Vec Index path should match");
    assert_param_names(&spec, &["self", "ix"], "Vec::index trait");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "Vec::index trait");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "Vec::index trait");
}

#[test]
fn test_vec_index_mut_trait_qualified_path_works() {
    let spec = lookup_std_spec("<alloc::vec::Vec as core::ops::IndexMut>::index_mut")
        .expect("trait-qualified Vec IndexMut path should match");
    assert_param_names(&spec, &["self", "ix"], "Vec::index_mut trait");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "Vec::index_mut trait");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "Vec::index_mut trait");
    assert_ensures_contains(
        &spec,
        "ix.has_value((^self)@, ^result)",
        "Vec::index_mut trait",
    );
    assert_ensures_contains(
        &spec,
        "ix.resolve_elsewhere(self@, (^self)@)",
        "Vec::index_mut trait",
    );
}
