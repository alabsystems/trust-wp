// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    super::{parse_spec, *},
    helpers::*,
};

#[test]
fn test_lookup_iterator_next() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::next").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("self.completed()"));
    assert!(spec.ensures[0].contains("produces"));
    assert!(parse_spec(&spec.ensures[0]).is_some());
}

#[test]
fn test_lookup_vec_iter() {
    let spec = lookup_std_spec("alloc::vec::Vec::<i32>::iter").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    assert!(spec.ensures.iter().any(|e| e.contains("result@")));
    assert!(spec
        .ensures
        .iter()
        .any(|e| e.contains("result.completed()")));
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_vec_iter_mut() {
    let spec = lookup_std_spec("std::vec::Vec::<i32>::iter_mut").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    assert!(spec.ensures.iter().any(|e| e.contains("result@")));
    assert!(spec
        .ensures
        .iter()
        .any(|e| e.contains("result.completed()")));
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_slice_iter_aliases_vec_iter_spec() {
    let from_vec = lookup_std_spec("alloc::vec::Vec::<u8>::iter").unwrap();
    let from_slice = lookup_std_spec("core::slice::<impl [u8]>::iter").unwrap();
    assert_eq!(from_vec.requires, from_slice.requires);
    assert_eq!(from_vec.ensures, from_slice.ensures);
}

#[test]
fn test_lookup_slice_iter_mut_aliases_vec_iter_mut_spec() {
    let from_vec = lookup_std_spec("alloc::vec::Vec::<u8>::iter_mut").unwrap();
    let from_slice = lookup_std_spec("std::slice::<impl [u8]>::iter_mut").unwrap();
    assert_eq!(from_vec.requires, from_slice.requires);
    assert_eq!(from_vec.ensures, from_slice.ensures);
}

#[test]
fn test_lookup_slice_first() {
    let spec = lookup_std_spec("core::slice::<impl [T]>::first").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(v) => self@.len() > 0 && *v == self@.index_logic(0)",
        "[T]::first",
    );
}

#[test]
fn test_lookup_slice_first_std_alias() {
    let spec = lookup_std_spec("std::slice::<impl [T]>::first").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(v) => self@.len() > 0 && *v == self@.index_logic(0)",
        "[T]::first std alias",
    );
}

#[test]
fn test_lookup_slice_first_bare_alias() {
    let spec = lookup_std_spec("core::slice::first").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(v) => self@.len() > 0 && *v == self@.index_logic(0)",
        "[T]::first bare alias",
    );
}

#[test]
fn test_lookup_slice_first_std_bare_alias() {
    let spec = lookup_std_spec("std::slice::first").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(v) => self@.len() > 0 && *v == self@.index_logic(0)",
        "[T]::first std bare alias",
    );
}

#[test]
fn test_lookup_slice_last() {
    let spec = lookup_std_spec("std::slice::<impl [T]>::last").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(v) => self@.len() > 0 && *v == self@[self@.len() - 1]",
        "[T]::last",
    );
}

#[test]
fn test_lookup_slice_get() {
    let spec = lookup_std_spec("core::slice::<impl [T]>::get").unwrap();
    assert!(spec.requires.is_empty());
    assert_param_names(&spec, &["self", "ix"], "[T]::get");
    assert_ensures_contains(
        &spec,
        "ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)",
        "[T]::get",
    );
    assert_ensures_contains(&spec, "!ix.in_bounds(self@) ==> result == None", "[T]::get");
}

#[test]
fn test_lookup_slice_get_mut() {
    let spec = lookup_std_spec("core::slice::<impl [T]>::get_mut").unwrap();
    assert!(spec.requires.is_empty());
    assert_param_names(&spec, &["self", "ix"], "[T]::get_mut");
    assert_ensures_contains(
        &spec,
        "ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)",
        "[T]::get_mut",
    );
    assert_ensures_contains(&spec, "ix.has_value((^self)@, ^result)", "[T]::get_mut");
    assert_ensures_contains(
        &spec,
        "ix.resolve_elsewhere(self@, (^self)@)",
        "[T]::get_mut",
    );
}

#[test]
fn test_slice_len_spec_content() {
    let spec = lookup_std_spec("core::slice::len").unwrap();
    assert!(
        spec.requires.is_empty(),
        "slice::len should have no requires"
    );
    assert_eq!(spec.ensures.len(), 1);
    assert!(
        spec.ensures[0].contains("self@.len()"),
        "slice::len ensures should relate result to self@.len(), got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_slice_is_empty_spec_content() {
    let spec = lookup_std_spec("core::slice::is_empty").unwrap();
    assert!(
        spec.requires.is_empty(),
        "slice::is_empty should have no requires"
    );
    assert_eq!(spec.ensures.len(), 1);
    assert!(
        spec.ensures[0].contains("self@.len() == 0"),
        "slice::is_empty ensures should check self@.len() == 0, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_slice_contains_spec_content() {
    let spec = lookup_std_spec("core::slice::contains").unwrap();
    assert!(
        spec.requires.is_empty(),
        "slice::contains should have no requires"
    );
    assert_eq!(spec.ensures.len(), 1);
    assert!(
        spec.ensures[0].contains("exists"),
        "slice::contains ensures should use existential quantifier, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_slice_binary_search_spec_content() {
    let spec = lookup_std_spec("core::slice::binary_search").unwrap();
    assert!(
        spec.requires.is_empty(),
        "slice::binary_search should have no requires"
    );
    assert_eq!(spec.ensures.len(), 1);
    assert!(
        spec.ensures[0].contains("Ok(i)") && spec.ensures[0].contains("Err(i)"),
        "slice::binary_search ensures should handle Ok and Err cases, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_lookup_slice_binary_search_std_aliases_core_spec() {
    let from_core = lookup_std_spec("core::slice::<impl [T]>::binary_search").unwrap();
    let from_std = lookup_std_spec("std::slice::<impl [T]>::binary_search")
        .expect("std::slice binary_search path should resolve");
    assert_eq!(from_core.requires, from_std.requires);
    assert_eq!(from_core.ensures, from_std.ensures);
}

#[test]
fn test_lookup_slice_index() {
    let spec = lookup_std_spec("core::slice::index").expect("slice index spec should exist");
    assert_param_names(&spec, &["self", "ix"], "[T]::index");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "[T]::index");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "[T]::index");
}

#[test]
fn test_lookup_slice_index_trait_qualified() {
    let spec = lookup_std_spec("<[T] as core::ops::Index>::index")
        .expect("trait-qualified slice Index path should match");
    assert_param_names(&spec, &["self", "ix"], "[T]::index trait");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "[T]::index trait");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "[T]::index trait");
}

#[test]
fn test_lookup_slice_index_mut() {
    let spec =
        lookup_std_spec("core::slice::index_mut").expect("slice index_mut spec should exist");
    assert_param_names(&spec, &["self", "ix"], "[T]::index_mut");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "[T]::index_mut");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "[T]::index_mut");
    assert_ensures_contains(&spec, "ix.has_value((^self)@, ^result)", "[T]::index_mut");
    assert_ensures_contains(
        &spec,
        "ix.resolve_elsewhere(self@, (^self)@)",
        "[T]::index_mut",
    );
}

#[test]
fn test_lookup_slice_index_mut_trait_qualified() {
    let spec = lookup_std_spec("<[T] as core::ops::IndexMut>::index_mut")
        .expect("trait-qualified slice IndexMut path should match (#1374)");
    assert_param_names(&spec, &["self", "ix"], "[T]::index_mut trait");
    assert_requires_contains(&spec, "ix.in_bounds(self@)", "[T]::index_mut trait");
    assert_ensures_contains(&spec, "ix.has_value(self@, result)", "[T]::index_mut trait");
    assert_ensures_contains(
        &spec,
        "ix.has_value((^self)@, ^result)",
        "[T]::index_mut trait",
    );
    assert_ensures_contains(
        &spec,
        "ix.resolve_elsewhere(self@, (^self)@)",
        "[T]::index_mut trait",
    );
}

// ── FMap additional specs (#967) ────────────────────────────────
