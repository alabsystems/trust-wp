// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_hashmap_new() {
    let spec =
        lookup_std_spec("std::collections::HashMap::new").expect("HashMap::new spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@.len() == 0", "HashMap::new");
}

#[test]
fn test_lookup_hashmap_insert() {
    let spec = lookup_std_spec("std::collections::HashMap::insert")
        .expect("HashMap::insert spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self)@.lookup(k) == v", "HashMap::insert");
    assert_ensures_contains(&spec, "match result", "HashMap::insert");
}

#[test]
fn test_lookup_hashmap_get() {
    let spec =
        lookup_std_spec("std::collections::HashMap::get").expect("HashMap::get spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Some(v) => self@.contains(*k)", "HashMap::get");
    assert_ensures_contains(&spec, "None => !self@.contains(*k)", "HashMap::get");
}

#[test]
fn test_lookup_hashmap_contains_key() {
    let spec = lookup_std_spec("std::collections::HashMap::contains_key")
        .expect("HashMap::contains_key spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == self@.contains(*k)",
        "HashMap::contains_key",
    );
}

#[test]
fn test_lookup_hashmap_remove() {
    let spec = lookup_std_spec("std::collections::HashMap::remove")
        .expect("HashMap::remove spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "!(^self)@.contains(*k)", "HashMap::remove");
    assert_ensures_contains(&spec, "match result", "HashMap::remove");
}

#[test]
fn test_lookup_hashmap_len() {
    let spec =
        lookup_std_spec("std::collections::HashMap::len").expect("HashMap::len spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@ == self@.len()", "HashMap::len");
}

#[test]
fn test_lookup_hashmap_clear() {
    let spec = lookup_std_spec("std::collections::HashMap::clear")
        .expect("HashMap::clear spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self)@.len() == 0", "HashMap::clear");
}

#[test]
fn test_lookup_hashmap_with_capacity() {
    let spec = lookup_std_spec("std::collections::HashMap::with_capacity")
        .expect("HashMap::with_capacity spec should exist");
    assert_requires_contains(
        &spec,
        "(3 * capacity@ + 16) * (__trust_wp_std_site_size_of_K_V() + 1)",
        "HashMap::with_capacity",
    );
    assert_ensures_contains(&spec, "result@.len() == 0", "HashMap::with_capacity");
}

#[test]
fn test_lookup_hashmap_is_empty() {
    let spec = lookup_std_spec("std::collections::HashMap::is_empty")
        .expect("HashMap::is_empty spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == (self@.len() == 0)", "HashMap::is_empty");
}

#[test]
fn test_lookup_hashmap_get_mut() {
    let spec = lookup_std_spec("std::collections::HashMap::get_mut")
        .expect("HashMap::get_mut spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Some(v) => self@.contains(*k)", "HashMap::get_mut");
    assert_ensures_contains(&spec, "None => !self@.contains(*k)", "HashMap::get_mut");
}

#[test]
fn test_lookup_hashmap_iter() {
    let spec = lookup_std_spec("std::collections::HashMap::iter")
        .expect("HashMap::iter spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@ == result@", "HashMap::iter");
}

#[test]
fn test_lookup_hashmap_iter_mut() {
    let spec = lookup_std_spec("std::collections::HashMap::iter_mut")
        .expect("HashMap::iter_mut spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "self@.contains(k) == (^self)@.contains(k)",
        "HashMap::iter_mut",
    );
    // Prophecy-threading clause needed for `roundtrip_hashmap_iter_mut`
    // (`tests/should_succeed/cc/collections.rs`). Mirrors Creusot's
    // `(*self)@[k] == *result@[k] && (^self)@[k] == ^result@[k]`.
    assert_ensures_contains(
        &spec,
        "^result@[k] == (^self)@[k]",
        "HashMap::iter_mut prophecy",
    );
    assert!(
        spec.ensures
            .iter()
            .all(|e| crate::std_specs::parse_spec(e).is_some()),
        "HashMap::iter_mut ensures clauses should all parse: {:?}",
        spec.ensures,
    );
}

#[test]
fn test_lookup_hashmap_into_iter() {
    let spec = lookup_std_spec("std::collections::HashMap::into_iter")
        .expect("HashMap::into_iter spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@ == result@", "HashMap::into_iter");
}

#[test]
fn test_lookup_hashmap_into_iter_ufcs() {
    let spec =
        lookup_std_spec("<std::collections::HashMap as core::iter::IntoIterator>::into_iter")
            .expect("HashMap IntoIterator::into_iter UFCS spec should exist");
    assert_ensures_contains(&spec, "self@ == result@", "HashMap IntoIterator UFCS");
}

#[test]
fn test_lookup_hashmap_into_iter_mut() {
    let spec =
        lookup_std_spec("<&mut std::collections::HashMap as core::iter::IntoIterator>::into_iter")
            .expect("&mut HashMap IntoIterator::into_iter spec should exist");
    assert_ensures_contains(
        &spec,
        "(*self)@.contains(k) == (^self)@.contains(k)",
        "&mut HashMap into_iter",
    );
}

// ── HashSet specs (#967) ────────────────────────────────────────

#[test]
fn test_lookup_hashset_new() {
    let spec =
        lookup_std_spec("std::collections::HashSet::new").expect("HashSet::new spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@.len() == 0", "HashSet::new");
}

#[test]
fn test_lookup_hashset_insert() {
    let spec = lookup_std_spec("std::collections::HashSet::insert")
        .expect("HashSet::insert spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == !self@.contains(value)", "HashSet::insert");
    assert_ensures_contains(&spec, "(^self)@.contains(value)", "HashSet::insert");
}

#[test]
fn test_lookup_hashset_contains() {
    let spec = lookup_std_spec("std::collections::HashSet::contains")
        .expect("HashSet::contains spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == self@.contains(*value)",
        "HashSet::contains",
    );
}

#[test]
fn test_lookup_hashset_remove() {
    let spec = lookup_std_spec("std::collections::HashSet::remove")
        .expect("HashSet::remove spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == self@.contains(*value)", "HashSet::remove");
    assert_ensures_contains(&spec, "!(^self)@.contains(*value)", "HashSet::remove");
}

#[test]
fn test_lookup_hashset_len() {
    let spec =
        lookup_std_spec("std::collections::HashSet::len").expect("HashSet::len spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@ == self@.len()", "HashSet::len");
}

#[test]
fn test_lookup_hashset_with_capacity() {
    let spec = lookup_std_spec("std::collections::HashSet::with_capacity")
        .expect("HashSet::with_capacity spec should exist");
    assert_requires_contains(
        &spec,
        "(3 * capacity@ + 16) * (__trust_wp_std_site_size_of_T() + 1)",
        "HashSet::with_capacity",
    );
    assert_ensures_contains(&spec, "result@.len() == 0", "HashSet::with_capacity");
}

#[test]
fn test_lookup_hashset_is_empty() {
    let spec = lookup_std_spec("std::collections::HashSet::is_empty")
        .expect("HashSet::is_empty spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == (self@.len() == 0)", "HashSet::is_empty");
}

#[test]
fn test_lookup_hashset_clear() {
    let spec = lookup_std_spec("std::collections::HashSet::clear")
        .expect("HashSet::clear spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self)@.len() == 0", "HashSet::clear");
}

#[test]
fn test_lookup_hashset_iter() {
    let spec = lookup_std_spec("std::collections::HashSet::iter")
        .expect("HashSet::iter spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@ == result@", "HashSet::iter");
}

#[test]
fn test_lookup_hashset_into_iter() {
    let spec = lookup_std_spec("std::collections::HashSet::into_iter")
        .expect("HashSet::into_iter spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@ == result@", "HashSet::into_iter");
}

#[test]
fn test_lookup_hashset_into_iter_ufcs() {
    let spec =
        lookup_std_spec("<std::collections::HashSet as core::iter::IntoIterator>::into_iter")
            .expect("HashSet IntoIterator::into_iter UFCS spec should exist");
    assert_ensures_contains(&spec, "self@ == result@", "HashSet IntoIterator UFCS");
}

#[test]
fn test_lookup_hashset_intersection() {
    let spec = lookup_std_spec("std::collections::HashSet::intersection")
        .expect("HashSet::intersection spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@.intersection(other@)", "HashSet::intersection");
}

#[test]
fn test_lookup_hashset_difference() {
    let spec = lookup_std_spec("std::collections::HashSet::difference")
        .expect("HashSet::difference spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@.difference(other@)", "HashSet::difference");
}

#[test]
fn test_lookup_hashmap_from_iter() {
    let spec =
        lookup_std_spec("<std::collections::HashMap as core::iter::FromIterator>::from_iter")
            .expect("HashMap FromIterator::from_iter spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.from_iter_post(iter@)", "HashMap::from_iter");
}

#[test]
fn test_lookup_hashset_from_iter() {
    let spec =
        lookup_std_spec("<std::collections::HashSet as core::iter::FromIterator>::from_iter")
            .expect("HashSet FromIterator::from_iter spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@ == iter@", "HashSet::from_iter");
}

#[test]
fn test_lookup_hashmap_hash_map_alias() {
    // Verify the internal module alias also resolves
    let spec = lookup_std_spec("std::collections::hash_map::HashMap::new")
        .expect("hash_map::HashMap::new alias should resolve");
    assert_ensures_contains(&spec, "result@.len() == 0", "hash_map::HashMap::new alias");
}

#[test]
fn test_lookup_hashset_hash_set_alias() {
    // Verify the internal module alias also resolves
    let spec = lookup_std_spec("std::collections::hash_set::HashSet::new")
        .expect("hash_set::HashSet::new alias should resolve");
    assert_ensures_contains(&spec, "result@.len() == 0", "hash_set::HashSet::new alias");
}
