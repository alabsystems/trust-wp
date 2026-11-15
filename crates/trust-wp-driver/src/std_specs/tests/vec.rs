// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_vec_push() {
    let spec = lookup_std_spec("alloc::vec::Vec::<i32>::push").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("push_back")),
        "Vec::push ensures must reference push_back: {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_vec_new() {
    let spec = lookup_std_spec("alloc::vec::Vec::new").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@.len() == 0", "Vec::new");
}

#[test]
fn test_lookup_vec_len() {
    let spec = lookup_std_spec("alloc::vec::Vec::<i32>::len").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("len()")),
        "Vec::len ensures must reference len(): {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_vec_is_empty() {
    let spec = lookup_std_spec("std::vec::Vec::<String>::is_empty").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("len()")),
        "Vec::is_empty ensures must reference len(): {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_vec_pop() {
    let spec = lookup_std_spec("alloc::vec::Vec::<i32>::pop").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("match")),
        "Vec::pop ensures must use match (Some/None cases): {:?}",
        spec.ensures
    );
    assert!(
        spec.ensures.iter().any(|e| e.contains("push_back")),
        "Vec::pop ensures must reference push_back (inverse of push): {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_vec_clear() {
    let spec = lookup_std_spec("std::vec::Vec::clear").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("len()")),
        "Vec::clear ensures must reference len(): {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_vec_first() {
    let spec = lookup_std_spec("alloc::vec::Vec::first").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(r) => self@.len() > 0 && *r == self@[0]",
        "Vec::first",
    );
}

#[test]
fn test_lookup_vec_last() {
    let spec = lookup_std_spec("std::vec::Vec::last").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "Some(r) => self@.len() > 0 && *r == self@[self@.len() - 1]",
        "Vec::last",
    );
}

#[test]
fn test_lookup_vec_get() {
    let spec = lookup_std_spec("alloc::vec::Vec::get").unwrap();
    assert!(spec.requires.is_empty());
    assert_param_names(&spec, &["self", "ix"], "Vec::get");
    assert_ensures_contains(
        &spec,
        "ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)",
        "Vec::get",
    );
    assert_ensures_contains(&spec, "!ix.in_bounds(self@) ==> result == None", "Vec::get");
}

#[test]
fn test_lookup_vec_get_mut() {
    let spec = lookup_std_spec("alloc::vec::Vec::get_mut").unwrap();
    assert!(spec.requires.is_empty());
    assert_param_names(&spec, &["self", "ix"], "Vec::get_mut");
    assert_ensures_contains(
        &spec,
        "ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)",
        "Vec::get_mut",
    );
    assert_ensures_contains(&spec, "ix.has_value((^self)@, ^result)", "Vec::get_mut");
    assert_ensures_contains(
        &spec,
        "ix.resolve_elsewhere(self@, (^self)@)",
        "Vec::get_mut",
    );
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
fn test_lookup_vec_capacity() {
    let spec = lookup_std_spec("std::vec::Vec::capacity").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@ >= self@.len()", "Vec::capacity");
}

#[test]
fn test_lookup_vec_reserve() {
    let spec = lookup_std_spec("alloc::vec::Vec::reserve").unwrap();
    assert_requires_contains(
        &spec,
        "2 * (self@.len() + additional@ - 1) * __trust_wp_std_site_size_of_T() <= isize::MAX@",
        "Vec::reserve",
    );
    assert_ensures_contains(&spec, "(^self)@ == self@", "Vec::reserve");
    assert_ensures_contains(&spec, "(^self)@.len() == self@.len()", "Vec::reserve");
    assert_ensures_contains(
        &spec,
        "(^self)@.index_logic(i) == self@.index_logic(i)",
        "Vec::reserve",
    );
    assert_ensures_contains(
        &spec,
        "(^self).capacity()@ >= self@.len() + additional@",
        "Vec::reserve",
    );
}

#[test]
fn test_lookup_vec_reserve_exact() {
    let spec = lookup_std_spec("alloc::vec::Vec::reserve_exact").unwrap();
    assert_requires_contains(
        &spec,
        "(self@.len() + additional@) * __trust_wp_std_site_size_of_T() <= isize::MAX@",
        "Vec::reserve_exact",
    );
    assert_ensures_contains(&spec, "(^self)@ == self@", "Vec::reserve_exact");
    assert_ensures_contains(&spec, "(^self)@.len() == self@.len()", "Vec::reserve_exact");
    assert_ensures_contains(
        &spec,
        "(^self)@.index_logic(i) == self@.index_logic(i)",
        "Vec::reserve_exact",
    );
    assert_ensures_contains(
        &spec,
        "(^self).capacity()@ >= self@.len() + additional@",
        "Vec::reserve_exact",
    );
}

#[test]
fn test_lookup_vec_with_capacity() {
    let spec = lookup_std_spec("std::vec::Vec::with_capacity").unwrap();
    assert_requires_contains(
        &spec,
        "capacity@ * __trust_wp_std_site_size_of_T() <= isize::MAX@",
        "Vec::with_capacity",
    );
    assert_ensures_contains(&spec, "result@.len() == 0", "Vec::with_capacity");
    assert_ensures_contains(
        &spec,
        "result.capacity()@ >= capacity@",
        "Vec::with_capacity",
    );
}

#[test]
fn test_lookup_vec_truncate() {
    let spec = lookup_std_spec("alloc::vec::Vec::truncate").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "if len@ < self@.len()", "Vec::truncate");
    assert_ensures_contains(&spec, "(^self)@ == self@", "Vec::truncate");
}

#[test]
fn test_lookup_vec_insert() {
    let spec = lookup_std_spec("std::vec::Vec::insert").unwrap();
    assert_requires_contains(&spec, "index@ <= self@.len()", "Vec::insert");
    assert_ensures_contains(
        &spec,
        "(^self)@.index_logic(index@) == element",
        "Vec::insert",
    );
}

#[test]
fn test_lookup_vec_remove() {
    let spec = lookup_std_spec("alloc::vec::Vec::remove").unwrap();
    assert_requires_contains(&spec, "index@ < self@.len()", "Vec::remove");
    assert_ensures_contains(&spec, "result == self@.index_logic(index@)", "Vec::remove");
}

#[test]
fn test_lookup_vec_shrink_to() {
    let spec = lookup_std_spec("alloc::vec::Vec::shrink_to").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self)@ == self@", "Vec::shrink_to");
    assert_ensures_contains(&spec, "(^self)@.len() == self@.len()", "Vec::shrink_to");
    assert_ensures_contains(
        &spec,
        "(^self)@.index_logic(i) == self@.index_logic(i)",
        "Vec::shrink_to",
    );
    assert_ensures_contains(
        &spec,
        "(^self).capacity()@ >= (^self)@.len()",
        "Vec::shrink_to",
    );
}

// String tests

/// A drain panics on a range out of order or past the length, which no clause
/// reads off a `RangeBounds`; the call site discharges the refusal for `..`.
#[test]
fn test_lookup_drain_is_refused_but_for_the_full_range() {
    for path in [
        "alloc::vec::Vec::drain",
        "std::collections::VecDeque::drain",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should have a spec"));
        assert_eq!(
            spec.requires,
            ["__trust_wp_std_site_unmodelled_panic_unless_full_range_R()"],
            "{path} refuses every range but `..`"
        );
    }
}
