// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Iterator std-spec lookup tests.

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
fn test_lookup_vec_into_iter() {
    let spec = lookup_std_spec("<alloc::vec::Vec as core::iter::IntoIterator>::into_iter").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@.ext_eq(self@)", "Vec::into_iter");
    assert_param_names(&spec, &["self"], "Vec::into_iter");
}

#[test]
fn test_lookup_iterator_next_std_path() {
    let spec = lookup_std_spec("std::iter::traits::iterator::Iterator::next").unwrap();
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("produces"));
}

#[test]
fn test_lookup_vec_into_iter_all_paths() {
    // All known aliases for Vec::into_iter must resolve to the same spec
    let paths = &[
        "alloc::vec::Vec::into_iter",
        "std::vec::Vec::into_iter",
        "<alloc::vec::Vec as core::iter::IntoIterator>::into_iter",
        "<std::vec::Vec as core::iter::IntoIterator>::into_iter",
        "<alloc::vec::Vec as std::iter::IntoIterator>::into_iter",
        "<std::vec::Vec as std::iter::IntoIterator>::into_iter",
    ];
    for path in paths {
        let spec = lookup_std_spec(path);
        assert!(spec.is_some(), "Vec::into_iter path not found: {path}");
        assert_ensures_contains(spec.as_ref().unwrap(), "result@.ext_eq(self@)", path);
        assert_param_names(spec.as_ref().unwrap(), &["self"], path);
    }
}

#[test]
fn test_lookup_iterator_fuse() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::fuse").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::fuse");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_cloned() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::cloned").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::cloned");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_copied() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::copied").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::copied");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_plain_aliases() {
    for path in &[
        "core::iter::Iterator::copied",
        "std::iter::Iterator::copied",
        "core::iter::Iterator::filter",
        "std::iter::Iterator::filter",
        "core::iter::Iterator::filter_map",
        "std::iter::Iterator::filter_map",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("plain Iterator alias should resolve: {path}"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result.iter() == self")),
            "{path} should preserve the wrapped iterator state"
        );
    }
}

#[test]
fn test_lookup_iterator_skip() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::skip").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::skip");
    assert_ensures_contains(&spec, "result.n() == n", "Iterator::skip");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_take() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::take").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::take");
    assert_ensures_contains(&spec, "result.n() == n", "Iterator::take");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_enumerate() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::enumerate").unwrap();
    assert_eq!(spec.requires.len(), 2);
    assert_requires_contains(&spec, "(*i).completed()", "Iterator::enumerate");
    assert_requires_contains(&spec, "core::usize::MAX@", "Iterator::enumerate");
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::enumerate");
    assert_ensures_contains(&spec, "result.n()@ == 0", "Iterator::enumerate");
    assert!(spec.requires.iter().all(|r| parse_spec(r).is_some()));
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_zip() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::zip").unwrap();
    assert_eq!(spec.requires.len(), 1);
    assert_requires_contains(&spec, "U::into_iter.precondition", "Iterator::zip");
    assert_ensures_contains(&spec, "result.itera() == self", "Iterator::zip");
    assert_ensures_contains(
        &spec,
        "U::into_iter.postcondition((other,), result.iterb())",
        "Iterator::zip",
    );
    assert!(spec.requires.iter().all(|r| parse_spec(r).is_some()));
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_rev() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::rev").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::rev");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

// -- IterMut UFCS Iterator::next paths (#2238) --

#[test]
fn test_lookup_iter_mut_ufcs_next() {
    // Post-borrowck MIR may resolve to the concrete IterMut impl of Iterator::next
    // rather than the generic trait method.
    for path in &[
        "<core::slice::iter::IterMut<'_, i32> as core::iter::Iterator>::next",
        "<std::slice::IterMut<'_, u8> as std::iter::Iterator>::next",
    ] {
        let spec = lookup_std_spec(path);
        assert!(spec.is_some(), "IterMut UFCS next path not found: {path}");
        let spec = spec.unwrap();
        assert!(
            spec.ensures[0].contains("produces"),
            "IterMut next spec should reference produces: {path}"
        );
    }
}

#[test]
fn test_lookup_slice_iter_ufcs_next() {
    // Shared slice::Iter UFCS paths for Iterator::next.
    for path in &[
        "<core::slice::iter::Iter<'_, i32> as core::iter::Iterator>::next",
        "<std::slice::Iter<'_, u8> as std::iter::Iterator>::next",
    ] {
        let spec = lookup_std_spec(path);
        assert!(spec.is_some(), "Iter UFCS next path not found: {path}");
        let spec = spec.unwrap();
        assert!(
            spec.ensures[0].contains("produces"),
            "Iter next spec should reference produces: {path}"
        );
    }
}

#[test]
fn test_lookup_into_iter_ufcs_next() {
    // Vec IntoIter UFCS paths for Iterator::next.
    for path in &[
        "<alloc::vec::into_iter::IntoIter<i32> as core::iter::Iterator>::next",
        "<std::vec::IntoIter<u8> as std::iter::Iterator>::next",
    ] {
        let spec = lookup_std_spec(path);
        assert!(spec.is_some(), "IntoIter UFCS next path not found: {path}");
        let spec = spec.unwrap();
        assert!(
            spec.ensures[0].contains("produces"),
            "IntoIter next spec should reference produces: {path}"
        );
    }
}

// -- &mut Vec / &mut [T] IntoIterator paths (#2238) --

#[test]
fn test_lookup_mut_ref_vec_into_iter() {
    // `for x in &mut vec {}` desugars to <&mut Vec as IntoIterator>::into_iter.
    for path in &[
        "<&mut alloc::vec::Vec<i32> as core::iter::IntoIterator>::into_iter",
        "<&mut std::vec::Vec<u8> as std::iter::IntoIterator>::into_iter",
    ] {
        let spec = lookup_std_spec(path);
        assert!(
            spec.is_some(),
            "&mut Vec IntoIterator path not found: {path}"
        );
        let spec = spec.unwrap();
        assert!(
            spec.ensures.iter().any(|e| e.contains("completed")),
            "&mut Vec into_iter spec should seed completed state: {path}"
        );
    }
}

#[test]
fn test_lookup_mut_ref_slice_into_iter() {
    // `for x in &mut slice {}` desugars to <&mut [T] as IntoIterator>::into_iter.
    // MIR preserves the generic `[T]` form (not concrete `[i32]`).
    for path in &[
        "<&mut [T] as core::iter::IntoIterator>::into_iter",
        "<&mut [T] as std::iter::IntoIterator>::into_iter",
    ] {
        let spec = lookup_std_spec(path);
        assert!(
            spec.is_some(),
            "&mut [T] IntoIterator path not found: {path}"
        );
        let spec = spec.unwrap();
        assert!(
            spec.ensures.iter().any(|e| e.contains("completed")),
            "&mut [T] into_iter spec should seed completed state: {path}"
        );
    }
}

// -- Map / Filter / FilterMap constructor specs (#2170) --

#[test]
fn test_lookup_iterator_map() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::map").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::map");
    assert_ensures_contains(&spec, "result.func() == f", "Iterator::map");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_map_std_path() {
    let spec = lookup_std_spec("std::iter::traits::iterator::Iterator::map").unwrap();
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::map (std)");
    assert_ensures_contains(&spec, "result.func() == f", "Iterator::map (std)");
}

#[test]
fn test_lookup_iterator_filter() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::filter").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::filter");
    assert_ensures_contains(&spec, "result.func() == f", "Iterator::filter");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_filter_std_path() {
    let spec = lookup_std_spec("std::iter::traits::iterator::Iterator::filter").unwrap();
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::filter (std)");
    assert_ensures_contains(&spec, "result.func() == f", "Iterator::filter (std)");
}

#[test]
fn test_lookup_iterator_filter_map() {
    let spec = lookup_std_spec("core::iter::traits::iterator::Iterator::filter_map").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::filter_map");
    assert_ensures_contains(&spec, "result.func() == f", "Iterator::filter_map");
    assert!(spec.ensures.iter().all(|e| parse_spec(e).is_some()));
}

#[test]
fn test_lookup_iterator_filter_map_std_path() {
    let spec = lookup_std_spec("std::iter::traits::iterator::Iterator::filter_map").unwrap();
    assert_ensures_contains(&spec, "result.iter() == self", "Iterator::filter_map (std)");
    assert_ensures_contains(&spec, "result.func() == f", "Iterator::filter_map (std)");
}

// -- &Vec / &[T] IntoIterator paths --

#[test]
fn test_lookup_ref_vec_into_iter() {
    // `for x in &vec {}` desugars to <&Vec as IntoIterator>::into_iter.
    for path in &[
        "<&alloc::vec::Vec<i32> as core::iter::IntoIterator>::into_iter",
        "<&std::vec::Vec<u8> as std::iter::IntoIterator>::into_iter",
    ] {
        let spec = lookup_std_spec(path);
        assert!(spec.is_some(), "&Vec IntoIterator path not found: {path}");
        let spec = spec.unwrap();
        assert!(
            spec.ensures.iter().any(|e| e.contains("completed")),
            "&Vec into_iter spec should seed completed state: {path}"
        );
    }
}

#[test]
fn test_lookup_ref_slice_into_iter() {
    // `for x in &slice {}` desugars to <&[T] as IntoIterator>::into_iter.
    // MIR preserves the generic `[T]` form (not concrete `[i32]`).
    for path in &[
        "<&[T] as core::iter::IntoIterator>::into_iter",
        "<&[T] as std::iter::IntoIterator>::into_iter",
    ] {
        let spec = lookup_std_spec(path);
        assert!(spec.is_some(), "&[T] IntoIterator path not found: {path}");
        let spec = spec.unwrap();
        assert!(
            spec.ensures.iter().any(|e| e.contains("completed")),
            "&[T] into_iter spec should seed completed state: {path}"
        );
    }
}
