// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[test]
fn test_normalize_path() {
    assert_eq!(
        normalize_path("core::option::Option::<i32>::unwrap"),
        "core::option::Option::unwrap"
    );
    assert_eq!(
        normalize_path("std::vec::Vec::<T>::push"),
        "std::vec::Vec::push"
    );
    assert_eq!(
        normalize_path("std::result::Result::<T, E>::unwrap"),
        "std::result::Result::unwrap"
    );
}

#[test]
fn test_normalize_path_nested_generics() {
    // Test nested generic parameters like HashMap<K, Vec<V>>
    assert_eq!(
        normalize_path("std::collections::HashMap::<String, Vec<i32>>::new"),
        "std::collections::HashMap::new"
    );
    // Test deeply nested generics
    assert_eq!(normalize_path("Foo::<Bar<Baz<T>>>::method"), "Foo::method");
}

#[test]
fn test_normalize_path_slice_impl() {
    assert_eq!(
        normalize_path("core::slice::<impl [T]>::first"),
        "core::slice::<impl [T]>::first"
    );
    assert_eq!(
        normalize_path("std::slice::<impl [T]>::binary_search"),
        "core::slice::<impl [T]>::binary_search"
    );
    assert_eq!(
        normalize_path("core::slice::<impl [u8]>::iter"),
        "core::slice::<impl [T]>::iter"
    );
    assert_eq!(
        normalize_path("std::slice::<impl [i32]>::iter_mut"),
        "core::slice::<impl [T]>::iter_mut"
    );
}

#[test]
fn test_normalize_path_specialized_inherent_impl_collapses_to_module_method() {
    assert_eq!(
        normalize_path("trust_wp_std::ghost::invariant::<impl Ghost<NonAtomicInvariant<P>>>::open"),
        "trust_wp_std::ghost::invariant::open"
    );
}

#[test]
fn test_normalize_path_internal_logic_prefix() {
    assert_eq!(
        normalize_path("logic::seq::Seq::push_back_ghost"),
        "trust_wp_std::logic::seq::Seq::push_back_ghost"
    );
}

#[test]
fn test_normalize_path_trait_qualified_internal_logic_prefix() {
    assert_eq!(
        normalize_path("<logic::seq::Seq<T> as core::ops::Index>::index"),
        "<trust_wp_std::logic::seq::Seq as core::ops::Index>::index"
    );
}
#[test]
fn test_normalize_path_trait_qualified_duration_add() {
    assert_eq!(
        normalize_path("<core::time::Duration as core::ops::Add>::add"),
        "<core::time::Duration as core::ops::Add>::add"
    );
}

#[test]
fn test_normalize_path_trait_qualified_duration_sub() {
    assert_eq!(
        normalize_path("<core::time::Duration as core::ops::Sub>::sub"),
        "<core::time::Duration as core::ops::Sub>::sub"
    );
}

#[test]
fn test_normalize_path_trait_qualified_instant_add() {
    assert_eq!(
        normalize_path("<std::time::Instant as core::ops::Add>::add"),
        "<std::time::Instant as core::ops::Add>::add"
    );
}

#[test]
fn test_normalize_path_trait_qualified_with_std_prefix() {
    // std::ops is normalized to core::ops so UFCS paths from MIR match
    // the STD_SPECS table which uses core:: paths canonically. (#967)
    assert_eq!(
        normalize_path("<std::time::Duration as std::ops::Add>::add"),
        "<std::time::Duration as core::ops::Add>::add"
    );
}

#[test]
fn test_normalize_path_trait_qualified_still_strips_inner_generics() {
    // Trait-qualified path with generic params inside the type should strip
    // the generics but preserve the trait qualification.
    assert_eq!(
        normalize_path("<alloc::vec::Vec<T> as core::ops::Index>::index"),
        "<alloc::vec::Vec as core::ops::Index>::index"
    );
    assert_eq!(
        normalize_path("<std::slice::Iter<'_, u8> as std::iter::Iterator>::next"),
        "<core::slice::Iter as std::iter::Iterator>::next"
    );
}

#[test]
fn test_normalize_path_non_trait_generic_still_stripped() {
    // Non-trait-qualified paths with generics should still be stripped.
    assert_eq!(
        normalize_path("core::option::Option::<i32>::unwrap"),
        "core::option::Option::unwrap"
    );
}

#[test]
fn test_normalize_path_internal_submodule_seq_core_push_back_ghost() {
    // MIR def_path for inherent impl in private `core` submodule (#2326):
    // `trust_wp_std::logic::seq::core::<impl Seq<T>>::push_back_ghost`
    // After generic stripping → `trust_wp_std::logic::seq::core::push_back_ghost`
    // INTERNAL_SUBMODULES rewrites → `trust_wp_std::logic::seq::Seq::push_back_ghost`
    assert_eq!(
        normalize_path("trust_wp_std::logic::seq::core::<impl Seq<T>>::push_back_ghost"),
        "trust_wp_std::logic::seq::Seq::push_back_ghost"
    );
}

#[test]
fn test_normalize_path_internal_submodule_seq_core_len_ghost() {
    assert_eq!(
        normalize_path("trust_wp_std::logic::seq::core::<impl Seq<T>>::len_ghost"),
        "trust_wp_std::logic::seq::Seq::len_ghost"
    );
}

#[test]
fn test_normalize_path_internal_submodule_fmap_core() {
    assert_eq!(
        normalize_path("trust_wp_std::logic::fmap::core::<impl FMap<K, V>>::get"),
        "trust_wp_std::logic::fmap::FMap::get"
    );
}

#[test]
fn test_normalize_path_internal_submodule_ghost_core() {
    assert_eq!(
        normalize_path("trust_wp_std::ghost::core::<impl Ghost<T>>::new"),
        "trust_wp_std::ghost::Ghost::new"
    );
}
