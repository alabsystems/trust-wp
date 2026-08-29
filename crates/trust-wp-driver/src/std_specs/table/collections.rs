// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! HashMap and HashSet specs.

use trust_wp_std::std::collections;

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // ── HashMap specs ───────────────────────────────────────────────
    (
        &[
            "std::collections::HashMap::new",
            "std::collections::hash_map::HashMap::new",
        ],
        collections::specs::HASHMAP_NEW,
    ),
    (
        &[
            "std::collections::HashMap::with_capacity",
            "std::collections::hash_map::HashMap::with_capacity",
        ],
        collections::specs::HASHMAP_WITH_CAPACITY,
    ),
    (
        &[
            "std::collections::HashMap::len",
            "std::collections::hash_map::HashMap::len",
        ],
        collections::specs::HASHMAP_LEN,
    ),
    (
        &[
            "std::collections::HashMap::is_empty",
            "std::collections::hash_map::HashMap::is_empty",
        ],
        collections::specs::HASHMAP_IS_EMPTY,
    ),
    (
        &[
            "std::collections::HashMap::insert",
            "std::collections::hash_map::HashMap::insert",
        ],
        collections::specs::HASHMAP_INSERT,
    ),
    (
        &[
            "std::collections::HashMap::remove",
            "std::collections::hash_map::HashMap::remove",
        ],
        collections::specs::HASHMAP_REMOVE,
    ),
    (
        &[
            "std::collections::HashMap::get",
            "std::collections::hash_map::HashMap::get",
        ],
        collections::specs::HASHMAP_GET,
    ),
    (
        &[
            "std::collections::HashMap::get_mut",
            "std::collections::hash_map::HashMap::get_mut",
        ],
        collections::specs::HASHMAP_GET_MUT,
    ),
    (
        &[
            "std::collections::HashMap::contains_key",
            "std::collections::hash_map::HashMap::contains_key",
        ],
        collections::specs::HASHMAP_CONTAINS_KEY,
    ),
    (
        &[
            "std::collections::HashMap::clear",
            "std::collections::hash_map::HashMap::clear",
        ],
        collections::specs::HASHMAP_CLEAR,
    ),
    (
        &[
            "std::collections::HashMap::iter",
            "std::collections::hash_map::HashMap::iter",
            "std::collections::hash::map::HashMap::iter",
        ],
        collections::specs::HASHMAP_ITER,
    ),
    (
        &[
            "std::collections::HashMap::iter_mut",
            "std::collections::hash_map::HashMap::iter_mut",
            "std::collections::hash::map::HashMap::iter_mut",
        ],
        collections::specs::HASHMAP_ITER_MUT,
    ),
    (
        &[
            "std::collections::HashMap::into_iter",
            "std::collections::hash_map::HashMap::into_iter",
            "<std::collections::HashMap as core::iter::IntoIterator>::into_iter",
            "<std::collections::HashMap as std::iter::IntoIterator>::into_iter",
            "<std::collections::hash_map::HashMap as core::iter::IntoIterator>::into_iter",
            "<std::collections::hash_map::HashMap as std::iter::IntoIterator>::into_iter",
            "<&std::collections::HashMap as core::iter::IntoIterator>::into_iter",
            "<&std::collections::HashMap as std::iter::IntoIterator>::into_iter",
            "<&std::collections::hash_map::HashMap as core::iter::IntoIterator>::into_iter",
            "<&std::collections::hash_map::HashMap as std::iter::IntoIterator>::into_iter",
        ],
        collections::specs::HASHMAP_INTO_ITER,
    ),
    (
        &[
            "<&mut std::collections::HashMap as core::iter::IntoIterator>::into_iter",
            "<&mut std::collections::HashMap as std::iter::IntoIterator>::into_iter",
            "<&mut std::collections::hash_map::HashMap as core::iter::IntoIterator>::into_iter",
            "<&mut std::collections::hash_map::HashMap as std::iter::IntoIterator>::into_iter",
        ],
        collections::specs::HASHMAP_INTO_ITER_MUT,
    ),
    // ── HashSet specs ───────────────────────────────────────────────
    (
        &[
            "std::collections::HashSet::new",
            "std::collections::hash_set::HashSet::new",
        ],
        collections::specs::HASHSET_NEW,
    ),
    (
        &[
            "std::collections::HashSet::with_capacity",
            "std::collections::hash_set::HashSet::with_capacity",
        ],
        collections::specs::HASHSET_WITH_CAPACITY,
    ),
    (
        &[
            "std::collections::HashSet::len",
            "std::collections::hash_set::HashSet::len",
        ],
        collections::specs::HASHSET_LEN,
    ),
    (
        &[
            "std::collections::HashSet::is_empty",
            "std::collections::hash_set::HashSet::is_empty",
        ],
        collections::specs::HASHSET_IS_EMPTY,
    ),
    (
        &[
            "std::collections::HashSet::insert",
            "std::collections::hash_set::HashSet::insert",
        ],
        collections::specs::HASHSET_INSERT,
    ),
    (
        &[
            "std::collections::HashSet::remove",
            "std::collections::hash_set::HashSet::remove",
        ],
        collections::specs::HASHSET_REMOVE,
    ),
    (
        &[
            "std::collections::HashSet::contains",
            "std::collections::hash_set::HashSet::contains",
        ],
        collections::specs::HASHSET_CONTAINS,
    ),
    (
        &[
            "std::collections::HashSet::clear",
            "std::collections::hash_set::HashSet::clear",
        ],
        collections::specs::HASHSET_CLEAR,
    ),
    (
        &[
            "std::collections::HashSet::iter",
            "std::collections::hash_set::HashSet::iter",
        ],
        collections::specs::HASHSET_ITER,
    ),
    (
        &[
            "std::collections::HashSet::into_iter",
            "std::collections::hash_set::HashSet::into_iter",
            "<std::collections::HashSet as core::iter::IntoIterator>::into_iter",
            "<std::collections::HashSet as std::iter::IntoIterator>::into_iter",
            "<std::collections::hash_set::HashSet as core::iter::IntoIterator>::into_iter",
            "<std::collections::hash_set::HashSet as std::iter::IntoIterator>::into_iter",
            "<&std::collections::HashSet as core::iter::IntoIterator>::into_iter",
            "<&std::collections::HashSet as std::iter::IntoIterator>::into_iter",
            "<&std::collections::hash_set::HashSet as core::iter::IntoIterator>::into_iter",
            "<&std::collections::hash_set::HashSet as std::iter::IntoIterator>::into_iter",
        ],
        collections::specs::HASHSET_INTO_ITER,
    ),
    (
        &[
            "std::collections::HashSet::intersection",
            "std::collections::hash_set::HashSet::intersection",
            "std::collections::hash::set::HashSet::intersection",
        ],
        collections::specs::HASHSET_INTERSECTION,
    ),
    (
        &[
            "std::collections::HashSet::difference",
            "std::collections::hash_set::HashSet::difference",
            "std::collections::hash::set::HashSet::difference",
        ],
        collections::specs::HASHSET_DIFFERENCE,
    ),
    // ── FromIterator::from_iter (collect) specs ─────────────────────
    // These close the roundtrip gap: into_iter ensures self@ == result@
    // (map→iter), from_iter ensures result@ == iter@ (iter→map). (#2116)
    (
        &[
            "<std::collections::HashMap as core::iter::FromIterator>::from_iter",
            "<std::collections::hash_map::HashMap as core::iter::FromIterator>::from_iter",
            "<std::collections::HashMap as std::iter::FromIterator>::from_iter",
            "<std::collections::hash_map::HashMap as std::iter::FromIterator>::from_iter",
            "<std::collections::HashMap as core::iter::traits::collect::FromIterator>::from_iter",
            "<std::collections::hash_map::HashMap as core::iter::traits::collect::FromIterator>::from_iter",
        ],
        collections::specs::HASHMAP_FROM_ITER,
    ),
    (
        &[
            "<std::collections::HashSet as core::iter::FromIterator>::from_iter",
            "<std::collections::hash_set::HashSet as core::iter::FromIterator>::from_iter",
            "<std::collections::HashSet as std::iter::FromIterator>::from_iter",
            "<std::collections::hash_set::HashSet as std::iter::FromIterator>::from_iter",
            "<std::collections::HashSet as core::iter::traits::collect::FromIterator>::from_iter",
            "<std::collections::hash_set::HashSet as core::iter::traits::collect::FromIterator>::from_iter",
        ],
        collections::specs::HASHSET_FROM_ITER,
    ),
    // ── HashMap Entry API ───────────────────────────────────────────
    (
        &[
            "std::collections::hash_map::Entry::or_insert",
            "std::collections::hash_map::entry::Entry::or_insert",
        ],
        collections::specs::HASHMAP_ENTRY_OR_INSERT,
    ),
    (
        &[
            "std::collections::hash_map::Entry::or_insert_with",
            "std::collections::hash_map::entry::Entry::or_insert_with",
        ],
        collections::specs::HASHMAP_ENTRY_OR_INSERT_WITH,
    ),
    (
        &[
            "std::collections::hash_map::Entry::or_default",
            "std::collections::hash_map::entry::Entry::or_default",
        ],
        collections::specs::HASHMAP_ENTRY_OR_DEFAULT,
    ),
    (
        &[
            "std::collections::hash_map::Entry::and_modify",
            "std::collections::hash_map::entry::Entry::and_modify",
        ],
        collections::specs::HASHMAP_ENTRY_AND_MODIFY,
    ),
    (
        &[
            "std::collections::hash_map::Entry::key",
            "std::collections::hash_map::entry::Entry::key",
        ],
        collections::specs::HASHMAP_ENTRY_KEY,
    ),
    // ── HashMap additional methods ──────────────────────────────────
    (
        &[
            "std::collections::HashMap::keys",
            "std::collections::hash_map::HashMap::keys",
        ],
        collections::specs::HASHMAP_KEYS,
    ),
    (
        &[
            "std::collections::HashMap::values",
            "std::collections::hash_map::HashMap::values",
        ],
        collections::specs::HASHMAP_VALUES,
    ),
    (
        &[
            "std::collections::HashMap::retain",
            "std::collections::hash_map::HashMap::retain",
        ],
        collections::specs::HASHMAP_RETAIN,
    ),
    (
        &[
            "std::collections::HashMap::entry",
            "std::collections::hash_map::HashMap::entry",
        ],
        collections::specs::HASHMAP_ENTRY,
    ),
    (
        &[
            "std::collections::HashMap::values_mut",
            "std::collections::hash_map::HashMap::values_mut",
        ],
        collections::specs::HASHMAP_VALUES_MUT,
    ),
    (
        &[
            "std::collections::HashMap::into_keys",
            "std::collections::hash_map::HashMap::into_keys",
        ],
        collections::specs::HASHMAP_INTO_KEYS,
    ),
    (
        &[
            "std::collections::HashMap::into_values",
            "std::collections::hash_map::HashMap::into_values",
        ],
        collections::specs::HASHMAP_INTO_VALUES,
    ),
    (
        &[
            "std::collections::HashMap::drain",
            "std::collections::hash_map::HashMap::drain",
        ],
        collections::specs::HASHMAP_DRAIN,
    ),
    (
        &[
            "<std::collections::HashMap as core::iter::Extend>::extend",
            "<std::collections::hash_map::HashMap as core::iter::Extend>::extend",
            "<std::collections::HashMap as std::iter::Extend>::extend",
            "<std::collections::hash_map::HashMap as std::iter::Extend>::extend",
            "std::collections::HashMap::extend",
            "std::collections::hash_map::HashMap::extend",
        ],
        collections::specs::HASHMAP_EXTEND,
    ),
    // ── HashSet additional methods ──────────────────────────────────
    (
        &[
            "std::collections::HashSet::retain",
            "std::collections::hash_set::HashSet::retain",
        ],
        collections::specs::HASHSET_RETAIN,
    ),
    (
        &[
            "std::collections::HashSet::union",
            "std::collections::hash_set::HashSet::union",
        ],
        collections::specs::HASHSET_UNION,
    ),
    (
        &[
            "std::collections::HashSet::is_subset",
            "std::collections::hash_set::HashSet::is_subset",
        ],
        collections::specs::HASHSET_IS_SUBSET,
    ),
    (
        &[
            "std::collections::HashSet::is_superset",
            "std::collections::hash_set::HashSet::is_superset",
        ],
        collections::specs::HASHSET_IS_SUPERSET,
    ),
    (
        &[
            "std::collections::HashSet::is_disjoint",
            "std::collections::hash_set::HashSet::is_disjoint",
        ],
        collections::specs::HASHSET_IS_DISJOINT,
    ),
    // ── HashMap Index/IndexMut trait ────────────────────────────────
    (
        &[
            "<std::collections::HashMap as core::ops::Index>::index",
            "<std::collections::HashMap as std::ops::Index>::index",
            "<std::collections::hash_map::HashMap as core::ops::Index>::index",
            "<std::collections::hash_map::HashMap as std::ops::Index>::index",
            "std::collections::HashMap::index",
            "std::collections::hash_map::HashMap::index",
        ],
        collections::specs::HASHMAP_INDEX,
    ),
    (
        &[
            "<std::collections::HashMap as core::ops::IndexMut>::index_mut",
            "<std::collections::HashMap as std::ops::IndexMut>::index_mut",
            "<std::collections::hash_map::HashMap as core::ops::IndexMut>::index_mut",
            "<std::collections::hash_map::HashMap as std::ops::IndexMut>::index_mut",
            "std::collections::HashMap::index_mut",
            "std::collections::hash_map::HashMap::index_mut",
        ],
        collections::specs::HASHMAP_INDEX_MUT,
    ),
    // ── BTreeMap specs ──────────────────────────────────────────────
    (
        &[
            "std::collections::BTreeMap::new",
            "std::collections::btree_map::BTreeMap::new",
            "alloc::collections::btree_map::BTreeMap::new",
            "alloc::collections::BTreeMap::new",
        ],
        collections::specs::BTREEMAP_NEW,
    ),
    (
        &[
            "std::collections::BTreeMap::len",
            "std::collections::btree_map::BTreeMap::len",
            "alloc::collections::btree_map::BTreeMap::len",
            "alloc::collections::BTreeMap::len",
        ],
        collections::specs::BTREEMAP_LEN,
    ),
    (
        &[
            "std::collections::BTreeMap::is_empty",
            "std::collections::btree_map::BTreeMap::is_empty",
            "alloc::collections::btree_map::BTreeMap::is_empty",
            "alloc::collections::BTreeMap::is_empty",
        ],
        collections::specs::BTREEMAP_IS_EMPTY,
    ),
    (
        &[
            "std::collections::BTreeMap::insert",
            "std::collections::btree_map::BTreeMap::insert",
            "alloc::collections::btree_map::BTreeMap::insert",
            "alloc::collections::BTreeMap::insert",
        ],
        collections::specs::BTREEMAP_INSERT,
    ),
    (
        &[
            "std::collections::BTreeMap::remove",
            "std::collections::btree_map::BTreeMap::remove",
            "alloc::collections::btree_map::BTreeMap::remove",
            "alloc::collections::BTreeMap::remove",
        ],
        collections::specs::BTREEMAP_REMOVE,
    ),
    (
        &[
            "std::collections::BTreeMap::get",
            "std::collections::btree_map::BTreeMap::get",
            "alloc::collections::btree_map::BTreeMap::get",
            "alloc::collections::BTreeMap::get",
        ],
        collections::specs::BTREEMAP_GET,
    ),
    (
        &[
            "std::collections::BTreeMap::get_mut",
            "std::collections::btree_map::BTreeMap::get_mut",
            "alloc::collections::btree_map::BTreeMap::get_mut",
            "alloc::collections::BTreeMap::get_mut",
        ],
        collections::specs::BTREEMAP_GET_MUT,
    ),
    (
        &[
            "std::collections::BTreeMap::contains_key",
            "std::collections::btree_map::BTreeMap::contains_key",
            "alloc::collections::btree_map::BTreeMap::contains_key",
            "alloc::collections::BTreeMap::contains_key",
        ],
        collections::specs::BTREEMAP_CONTAINS_KEY,
    ),
    (
        &[
            "std::collections::BTreeMap::clear",
            "std::collections::btree_map::BTreeMap::clear",
            "alloc::collections::btree_map::BTreeMap::clear",
            "alloc::collections::BTreeMap::clear",
        ],
        collections::specs::BTREEMAP_CLEAR,
    ),
    (
        &[
            "std::collections::BTreeMap::iter",
            "std::collections::btree_map::BTreeMap::iter",
            "alloc::collections::btree_map::BTreeMap::iter",
            "alloc::collections::BTreeMap::iter",
        ],
        collections::specs::BTREEMAP_ITER,
    ),
    (
        &[
            "std::collections::BTreeMap::keys",
            "std::collections::btree_map::BTreeMap::keys",
            "alloc::collections::btree_map::BTreeMap::keys",
            "alloc::collections::BTreeMap::keys",
        ],
        collections::specs::BTREEMAP_KEYS,
    ),
    (
        &[
            "std::collections::BTreeMap::values",
            "std::collections::btree_map::BTreeMap::values",
            "alloc::collections::btree_map::BTreeMap::values",
            "alloc::collections::BTreeMap::values",
        ],
        collections::specs::BTREEMAP_VALUES,
    ),
    (
        &[
            "std::collections::BTreeMap::into_iter",
            "std::collections::btree_map::BTreeMap::into_iter",
            "alloc::collections::btree_map::BTreeMap::into_iter",
            "alloc::collections::BTreeMap::into_iter",
            "<std::collections::BTreeMap as core::iter::IntoIterator>::into_iter",
            "<std::collections::BTreeMap as std::iter::IntoIterator>::into_iter",
            "<alloc::collections::btree_map::BTreeMap as core::iter::IntoIterator>::into_iter",
            "<alloc::collections::btree_map::BTreeMap as std::iter::IntoIterator>::into_iter",
            "<&std::collections::BTreeMap as core::iter::IntoIterator>::into_iter",
            "<&std::collections::BTreeMap as std::iter::IntoIterator>::into_iter",
            "<&alloc::collections::btree_map::BTreeMap as core::iter::IntoIterator>::into_iter",
            "<&alloc::collections::btree_map::BTreeMap as std::iter::IntoIterator>::into_iter",
        ],
        collections::specs::BTREEMAP_INTO_ITER,
    ),
    // ── BTreeSet specs ──────────────────────────────────────────────
    (
        &[
            "std::collections::BTreeSet::new",
            "std::collections::btree_set::BTreeSet::new",
            "alloc::collections::btree_set::BTreeSet::new",
            "alloc::collections::BTreeSet::new",
        ],
        collections::specs::BTREESET_NEW,
    ),
    (
        &[
            "std::collections::BTreeSet::len",
            "std::collections::btree_set::BTreeSet::len",
            "alloc::collections::btree_set::BTreeSet::len",
            "alloc::collections::BTreeSet::len",
        ],
        collections::specs::BTREESET_LEN,
    ),
    (
        &[
            "std::collections::BTreeSet::is_empty",
            "std::collections::btree_set::BTreeSet::is_empty",
            "alloc::collections::btree_set::BTreeSet::is_empty",
            "alloc::collections::BTreeSet::is_empty",
        ],
        collections::specs::BTREESET_IS_EMPTY,
    ),
    (
        &[
            "std::collections::BTreeSet::insert",
            "std::collections::btree_set::BTreeSet::insert",
            "alloc::collections::btree_set::BTreeSet::insert",
            "alloc::collections::BTreeSet::insert",
        ],
        collections::specs::BTREESET_INSERT,
    ),
    (
        &[
            "std::collections::BTreeSet::remove",
            "std::collections::btree_set::BTreeSet::remove",
            "alloc::collections::btree_set::BTreeSet::remove",
            "alloc::collections::BTreeSet::remove",
        ],
        collections::specs::BTREESET_REMOVE,
    ),
    (
        &[
            "std::collections::BTreeSet::contains",
            "std::collections::btree_set::BTreeSet::contains",
            "alloc::collections::btree_set::BTreeSet::contains",
            "alloc::collections::BTreeSet::contains",
        ],
        collections::specs::BTREESET_CONTAINS,
    ),
    (
        &[
            "std::collections::BTreeSet::clear",
            "std::collections::btree_set::BTreeSet::clear",
            "alloc::collections::btree_set::BTreeSet::clear",
            "alloc::collections::BTreeSet::clear",
        ],
        collections::specs::BTREESET_CLEAR,
    ),
    (
        &[
            "std::collections::BTreeSet::iter",
            "std::collections::btree_set::BTreeSet::iter",
            "alloc::collections::btree_set::BTreeSet::iter",
            "alloc::collections::BTreeSet::iter",
        ],
        collections::specs::BTREESET_ITER,
    ),
    (
        &[
            "std::collections::BTreeSet::into_iter",
            "std::collections::btree_set::BTreeSet::into_iter",
            "alloc::collections::btree_set::BTreeSet::into_iter",
            "alloc::collections::BTreeSet::into_iter",
            "<std::collections::BTreeSet as core::iter::IntoIterator>::into_iter",
            "<std::collections::BTreeSet as std::iter::IntoIterator>::into_iter",
            "<alloc::collections::btree_set::BTreeSet as core::iter::IntoIterator>::into_iter",
            "<alloc::collections::btree_set::BTreeSet as std::iter::IntoIterator>::into_iter",
            "<&std::collections::BTreeSet as core::iter::IntoIterator>::into_iter",
            "<&std::collections::BTreeSet as std::iter::IntoIterator>::into_iter",
            "<&alloc::collections::btree_set::BTreeSet as core::iter::IntoIterator>::into_iter",
            "<&alloc::collections::btree_set::BTreeSet as std::iter::IntoIterator>::into_iter",
        ],
        collections::specs::BTREESET_INTO_ITER,
    ),
    // ── BTreeMap additional methods ─────────────────────────────────
    (
        &[
            "std::collections::BTreeMap::iter_mut",
            "std::collections::btree_map::BTreeMap::iter_mut",
            "alloc::collections::btree_map::BTreeMap::iter_mut",
            "alloc::collections::BTreeMap::iter_mut",
        ],
        collections::specs::BTREEMAP_ITER_MUT,
    ),
    (
        &[
            "std::collections::BTreeMap::retain",
            "std::collections::btree_map::BTreeMap::retain",
            "alloc::collections::btree_map::BTreeMap::retain",
            "alloc::collections::BTreeMap::retain",
        ],
        collections::specs::BTREEMAP_RETAIN,
    ),
    (
        &[
            "std::collections::BTreeMap::entry",
            "std::collections::btree_map::BTreeMap::entry",
            "alloc::collections::btree_map::BTreeMap::entry",
            "alloc::collections::BTreeMap::entry",
        ],
        collections::specs::BTREEMAP_ENTRY,
    ),
    (
        &[
            "std::collections::BTreeMap::into_keys",
            "std::collections::btree_map::BTreeMap::into_keys",
            "alloc::collections::btree_map::BTreeMap::into_keys",
            "alloc::collections::BTreeMap::into_keys",
        ],
        collections::specs::BTREEMAP_INTO_KEYS,
    ),
    (
        &[
            "std::collections::BTreeMap::into_values",
            "std::collections::btree_map::BTreeMap::into_values",
            "alloc::collections::btree_map::BTreeMap::into_values",
            "alloc::collections::BTreeMap::into_values",
        ],
        collections::specs::BTREEMAP_INTO_VALUES,
    ),
    // BTreeMap FromIterator
    (
        &[
            "<std::collections::BTreeMap as core::iter::FromIterator>::from_iter",
            "<std::collections::btree_map::BTreeMap as core::iter::FromIterator>::from_iter",
            "<alloc::collections::btree_map::BTreeMap as core::iter::FromIterator>::from_iter",
            "<std::collections::BTreeMap as std::iter::FromIterator>::from_iter",
            "<alloc::collections::btree_map::BTreeMap as std::iter::FromIterator>::from_iter",
            "<std::collections::BTreeMap as core::iter::traits::collect::FromIterator>::from_iter",
            "<alloc::collections::btree_map::BTreeMap as core::iter::traits::collect::FromIterator>::from_iter",
        ],
        collections::specs::BTREEMAP_FROM_ITER,
    ),
    // ── BTreeSet additional methods ─────────────────────────────────
    (
        &[
            "std::collections::BTreeSet::retain",
            "std::collections::btree_set::BTreeSet::retain",
            "alloc::collections::btree_set::BTreeSet::retain",
            "alloc::collections::BTreeSet::retain",
        ],
        collections::specs::BTREESET_RETAIN,
    ),
    (
        &[
            "std::collections::BTreeSet::intersection",
            "std::collections::btree_set::BTreeSet::intersection",
            "alloc::collections::btree_set::BTreeSet::intersection",
            "alloc::collections::BTreeSet::intersection",
        ],
        collections::specs::BTREESET_INTERSECTION,
    ),
    (
        &[
            "std::collections::BTreeSet::difference",
            "std::collections::btree_set::BTreeSet::difference",
            "alloc::collections::btree_set::BTreeSet::difference",
            "alloc::collections::BTreeSet::difference",
        ],
        collections::specs::BTREESET_DIFFERENCE,
    ),
    (
        &[
            "std::collections::BTreeSet::union",
            "std::collections::btree_set::BTreeSet::union",
            "alloc::collections::btree_set::BTreeSet::union",
            "alloc::collections::BTreeSet::union",
        ],
        collections::specs::BTREESET_UNION,
    ),
    (
        &[
            "std::collections::BTreeSet::is_subset",
            "std::collections::btree_set::BTreeSet::is_subset",
            "alloc::collections::btree_set::BTreeSet::is_subset",
            "alloc::collections::BTreeSet::is_subset",
        ],
        collections::specs::BTREESET_IS_SUBSET,
    ),
    (
        &[
            "std::collections::BTreeSet::is_superset",
            "std::collections::btree_set::BTreeSet::is_superset",
            "alloc::collections::btree_set::BTreeSet::is_superset",
            "alloc::collections::BTreeSet::is_superset",
        ],
        collections::specs::BTREESET_IS_SUPERSET,
    ),
    (
        &[
            "std::collections::BTreeSet::is_disjoint",
            "std::collections::btree_set::BTreeSet::is_disjoint",
            "alloc::collections::btree_set::BTreeSet::is_disjoint",
            "alloc::collections::BTreeSet::is_disjoint",
        ],
        collections::specs::BTREESET_IS_DISJOINT,
    ),
    // BTreeSet FromIterator
    (
        &[
            "<std::collections::BTreeSet as core::iter::FromIterator>::from_iter",
            "<std::collections::btree_set::BTreeSet as core::iter::FromIterator>::from_iter",
            "<alloc::collections::btree_set::BTreeSet as core::iter::FromIterator>::from_iter",
            "<std::collections::BTreeSet as std::iter::FromIterator>::from_iter",
            "<alloc::collections::btree_set::BTreeSet as std::iter::FromIterator>::from_iter",
            "<std::collections::BTreeSet as core::iter::traits::collect::FromIterator>::from_iter",
            "<alloc::collections::btree_set::BTreeSet as core::iter::traits::collect::FromIterator>::from_iter",
        ],
        collections::specs::BTREESET_FROM_ITER,
    ),
    // ── HashSet extend ─────────────────────────────────────────────
    (
        &[
            "<std::collections::HashSet as core::iter::Extend>::extend",
            "<std::collections::hash_set::HashSet as core::iter::Extend>::extend",
            "<std::collections::HashSet as std::iter::Extend>::extend",
            "<std::collections::hash_set::HashSet as std::iter::Extend>::extend",
            "std::collections::HashSet::extend",
            "std::collections::hash_set::HashSet::extend",
        ],
        collections::specs::HASHSET_EXTEND,
    ),
    // ── BTreeMap Entry API ─────────────────────────────────────────
    (
        &[
            "std::collections::btree_map::Entry::or_insert",
            "alloc::collections::btree_map::entry::Entry::or_insert",
            "std::collections::btree_map::entry::Entry::or_insert",
        ],
        collections::specs::BTREEMAP_ENTRY_OR_INSERT,
    ),
    (
        &[
            "std::collections::btree_map::Entry::or_insert_with",
            "alloc::collections::btree_map::entry::Entry::or_insert_with",
            "std::collections::btree_map::entry::Entry::or_insert_with",
        ],
        collections::specs::BTREEMAP_ENTRY_OR_INSERT_WITH,
    ),
    (
        &[
            "std::collections::btree_map::Entry::or_default",
            "alloc::collections::btree_map::entry::Entry::or_default",
            "std::collections::btree_map::entry::Entry::or_default",
        ],
        collections::specs::BTREEMAP_ENTRY_OR_DEFAULT,
    ),
    (
        &[
            "std::collections::btree_map::Entry::and_modify",
            "alloc::collections::btree_map::entry::Entry::and_modify",
            "std::collections::btree_map::entry::Entry::and_modify",
        ],
        collections::specs::BTREEMAP_ENTRY_AND_MODIFY,
    ),
    (
        &[
            "std::collections::btree_map::Entry::key",
            "alloc::collections::btree_map::entry::Entry::key",
            "std::collections::btree_map::entry::Entry::key",
        ],
        collections::specs::BTREEMAP_ENTRY_KEY,
    ),
    // ── BTreeMap::values_mut ───────────────────────────────────────
    (
        &[
            "std::collections::BTreeMap::values_mut",
            "std::collections::btree_map::BTreeMap::values_mut",
            "alloc::collections::btree_map::BTreeMap::values_mut",
            "alloc::collections::BTreeMap::values_mut",
        ],
        collections::specs::BTREEMAP_VALUES_MUT,
    ),
    // ── VecDeque specs ─────────────────────────────────────────────
    (
        &[
            "std::collections::VecDeque::new",
            "std::collections::vec_deque::VecDeque::new",
            "alloc::collections::vec_deque::VecDeque::new",
            "alloc::collections::VecDeque::new",
        ],
        collections::specs::VECDEQUE_NEW,
    ),
    (
        &[
            "std::collections::VecDeque::with_capacity",
            "std::collections::vec_deque::VecDeque::with_capacity",
            "alloc::collections::vec_deque::VecDeque::with_capacity",
            "alloc::collections::VecDeque::with_capacity",
        ],
        collections::specs::VECDEQUE_WITH_CAPACITY,
    ),
    (
        &[
            "std::collections::VecDeque::len",
            "std::collections::vec_deque::VecDeque::len",
            "alloc::collections::vec_deque::VecDeque::len",
            "alloc::collections::VecDeque::len",
        ],
        collections::specs::VECDEQUE_LEN,
    ),
    (
        &[
            "std::collections::VecDeque::is_empty",
            "std::collections::vec_deque::VecDeque::is_empty",
            "alloc::collections::vec_deque::VecDeque::is_empty",
            "alloc::collections::VecDeque::is_empty",
        ],
        collections::specs::VECDEQUE_IS_EMPTY,
    ),
    (
        &[
            "std::collections::VecDeque::push_back",
            "std::collections::vec_deque::VecDeque::push_back",
            "alloc::collections::vec_deque::VecDeque::push_back",
            "alloc::collections::VecDeque::push_back",
        ],
        collections::specs::VECDEQUE_PUSH_BACK,
    ),
    (
        &[
            "std::collections::VecDeque::push_front",
            "std::collections::vec_deque::VecDeque::push_front",
            "alloc::collections::vec_deque::VecDeque::push_front",
            "alloc::collections::VecDeque::push_front",
        ],
        collections::specs::VECDEQUE_PUSH_FRONT,
    ),
    (
        &[
            "std::collections::VecDeque::pop_back",
            "std::collections::vec_deque::VecDeque::pop_back",
            "alloc::collections::vec_deque::VecDeque::pop_back",
            "alloc::collections::VecDeque::pop_back",
        ],
        collections::specs::VECDEQUE_POP_BACK,
    ),
    (
        &[
            "std::collections::VecDeque::pop_front",
            "std::collections::vec_deque::VecDeque::pop_front",
            "alloc::collections::vec_deque::VecDeque::pop_front",
            "alloc::collections::VecDeque::pop_front",
        ],
        collections::specs::VECDEQUE_POP_FRONT,
    ),
    (
        &[
            "std::collections::VecDeque::clear",
            "std::collections::vec_deque::VecDeque::clear",
            "alloc::collections::vec_deque::VecDeque::clear",
            "alloc::collections::VecDeque::clear",
        ],
        collections::specs::VECDEQUE_CLEAR,
    ),
    (
        &[
            "std::collections::VecDeque::contains",
            "std::collections::vec_deque::VecDeque::contains",
            "alloc::collections::vec_deque::VecDeque::contains",
            "alloc::collections::VecDeque::contains",
        ],
        collections::specs::VECDEQUE_CONTAINS,
    ),
    (
        &[
            "std::collections::VecDeque::get",
            "std::collections::vec_deque::VecDeque::get",
            "alloc::collections::vec_deque::VecDeque::get",
            "alloc::collections::VecDeque::get",
        ],
        collections::specs::VECDEQUE_GET,
    ),
    (
        &[
            "std::collections::VecDeque::iter",
            "std::collections::vec_deque::VecDeque::iter",
            "alloc::collections::vec_deque::VecDeque::iter",
            "alloc::collections::VecDeque::iter",
        ],
        collections::specs::VECDEQUE_ITER,
    ),
    (
        &[
            "std::collections::VecDeque::into_iter",
            "std::collections::vec_deque::VecDeque::into_iter",
            "alloc::collections::vec_deque::VecDeque::into_iter",
            "alloc::collections::VecDeque::into_iter",
            "<std::collections::VecDeque as core::iter::IntoIterator>::into_iter",
            "<std::collections::VecDeque as std::iter::IntoIterator>::into_iter",
            "<alloc::collections::vec_deque::VecDeque as core::iter::IntoIterator>::into_iter",
            "<alloc::collections::vec_deque::VecDeque as std::iter::IntoIterator>::into_iter",
        ],
        collections::specs::VECDEQUE_INTO_ITER,
    ),
    (
        &[
            "std::collections::VecDeque::drain",
            "std::collections::vec_deque::VecDeque::drain",
            "alloc::collections::vec_deque::VecDeque::drain",
            "alloc::collections::VecDeque::drain",
        ],
        collections::specs::VECDEQUE_DRAIN,
    ),
];
