// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared std-spec path authority for `trust-wp-std`.
//!
//! This module centralizes std-spec *path ownership* (canonical paths + lookup
//! aliases + spec string references) so the driver imports metadata instead of
//! maintaining independent alias arrays.
//!
//! See: `designs/2026-03-19-2524-std-spec-path-authority-unification.md`
//! Issue: #2524

use super::{clone, default, mem, primitives, ptr, slice};

/// A spec lookup entry: all lookup paths (canonical first) and the spec string.
///
/// This matches the driver's `SpecEntry` type alias
/// `(&'static [&'static str], &'static str)` so the driver can reference
/// these slices directly in `STD_SPEC_TABLES`.
pub type SpecLookupEntry = (&'static [&'static str], &'static str);

// ── Mem / Clone / Default domain ────────────────────────────────────────────

/// Mem, clone, and default spec entries.
///
/// These entries consolidate the path metadata previously split between
/// `trust-wp-driver/src/std_specs/table/mem_clone_default.rs` (alias arrays)
/// and `trust-wp-std/src/std/builtin_registry.rs` (extern bridge entries).
///
/// Entries whose canonical path (first element) appears in
/// `BUILTIN_EXTERN_SPECS` have `builtin_extern_canonical_path()` return
/// `Some(...)` so the driver can source alias coverage from here instead
/// of from independent `expand_builtin_path_aliases()`.
pub static MEM_CLONE_DEFAULT: &[SpecLookupEntry] = &[
    // mem specs
    (
        &["core::mem::replace", "std::mem::replace"],
        mem::specs::REPLACE,
    ),
    (&["core::mem::swap", "std::mem::swap"], mem::specs::SWAP),
    (&["core::mem::take", "std::mem::take"], mem::specs::TAKE),
    // Clone for primitive types — result == *self (#1672)
    (
        &[
            "<bool as core::clone::Clone>::clone",
            "<bool as std::clone::Clone>::clone",
            "bool::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<i8 as core::clone::Clone>::clone",
            "<i8 as std::clone::Clone>::clone",
            "i8::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<i16 as core::clone::Clone>::clone",
            "<i16 as std::clone::Clone>::clone",
            "i16::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<i32 as core::clone::Clone>::clone",
            "<i32 as std::clone::Clone>::clone",
            "i32::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<i64 as core::clone::Clone>::clone",
            "<i64 as std::clone::Clone>::clone",
            "i64::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<i128 as core::clone::Clone>::clone",
            "<i128 as std::clone::Clone>::clone",
            "i128::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<isize as core::clone::Clone>::clone",
            "<isize as std::clone::Clone>::clone",
            "isize::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<u8 as core::clone::Clone>::clone",
            "<u8 as std::clone::Clone>::clone",
            "u8::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<u16 as core::clone::Clone>::clone",
            "<u16 as std::clone::Clone>::clone",
            "u16::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<u32 as core::clone::Clone>::clone",
            "<u32 as std::clone::Clone>::clone",
            "u32::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<u64 as core::clone::Clone>::clone",
            "<u64 as std::clone::Clone>::clone",
            "u64::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<u128 as core::clone::Clone>::clone",
            "<u128 as std::clone::Clone>::clone",
            "u128::clone",
        ],
        primitives::specs::CLONE,
    ),
    (
        &[
            "<usize as core::clone::Clone>::clone",
            "<usize as std::clone::Clone>::clone",
            "usize::clone",
        ],
        primitives::specs::CLONE,
    ),
    // Generic Clone::clone() fallback (#1296)
    (
        &["core::clone::Clone::clone", "std::clone::Clone::clone"],
        clone::specs::POSTCONDITION_ONLY,
    ),
    // Default for primitive types (#1672)
    (
        &[
            "<bool as core::default::Default>::default",
            "<bool as std::default::Default>::default",
            "bool::default",
        ],
        default::specs::FALSE,
    ),
    (
        &[
            "<i8 as core::default::Default>::default",
            "<i8 as std::default::Default>::default",
            "i8::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<i16 as core::default::Default>::default",
            "<i16 as std::default::Default>::default",
            "i16::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<i32 as core::default::Default>::default",
            "<i32 as std::default::Default>::default",
            "i32::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<i64 as core::default::Default>::default",
            "<i64 as std::default::Default>::default",
            "i64::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<i128 as core::default::Default>::default",
            "<i128 as std::default::Default>::default",
            "i128::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<isize as core::default::Default>::default",
            "<isize as std::default::Default>::default",
            "isize::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<u8 as core::default::Default>::default",
            "<u8 as std::default::Default>::default",
            "u8::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<u16 as core::default::Default>::default",
            "<u16 as std::default::Default>::default",
            "u16::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<u32 as core::default::Default>::default",
            "<u32 as std::default::Default>::default",
            "u32::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<u64 as core::default::Default>::default",
            "<u64 as std::default::Default>::default",
            "u64::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<u128 as core::default::Default>::default",
            "<u128 as std::default::Default>::default",
            "u128::default",
        ],
        default::specs::ZERO,
    ),
    (
        &[
            "<usize as core::default::Default>::default",
            "<usize as std::default::Default>::default",
            "usize::default",
        ],
        default::specs::ZERO,
    ),
    // Default for collection/wrapper types — concrete postconditions (#2256)
    //
    // These MUST appear before the generic fallback so first-match precedence
    // gives the solver a usable clause instead of the uninterpreted predicate.
    // MIR UFCS paths after normalize_path: `<alloc::vec::Vec as core::default::Default>::default`.
    (
        &[
            "<alloc::vec::Vec as core::default::Default>::default",
            "<std::vec::Vec as core::default::Default>::default",
            "<alloc::vec::Vec as std::default::Default>::default",
            "<std::vec::Vec as std::default::Default>::default",
        ],
        default::specs::VEC_EMPTY,
    ),
    (
        &[
            "<alloc::string::String as core::default::Default>::default",
            "<std::string::String as core::default::Default>::default",
            "<alloc::string::String as std::default::Default>::default",
            "<std::string::String as std::default::Default>::default",
        ],
        default::specs::STRING_EMPTY,
    ),
    (
        &[
            "<core::option::Option as core::default::Default>::default",
            "<std::option::Option as core::default::Default>::default",
            "<core::option::Option as std::default::Default>::default",
            "<std::option::Option as std::default::Default>::default",
        ],
        default::specs::OPTION_NONE,
    ),
    (
        &[
            "<std::collections::HashMap as core::default::Default>::default",
            "<std::collections::hash_map::HashMap as core::default::Default>::default",
            "<std::collections::HashMap as std::default::Default>::default",
            "<std::collections::hash_map::HashMap as std::default::Default>::default",
        ],
        default::specs::HASHMAP_EMPTY,
    ),
    (
        &[
            "<std::collections::HashSet as core::default::Default>::default",
            "<std::collections::hash_set::HashSet as core::default::Default>::default",
            "<std::collections::HashSet as std::default::Default>::default",
            "<std::collections::hash_set::HashSet as std::default::Default>::default",
        ],
        default::specs::HASHSET_EMPTY,
    ),
    (
        &[
            "<std::collections::BTreeMap as core::default::Default>::default",
            "<std::collections::btree_map::BTreeMap as core::default::Default>::default",
            "<alloc::collections::btree_map::BTreeMap as core::default::Default>::default",
            "<std::collections::BTreeMap as std::default::Default>::default",
            "<alloc::collections::btree_map::BTreeMap as std::default::Default>::default",
        ],
        default::specs::BTREEMAP_EMPTY,
    ),
    (
        &[
            "<std::collections::BTreeSet as core::default::Default>::default",
            "<std::collections::btree_set::BTreeSet as core::default::Default>::default",
            "<alloc::collections::btree_set::BTreeSet as core::default::Default>::default",
            "<std::collections::BTreeSet as std::default::Default>::default",
            "<alloc::collections::btree_set::BTreeSet as std::default::Default>::default",
        ],
        default::specs::BTREESET_EMPTY,
    ),
    (
        &[
            "<std::collections::VecDeque as core::default::Default>::default",
            "<std::collections::vec_deque::VecDeque as core::default::Default>::default",
            "<alloc::collections::vec_deque::VecDeque as core::default::Default>::default",
            "<std::collections::VecDeque as std::default::Default>::default",
            "<alloc::collections::vec_deque::VecDeque as std::default::Default>::default",
        ],
        default::specs::VECDEQUE_EMPTY,
    ),
    (
        &[
            "<char as core::default::Default>::default",
            "<char as std::default::Default>::default",
            "char::default",
        ],
        default::specs::CHAR_NUL,
    ),
    // Generic Default::default() fallback
    (
        &[
            "core::default::Default::default",
            "std::default::Default::default",
        ],
        default::specs::POSTCONDITION_ONLY,
    ),
];

// ── Ptr / Slice domain ──────────────────────────────────────────────────────

/// Char, raw pointer, and slice spec entries.
///
/// These entries consolidate the path metadata previously owned by
/// `trust-wp-driver/src/std_specs/table/ptr_slice.rs`.
/// No entries in this domain participate in the builtin extern-spec bridge.
pub static PTR_SLICE: &[SpecLookupEntry] = &[
    // Char specs
    (
        &["core::char::methods::is_ascii", "char::is_ascii"],
        primitives::specs::CHAR_IS_ASCII,
    ),
    (
        &[
            "core::char::methods::is_ascii_digit",
            "char::is_ascii_digit",
        ],
        primitives::specs::CHAR_IS_ASCII_DIGIT,
    ),
    (
        &[
            "core::char::methods::is_ascii_alphabetic",
            "char::is_ascii_alphabetic",
        ],
        primitives::specs::CHAR_IS_ASCII_ALPHABETIC,
    ),
    (
        &[
            "core::char::methods::is_ascii_lowercase",
            "char::is_ascii_lowercase",
        ],
        primitives::specs::CHAR_IS_ASCII_LOWERCASE,
    ),
    (
        &[
            "core::char::methods::is_ascii_uppercase",
            "char::is_ascii_uppercase",
        ],
        primitives::specs::CHAR_IS_ASCII_UPPERCASE,
    ),
    // ── Raw pointer specs ─────────────────────────────────────────────
    (
        &[
            "core::ptr::const_ptr::<impl *const T>::addr",
            "core::ptr::mut_ptr::<impl *mut T>::addr",
            // Normalized forms (normalize_path strips `<impl *const T>` as generic):
            "core::ptr::const_ptr::addr",
            "core::ptr::mut_ptr::addr",
            "<*const T>::addr",
            "<*mut T>::addr",
        ],
        ptr::specs::ADDR,
    ),
    (
        &[
            "core::ptr::const_ptr::<impl *const T>::is_null",
            "core::ptr::mut_ptr::<impl *mut T>::is_null",
            // Normalized forms (normalize_path strips `<impl *const T>` as generic):
            "core::ptr::const_ptr::is_null",
            "core::ptr::mut_ptr::is_null",
            "<*const T>::is_null",
            "<*mut T>::is_null",
        ],
        ptr::specs::IS_NULL,
    ),
    (
        &[
            // Free-standing constructors that return a null pointer.
            // Spec gives result.addr_logic() == 0, eliminating the
            // fail-closed `requires(false)` injection that opaque calls
            // otherwise produce (#2048) and unblocking `union_find_*`'s
            // injected `impl Default for Elem` shim.
            "core::ptr::null",
            "core::ptr::null_mut",
            "std::ptr::null",
            "std::ptr::null_mut",
        ],
        ptr::specs::NULL_PTR,
    ),
    (
        &[
            // Address-based pointer equality. Used by `Elem::eq` shims that
            // compare `*mut ()` wrappers in `union_find_*`.
            "core::ptr::addr_eq",
            "std::ptr::addr_eq",
        ],
        ptr::specs::ADDR_EQ,
    ),
    // ── Slice specs ─────────────────────────────────────────────────
    (
        &[
            "core::slice::binary_search",
            "core::slice::<impl [T]>::binary_search",
            "[T]::binary_search",
        ],
        slice::specs::BINARY_SEARCH,
    ),
    (
        &[
            "core::slice::binary_search_by",
            "core::slice::<impl [T]>::binary_search_by",
            "[T]::binary_search_by",
        ],
        slice::specs::BINARY_SEARCH_BY,
    ),
    (
        &[
            "core::slice::binary_search_by_key",
            "core::slice::<impl [T]>::binary_search_by_key",
            "[T]::binary_search_by_key",
        ],
        slice::specs::BINARY_SEARCH_BY_KEY,
    ),
    (
        &[
            "core::slice::partition_point",
            "core::slice::<impl [T]>::partition_point",
            "[T]::partition_point",
        ],
        slice::specs::PARTITION_POINT,
    ),
    (
        &[
            "core::slice::len",
            "core::slice::<impl [T]>::len",
            "[T]::len",
        ],
        slice::specs::LEN,
    ),
    (
        &[
            "core::slice::is_empty",
            "core::slice::<impl [T]>::is_empty",
            "[T]::is_empty",
        ],
        slice::specs::IS_EMPTY,
    ),
    (
        // bare `core::slice::get` lives in core_types.rs (Vec deref path)
        &["core::slice::<impl [T]>::get", "[T]::get"],
        slice::specs::GET_GENERIC,
    ),
    (
        // bare `core::slice::get_mut` lives in core_types.rs (Vec deref path)
        &["core::slice::<impl [T]>::get_mut", "[T]::get_mut"],
        slice::specs::GET_MUT_GENERIC,
    ),
    (
        // bare `core::slice::first` and `std::slice::first` should resolve
        // to the slice inherent-method spec, not the Vec fallback.
        &[
            "core::slice::first",
            "std::slice::first",
            "core::slice::<impl [T]>::first",
            "[T]::first",
        ],
        slice::specs::FIRST,
    ),
    (
        // bare `core::slice::last` and `std::slice::last` should resolve
        // to the slice inherent-method spec, not the Vec fallback.
        &[
            "core::slice::last",
            "std::slice::last",
            "core::slice::<impl [T]>::last",
            "[T]::last",
        ],
        slice::specs::LAST,
    ),
    (
        // bare `core::slice::contains` lives in core_types.rs (Vec deref path)
        &["core::slice::<impl [T]>::contains", "[T]::contains"],
        slice::specs::CONTAINS,
    ),
    // Slice Index trait — concrete and trait-qualified paths (#967)
    (
        &[
            "core::slice::index",
            "core::slice::<impl [T]>::index",
            "[T]::index",
            "<[T] as core::ops::Index>::index",
            "<[T] as std::ops::Index>::index",
        ],
        slice::specs::INDEX_GENERIC,
    ),
    (
        &[
            "core::slice::index_mut",
            "core::slice::<impl [T]>::index_mut",
            "[T]::index_mut",
            "<[T] as core::ops::IndexMut>::index_mut",
            "<[T] as std::ops::IndexMut>::index_mut",
        ],
        slice::specs::INDEX_MUT_GENERIC,
    ),
    (
        &[
            "core::slice::split_at",
            "core::slice::<impl [T]>::split_at",
            "[T]::split_at",
        ],
        slice::specs::SPLIT_AT,
    ),
    (
        &[
            "core::slice::split_at_mut",
            "core::slice::<impl [T]>::split_at_mut",
            "[T]::split_at_mut",
        ],
        slice::specs::SPLIT_AT_MUT,
    ),
    (
        &[
            "core::slice::windows",
            "core::slice::<impl [T]>::windows",
            "[T]::windows",
        ],
        slice::specs::WINDOWS,
    ),
    (
        &[
            "core::slice::chunks",
            "core::slice::<impl [T]>::chunks",
            "[T]::chunks",
        ],
        slice::specs::CHUNKS,
    ),
    // Note: core::slice::iter and iter_mut are in the iter.rs table (not here)
    // because they return iterator types and need the iterator adapter wiring.
    (
        &[
            "core::slice::split_first",
            "core::slice::<impl [T]>::split_first",
            "[T]::split_first",
        ],
        slice::specs::SPLIT_FIRST,
    ),
    (
        &[
            "core::slice::split_last",
            "core::slice::<impl [T]>::split_last",
            "[T]::split_last",
        ],
        slice::specs::SPLIT_LAST,
    ),
    (
        &[
            "core::slice::copy_from_slice",
            "core::slice::<impl [T]>::copy_from_slice",
            "[T]::copy_from_slice",
        ],
        slice::specs::COPY_FROM_SLICE,
    ),
    (
        &[
            "core::slice::sort_by",
            "core::slice::<impl [T]>::sort_by",
            "[T]::sort_by",
        ],
        slice::specs::SORT_BY,
    ),
    (
        &[
            "core::slice::sort_by_key",
            "core::slice::<impl [T]>::sort_by_key",
            "[T]::sort_by_key",
        ],
        slice::specs::SORT_BY_KEY,
    ),
    (
        &[
            "core::slice::sort_unstable_by",
            "core::slice::<impl [T]>::sort_unstable_by",
            "[T]::sort_unstable_by",
        ],
        slice::specs::SORT_UNSTABLE_BY,
    ),
    (
        &[
            "core::slice::sort_unstable_by_key",
            "core::slice::<impl [T]>::sort_unstable_by_key",
            "[T]::sort_unstable_by_key",
        ],
        slice::specs::SORT_UNSTABLE_BY_KEY,
    ),
    (
        &[
            "core::slice::rotate_left",
            "core::slice::<impl [T]>::rotate_left",
            "[T]::rotate_left",
        ],
        slice::specs::ROTATE_LEFT,
    ),
    (
        &[
            "core::slice::rotate_right",
            "core::slice::<impl [T]>::rotate_right",
            "[T]::rotate_right",
        ],
        slice::specs::ROTATE_RIGHT,
    ),
    (
        &[
            "core::slice::fill",
            "core::slice::<impl [T]>::fill",
            "[T]::fill",
        ],
        slice::specs::FILL,
    ),
    // ── Mutable slice methods (bare paths) ─────────────────────────
    (
        &[
            "core::slice::split_first_mut",
            "core::slice::<impl [T]>::split_first_mut",
            "[T]::split_first_mut",
        ],
        slice::specs::SPLIT_FIRST_MUT,
    ),
    (
        &[
            "core::slice::split_last_mut",
            "core::slice::<impl [T]>::split_last_mut",
            "[T]::split_last_mut",
        ],
        slice::specs::SPLIT_LAST_MUT,
    ),
    // NOTE: bare `core::slice::first_mut` etc. live in core_types.rs (Vec deref paths).
    // Only the `<impl [T]>` and `[T]` forms go here to avoid duplicate-alias violations.
    (
        &["core::slice::<impl [T]>::first_mut", "[T]::first_mut"],
        slice::specs::FIRST_MUT,
    ),
    (
        &["core::slice::<impl [T]>::last_mut", "[T]::last_mut"],
        slice::specs::LAST_MUT,
    ),
    (
        &["core::slice::<impl [T]>::swap", "[T]::swap"],
        slice::specs::SWAP,
    ),
    (
        &["core::slice::<impl [T]>::reverse", "[T]::reverse"],
        slice::specs::REVERSE,
    ),
    (
        &["core::slice::<impl [T]>::sort", "[T]::sort"],
        slice::specs::SORT,
    ),
    (
        &[
            "core::slice::<impl [T]>::sort_unstable",
            "[T]::sort_unstable",
        ],
        slice::specs::SORT_UNSTABLE,
    ),
    (
        &["core::slice::<impl [T]>::dedup", "[T]::dedup"],
        slice::specs::DEDUP,
    ),
];

/// Get alias paths for a builtin extern entry whose alias coverage has
/// been migrated to the shared registry.
///
/// Returns `Some(alias_slice)` if the canonical path matches a migrated
/// entry in `MEM_CLONE_DEFAULT` (the only pilot domain with builtin extern
/// entries). Returns `None` for non-migrated paths, signaling the driver
/// should use its own `expand_builtin_path_aliases()`.
///
/// `ptr_slice` has no builtin extern entries, so it is not checked.
pub fn migrated_builtin_extern_aliases(canonical_path: &str) -> Option<&'static [&'static str]> {
    for (paths, _spec) in MEM_CLONE_DEFAULT {
        if !paths.is_empty() && paths[0] == canonical_path {
            // mem::replace/swap/take are NOT in BUILTIN_EXTERN_SPECS,
            // but returning their aliases here is harmless — the caller
            // only invokes this for paths that ARE in BUILTIN_EXTERN_SPECS.
            return Some(&paths[1..]);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mem_clone_default_has_expected_entry_count() {
        // 3 mem + 13 clone + 1 generic clone + 20 default (13 primitive + 8 collection/char + 1 generic) = 40
        assert_eq!(MEM_CLONE_DEFAULT.len(), 40);
    }

    #[test]
    fn ptr_slice_has_expected_entry_count() {
        // 5 char + 4 ptr (addr, is_null, null/null_mut, addr_eq) + 22 slice +
        // 7 sort/rotate/fill + 9 mut slice (split_first_mut, split_last_mut,
        // first_mut, last_mut, swap, reverse, sort, sort_unstable, dedup) +
        // 3 for binary_search_by, binary_search_by_key, partition_point = 45.
        assert_eq!(PTR_SLICE.len(), 45);
    }

    #[test]
    fn all_entries_have_at_least_one_path() {
        for (paths, _spec) in MEM_CLONE_DEFAULT.iter().chain(PTR_SLICE.iter()) {
            assert!(!paths.is_empty(), "entry has empty path list");
        }
    }

    #[test]
    fn all_entries_have_nonempty_spec() {
        for (paths, spec) in MEM_CLONE_DEFAULT.iter().chain(PTR_SLICE.iter()) {
            assert!(
                !spec.trim().is_empty(),
                "entry {:?} has empty spec",
                paths[0]
            );
        }
    }

    #[test]
    fn no_duplicate_paths_within_registry() {
        use std::collections::HashSet;
        let mut seen = HashSet::new();
        for (paths, _spec) in MEM_CLONE_DEFAULT.iter().chain(PTR_SLICE.iter()) {
            for &path in *paths {
                assert!(
                    seen.insert(path),
                    "duplicate path in lookup registry: {path}"
                );
            }
        }
    }

    #[test]
    fn migrated_aliases_returns_some_for_clone_entry() {
        let aliases = migrated_builtin_extern_aliases("<bool as core::clone::Clone>::clone");
        assert!(aliases.is_some(), "bool clone should be migrated");
        let aliases = aliases.unwrap();
        assert!(
            aliases.contains(&"<bool as std::clone::Clone>::clone"),
            "should include std alias"
        );
        assert!(
            aliases.contains(&"bool::clone"),
            "should include shorthand alias"
        );
    }

    #[test]
    fn migrated_aliases_returns_some_for_default_entry() {
        let aliases = migrated_builtin_extern_aliases("<i32 as core::default::Default>::default");
        assert!(aliases.is_some(), "i32 default should be migrated");
        let aliases = aliases.unwrap();
        assert!(
            aliases.contains(&"<i32 as std::default::Default>::default"),
            "should include std alias"
        );
        assert!(
            aliases.contains(&"i32::default"),
            "should include shorthand alias"
        );
    }

    #[test]
    fn migrated_aliases_returns_none_for_vec_push() {
        assert!(
            migrated_builtin_extern_aliases("std::vec::Vec::push").is_none(),
            "Vec::push is not in a migrated domain"
        );
    }

    #[test]
    fn clone_entries_cover_all_primitive_types() {
        let expected_types = [
            "bool", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128",
            "usize",
        ];
        for ty in &expected_types {
            let canonical = format!("<{ty} as core::clone::Clone>::clone");
            assert!(
                MEM_CLONE_DEFAULT
                    .iter()
                    .any(|(paths, _)| paths[0] == canonical),
                "missing clone entry for {ty}"
            );
        }
    }

    #[test]
    fn default_entries_cover_all_primitive_types() {
        let expected_types = [
            "bool", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128",
            "usize",
        ];
        for ty in &expected_types {
            let canonical = format!("<{ty} as core::default::Default>::default");
            assert!(
                MEM_CLONE_DEFAULT
                    .iter()
                    .any(|(paths, _)| paths[0] == canonical),
                "missing default entry for {ty}"
            );
        }
    }

    #[test]
    fn default_entries_cover_collection_types() {
        // Vec, String, Option, HashMap, and HashSet should have concrete Default specs (#2256)
        let expected = [
            (
                "<alloc::vec::Vec as core::default::Default>::default",
                "result@.len() == 0",
            ),
            (
                "<alloc::string::String as core::default::Default>::default",
                "result@.len() == 0",
            ),
            (
                "<core::option::Option as core::default::Default>::default",
                "result == None()",
            ),
            (
                "<std::collections::HashMap as core::default::Default>::default",
                "result@.len() == 0",
            ),
            (
                "<std::collections::HashSet as core::default::Default>::default",
                "result@.len() == 0",
            ),
        ];
        for (path, expected_clause) in &expected {
            let entry = MEM_CLONE_DEFAULT
                .iter()
                .find(|(paths, _)| paths.contains(path));
            assert!(
                entry.is_some(),
                "missing collection default entry for {path}"
            );
            let (_paths, spec) = entry.unwrap();
            assert!(
                spec.contains(expected_clause),
                "{path} default spec should contain `{expected_clause}`, got: {spec}"
            );
            assert!(
                spec.contains("Default::default.postcondition"),
                "{path} default spec should also retain the generic postcondition fact"
            );
        }
    }

    // ── new primitive arithmetic spec strings parse cleanly ───────────────
    //
    // These specs are registered via `primitives_overflow.rs` (a driver-side
    // table that does not flow through `lookup_registry`). The tests below
    // sanity-check the spec strings themselves so that breakage shows up in
    // `trust-wp-std`'s own test suite rather than only at driver lookup time.

    #[test]
    fn checked_neg_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::CHECKED_NEG;
        assert!(
            spec.contains("0 - self@"),
            "CHECKED_NEG should encode negation via `0 - self@`, got: {spec}"
        );
        assert!(
            spec.contains("result.is_some()") && spec.contains("result.is_none()"),
            "CHECKED_NEG should branch on overflow via is_some/is_none, got: {spec}"
        );
        // Three implication arms: in-range -> Some, in-range -> value, out-of-range -> None.
        assert_eq!(
            spec.matches("ensures:").count(),
            3,
            "CHECKED_NEG should have 3 ensures clauses"
        );
    }

    #[test]
    fn checked_rem_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::CHECKED_REM;
        assert!(
            spec.contains("self@ % rhs@"),
            "CHECKED_REM should compute `self@ % rhs@`, got: {spec}"
        );
        assert!(
            spec.contains("rhs@ != 0") && spec.contains("rhs@ == 0"),
            "CHECKED_REM should split on `rhs == 0`, got: {spec}"
        );
        assert_eq!(
            spec.matches("ensures:").count(),
            3,
            "CHECKED_REM should have 3 ensures clauses"
        );
    }

    #[test]
    fn wrapping_rem_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::WRAPPING_REM;
        assert!(
            spec.contains("requires: rhs@ != 0"),
            "WRAPPING_REM should require rhs@ != 0, got: {spec}"
        );
        assert!(
            spec.contains("self@ % rhs@"),
            "WRAPPING_REM should compute `self@ % rhs@`, got: {spec}"
        );
        assert_eq!(
            spec.matches("ensures:").count(),
            1,
            "WRAPPING_REM should have a single ensures clause"
        );
    }

    #[test]
    fn signum_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::SIGNUM;
        // Three implication arms: negative -> -1, zero -> 0, positive -> 1.
        assert_eq!(
            spec.matches("ensures:").count(),
            3,
            "SIGNUM should have 3 ensures clauses"
        );
        assert!(
            spec.contains("self@ < 0") && spec.contains("result@ == 0 - 1"),
            "SIGNUM should map self < 0 to result == -1, got: {spec}"
        );
        assert!(
            spec.contains("self@ == 0") && spec.contains("result@ == 0"),
            "SIGNUM should map self == 0 to result == 0, got: {spec}"
        );
        assert!(
            spec.contains("self@ > 0") && spec.contains("result@ == 1"),
            "SIGNUM should map self > 0 to result == 1, got: {spec}"
        );
    }

    #[test]
    fn is_positive_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::IS_POSITIVE;
        assert_eq!(
            spec.matches("ensures:").count(),
            1,
            "IS_POSITIVE should have a single ensures clause"
        );
        assert!(
            spec.contains("(self@ > 0)"),
            "IS_POSITIVE should encode `result == (self@ > 0)`, got: {spec}"
        );
    }

    #[test]
    fn is_negative_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::IS_NEGATIVE;
        assert_eq!(
            spec.matches("ensures:").count(),
            1,
            "IS_NEGATIVE should have a single ensures clause"
        );
        assert!(
            spec.contains("(self@ < 0)"),
            "IS_NEGATIVE should encode `result == (self@ < 0)`, got: {spec}"
        );
    }

    #[test]
    fn abs_diff_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::ABS_DIFF;
        assert_eq!(
            spec.matches("ensures:").count(),
            2,
            "ABS_DIFF should have 2 ensures clauses (>= and <)"
        );
        assert!(
            spec.contains("self@ >= rhs@") && spec.contains("self@ - rhs@"),
            "ABS_DIFF should map self >= rhs to self - rhs, got: {spec}"
        );
        assert!(
            spec.contains("self@ < rhs@") && spec.contains("rhs@ - self@"),
            "ABS_DIFF should map self < rhs to rhs - self, got: {spec}"
        );
    }

    #[test]
    fn saturating_neg_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::SATURATING_NEG;
        assert_eq!(
            spec.matches("ensures:").count(),
            2,
            "SATURATING_NEG should have 2 ensures clauses (MIN saturates, else 0 - self)"
        );
        assert!(
            spec.contains("self@ == Self::MIN@") && spec.contains("result@ == Self::MAX@"),
            "SATURATING_NEG should map MIN -> MAX, got: {spec}"
        );
        assert!(
            spec.contains("self@ > Self::MIN@") && spec.contains("0 - self@"),
            "SATURATING_NEG should map self > MIN to 0 - self, got: {spec}"
        );
    }

    #[test]
    fn wrapping_abs_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::WRAPPING_ABS;
        assert_eq!(
            spec.matches("ensures:").count(),
            3,
            "WRAPPING_ABS should have 3 ensures clauses (MIN, nonneg, neg)"
        );
        assert!(
            spec.contains("self@ == Self::MIN@") && spec.contains("result@ == Self::MIN@"),
            "WRAPPING_ABS should map MIN -> MIN (wraps), got: {spec}"
        );
        assert!(
            spec.contains("self@ >= 0") && spec.contains("result@ == self@"),
            "WRAPPING_ABS should map nonneg self to self, got: {spec}"
        );
        assert!(
            spec.contains("self@ < 0") && spec.contains("0 - self@"),
            "WRAPPING_ABS should map negative self to 0 - self, got: {spec}"
        );
    }

    #[test]
    fn count_ones_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::COUNT_ONES;
        assert_eq!(
            spec.matches("ensures:").count(),
            2,
            "COUNT_ONES should have 2 ensures clauses (nonneg, zero-case)"
        );
        assert!(
            spec.contains("result@ >= 0"),
            "COUNT_ONES should ensure result is nonneg, got: {spec}"
        );
        assert!(
            spec.contains("self@ == 0") && spec.contains("result@ == 0"),
            "COUNT_ONES should map self == 0 to result == 0, got: {spec}"
        );
    }

    #[test]
    fn count_zeros_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::COUNT_ZEROS;
        assert_eq!(
            spec.matches("ensures:").count(),
            2,
            "COUNT_ZEROS should have 2 ensures clauses (nonneg, zero-case)"
        );
        assert!(
            spec.contains("result@ >= 0"),
            "COUNT_ZEROS should ensure result is nonneg, got: {spec}"
        );
        assert!(
            spec.contains("self@ == 0") && spec.contains("result@ > 0"),
            "COUNT_ZEROS should map self == 0 to result > 0, got: {spec}"
        );
    }

    #[test]
    fn next_power_of_two_spec_string_contains_signature_fragments() {
        let spec = primitives::specs::NEXT_POWER_OF_TWO;
        assert_eq!(
            spec.matches("ensures:").count(),
            3,
            "NEXT_POWER_OF_TWO should have 3 ensures clauses (>= 1, >= self, <=1 case)"
        );
        assert!(
            spec.contains("result@ >= 1"),
            "NEXT_POWER_OF_TWO should ensure result >= 1, got: {spec}"
        );
        assert!(
            spec.contains("result@ >= self@"),
            "NEXT_POWER_OF_TWO should ensure result >= self, got: {spec}"
        );
        assert!(
            spec.contains("self@ <= 1") && spec.contains("result@ == 1"),
            "NEXT_POWER_OF_TWO should map self <= 1 to result == 1, got: {spec}"
        );
    }
}
