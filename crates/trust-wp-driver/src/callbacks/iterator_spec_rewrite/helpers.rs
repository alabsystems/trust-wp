// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort detection helpers for iterator type identification.

use trust_wp_core::formula::{resolve_sort_name, ExprSort, PureExpr};

/// Sort names that identify `Vec::IntoIter` in the sort interner.
///
/// `tcx.def_path_str()` records concrete ADT paths, so the rewrite must stay
/// on the vector iterator allowlist rather than matching every `*::IntoIter`.
pub(super) const VEC_INTO_ITER_SORT_NAMES: &[&str] =
    &["alloc::vec::into_iter::IntoIter", "std::vec::IntoIter"];

/// Sort names that identify `Range<T>` in the sort interner.
pub(super) const RANGE_SORT_NAMES: &[&str] = &[
    "core::ops::range::Range",
    "std::ops::Range",
    "core::ops::Range",
];

/// Sort names that identify `std::iter::Empty<T>` in the sort interner.
pub(super) const EMPTY_SORT_NAMES: &[&str] = &[
    "core::iter::sources::empty::Empty",
    "core::iter::Empty",
    "std::iter::Empty",
];

/// Sort names that identify `std::iter::Once<T>` in the sort interner.
pub(super) const ONCE_SORT_NAMES: &[&str] = &[
    "core::iter::sources::once::Once",
    "core::iter::Once",
    "std::iter::Once",
];

/// Sort names that identify `std::iter::Repeat<T>` in the sort interner.
pub(super) const REPEAT_SORT_NAMES: &[&str] = &[
    "core::iter::sources::repeat::Repeat",
    "core::iter::Repeat",
    "std::iter::Repeat",
];

/// Sort names that identify `std::iter::Fuse<I>` in the sort interner.
pub(super) const FUSE_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::fuse::Fuse",
    "core::iter::Fuse",
    "std::iter::Fuse",
];

/// Sort names that identify `std::iter::Cloned<I>` in the sort interner.
pub(super) const CLONED_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::cloned::Cloned",
    "core::iter::Cloned",
    "std::iter::Cloned",
];

/// Sort names that identify `std::iter::Copied<I>` in the sort interner.
pub(super) const COPIED_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::copied::Copied",
    "core::iter::Copied",
    "std::iter::Copied",
];

/// Sort names that identify `std::iter::Rev<I>` in the sort interner.
pub(super) const REV_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::rev::Rev",
    "core::iter::Rev",
    "std::iter::Rev",
];

/// Sort names that identify `std::iter::Skip<I>` in the sort interner.
pub(super) const SKIP_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::skip::Skip",
    "core::iter::Skip",
    "std::iter::Skip",
];

/// Sort names that identify `std::iter::Take<I>` in the sort interner.
pub(super) const TAKE_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::take::Take",
    "core::iter::Take",
    "std::iter::Take",
];

/// Sort names that identify `std::iter::Enumerate<I>` in the sort interner.
pub(super) const ENUMERATE_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::enumerate::Enumerate",
    "core::iter::Enumerate",
    "std::iter::Enumerate",
];

/// Sort names that identify `std::iter::Zip<A, B>` in the sort interner.
pub(super) const ZIP_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::zip::Zip",
    "core::iter::Zip",
    "std::iter::Zip",
];

/// Sort names that identify `std::iter::Chain<A, B>` in the sort interner.
pub(super) const CHAIN_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::chain::Chain",
    "core::iter::Chain",
    "std::iter::Chain",
];

/// Sort names that identify `std::iter::Peekable<I>` in the sort interner.
pub(super) const PEEKABLE_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::peekable::Peekable",
    "core::iter::Peekable",
    "std::iter::Peekable",
];

/// Sort names that identify `std::iter::Map<I, F>` in the sort interner.
pub(super) const MAP_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::map::Map",
    "core::iter::Map",
    "std::iter::Map",
];

/// Sort names that identify `std::iter::Filter<I, P>` in the sort interner.
pub(super) const FILTER_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::filter::Filter",
    "core::iter::Filter",
    "std::iter::Filter",
];

/// Sort names that identify `std::iter::FilterMap<I, F>` in the sort interner.
pub(super) const FILTER_MAP_SORT_NAMES: &[&str] = &[
    "core::iter::adapters::filter_map::FilterMap",
    "core::iter::FilterMap",
    "std::iter::FilterMap",
];

/// Sort names that identify `trust_wp_std::std::iter::MapInv<I, F>` in the sort
/// interner.
pub(super) const MAP_INV_SORT_NAMES: &[&str] = &[
    "trust_wp_std::std::iter::map_inv::MapInv",
    "trust_wp_std::std::iter::MapInv",
    "creusot_std::std::iter::MapInv",
    "creusot_std::MapInv",
];

/// Sort names that identify `std::collections::HashMap::IntoIter` in the sort
/// interner.
pub(super) const HASH_MAP_INTO_ITER_SORT_NAMES: &[&str] = &[
    "std::collections::hash_map::IntoIter",
    "std::collections::hash::map::IntoIter",
];

/// Sort names that identify `std::collections::HashMap::Iter` in the sort
/// interner.
pub(super) const HASH_MAP_ITER_SORT_NAMES: &[&str] = &[
    "std::collections::hash_map::Iter",
    "std::collections::hash::map::Iter",
];

/// Sort names that identify `std::collections::HashMap::IterMut` in the sort
/// interner.
pub(super) const HASH_MAP_ITER_MUT_SORT_NAMES: &[&str] = &[
    "std::collections::hash_map::IterMut",
    "std::collections::hash::map::IterMut",
];

/// Sort names that identify `std::collections::HashSet::IntoIter` in the sort
/// interner.
pub(super) const HASH_SET_INTO_ITER_SORT_NAMES: &[&str] = &[
    "std::collections::hash_set::IntoIter",
    "std::collections::hash::set::IntoIter",
];

/// Sort names that identify `std::collections::HashSet::Iter` in the sort
/// interner.
pub(super) const HASH_SET_ITER_SORT_NAMES: &[&str] = &[
    "std::collections::hash_set::Iter",
    "std::collections::hash::set::Iter",
];

/// Sort names that identify `std::collections::HashSet::Intersection` in the
/// sort interner.
pub(super) const HASH_SET_INTERSECTION_SORT_NAMES: &[&str] = &[
    "std::collections::hash_set::Intersection",
    "std::collections::hash::set::Intersection",
];

/// Sort names that identify `std::collections::HashSet::Difference` in the
/// sort interner.
pub(super) const HASH_SET_DIFFERENCE_SORT_NAMES: &[&str] = &[
    "std::collections::hash_set::Difference",
    "std::collections::hash::set::Difference",
];

/// Sort names that identify `trust_wp_std::logic::fmap::FMapIter` (logical FMap
/// into_iter) in the sort interner. Yields owned `(K, V)` pairs.
pub(super) const FMAP_ITER_SORT_NAMES: &[&str] = &[
    "trust_wp_std::logic::fmap::FMapIter",
    // The Creusot-facing `FMapIter` sort surfaced by owned FMap iteration
    // (`for (k, v) in s`). Without it `is_logical_fmap_iter` returns false, the
    // loop falls through to the generic iterator path (no FMap frame axioms, no
    // element prophecy resolution), and trust-wp emits a validated-sat
    // counterexample to a *true* invariant (`^snap_k` left uninterpreted).
    "creusot_std::logic::fmap::FMapIter",
    "creusot_std::logic::fmap::Iter",
    "logic::fmap::Iter",
    // Concrete sort forms surfaced by owned FMap iteration
    // (e.g., `for (k, v) in s` over an `FMap<K, V>`). Without these the
    // iterator-spec rewrite falls through and the FMap-iter identity bridge
    // never fires, leaving snapshot-alias invariants unprovable.
    "trust_wp_std::logic::fmap::FMap::IntoIter",
    "creusot_std::logic::fmap::FMap::IntoIter",
    "logic::fmap::FMap::IntoIter",
    "trust_wp_std::logic::fmap::IntoIter",
    "creusot_std::logic::fmap::IntoIter",
];

/// Sort names that identify `trust_wp_std::logic::seq::SeqIter` (logical Seq
/// into_iter) in the sort interner. Yields owned `T` elements in order.
pub(super) const SEQ_ITER_SORT_NAMES: &[&str] = &[
    "trust_wp_std::logic::seq::SeqIter",
    "trust_wp_std::logic::seq::iter::SeqIter",
    "creusot_std::logic::seq::SeqIter",
    "creusot_std::logic::seq::iter::SeqIter",
    "creusot_std::logic::seq::Iter",
    "logic::seq::Iter",
];

/// Sort names that identify borrowed `std::slice::Iter` in the sort interner.
///
/// This family stays fail-closed in the driver rewrite until a dedicated
/// borrowed-element / ref-seq design lands. Keeping the allowlist explicit
/// prevents future patches from widening the SeqIter rule silently. (#2116,
/// #2172, #694)
pub(super) const SLICE_ITER_SORT_NAMES: &[&str] = &[
    "core::slice::iter::Iter",
    "core::slice::Iter",
    "std::slice::Iter",
];

/// Sort names that identify mutable `std::slice::IterMut` in the sort interner.
///
/// `IterMut` yields `&mut T` elements. The produces rewrite uses a
/// snapshot-aware model: each visited element's dereferenced value corresponds
/// to the container's pre-mutation content at that position. This enables
/// verifying loops over `iter_mut()` that track mutations via the
/// `*visited[i]` / `^visited[i]` (current/final) separation logic encoding.
/// (#2238)
pub(super) const SLICE_ITER_MUT_SORT_NAMES: &[&str] = &[
    "core::slice::iter::IterMut",
    "core::slice::IterMut",
    "std::slice::IterMut",
];

/// Check whether a `Datatype` sort name matches any name in the allowlist.
pub(super) fn sort_matches_any(id: u32, names: &[&str]) -> bool {
    let name = resolve_sort_name(id);
    names.contains(&name.as_str())
}

/// Check whether a `Datatype` sort name matches `Vec::IntoIter`.
pub(super) fn is_into_iter_sort(id: u32) -> bool {
    sort_matches_any(id, VEC_INTO_ITER_SORT_NAMES)
}

/// Extract the `ExprSort` from the root variable of a receiver expression,
/// stripping through `Old`, `Deref`, `Final`, and `View` wrappers.
pub(super) fn receiver_root_sort(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, sort) => sort.as_ref(),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_root_sort(inner),
        _ => None,
    }
}

fn datatype_id_from_sort(sort: &ExprSort) -> Option<u32> {
    match sort {
        ExprSort::Datatype(id) => Some(*id),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => datatype_id_from_sort(inner),
        _ => None,
    }
}

/// Returns the Datatype sort ID of the receiver, if it has one.
pub(super) fn receiver_datatype_id(expr: &PureExpr) -> Option<u32> {
    receiver_root_sort(expr).and_then(datatype_id_from_sort)
}

/// Returns `true` if `expr` is a receiver whose root variable type is
/// `Vec::IntoIter` (gated by `ExprSort::Datatype` annotation).
pub(super) fn is_into_iter_receiver(expr: &PureExpr) -> bool {
    receiver_datatype_id(expr).is_some_and(is_into_iter_sort)
}

/// Returns `true` if the expression's root sort is a Seq-backed iterator
/// (SeqIter or Vec::IntoIter) whose `View` gives a `Seq`.
///
/// Used by `loop_verify` to generate direct `push_front` transition facts
/// instead of the ext_eq+concat form, which avoids quantifier overhead in
/// the preservation proof. (#2116)
pub(crate) fn is_seq_backed_iterator(expr: &PureExpr) -> bool {
    receiver_datatype_id(expr).is_some_and(|id| {
        sort_matches_any(id, SEQ_ITER_SORT_NAMES) || sort_matches_any(id, VEC_INTO_ITER_SORT_NAMES)
    })
}

/// Returns `true` if the expression's root sort is backed by an FMap view.
///
/// Logical `FMapIter` and the standard-library `HashMap` iterator families all
/// expose `View(iter_state)` as an `FMap`, so loop completion can reuse the
/// same `iter@ == fmap_new()` exhaustion fact. (#2116)
pub(crate) fn is_fmap_backed_iterator(expr: &PureExpr) -> bool {
    receiver_datatype_id(expr).is_some_and(|id| {
        sort_matches_any(id, FMAP_ITER_SORT_NAMES)
            || sort_matches_any(id, HASH_MAP_INTO_ITER_SORT_NAMES)
            || sort_matches_any(id, HASH_MAP_ITER_SORT_NAMES)
            || sort_matches_any(id, HASH_MAP_ITER_MUT_SORT_NAMES)
    })
}

/// Returns `true` only for the logical `FMapIter` family.
///
/// The loop verifier uses this narrower predicate for the direct `(K, V)`
/// single-step delta facts. Borrowed `HashMap::{Iter, IterMut}` still rely on
/// the generic collection rewrite until their yielded-reference model is wired
/// through the loop step relation. (#2116)
pub(crate) fn is_logical_fmap_iter(expr: &PureExpr) -> bool {
    receiver_datatype_id(expr).is_some_and(|id| sort_matches_any(id, FMAP_ITER_SORT_NAMES))
}
