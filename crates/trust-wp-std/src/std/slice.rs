// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for slice types (`[T]`)
//!
//! Provides logical methods for reasoning about slices in specifications.
//!
//! Reference: Creusot `creusot-std/src/std/slice.rs`

use std::ops;

use crate::{
    ghost::{perm::Perm, Ghost},
    logic::{Int, Seq},
};

/// Stable helper methods for slices.
pub trait SliceExt<T> {
    /// Convert the slice into a logical sequence of mutable references.
    fn to_mut_seq(&mut self) -> Seq<&mut T>;

    /// Convert the slice into a logical sequence of shared references.
    fn to_ref_seq(&self) -> Seq<&T>;

    /// Get a raw pointer to the slice data with a ghost permission token.
    fn as_ptr_perm(&self) -> (*const T, Ghost<&Perm<*const [T]>>);

    /// Get a mutable raw pointer to the slice data with a ghost permission token.
    fn as_mut_ptr_perm(&mut self) -> (*mut T, Ghost<&mut Perm<*const [T]>>);
}

impl<T> SliceExt<T> for [T] {
    fn to_mut_seq(&mut self) -> Seq<&mut T> {
        Seq::from(self.iter_mut().collect::<Vec<_>>())
    }

    fn to_ref_seq(&self) -> Seq<&T> {
        Seq::from(self.iter().collect::<Vec<_>>())
    }

    fn as_ptr_perm(&self) -> (*const T, Ghost<&Perm<*const [T]>>) {
        <[T] as SlicePermExt<T>>::as_ptr_perm(self)
    }

    fn as_mut_ptr_perm(&mut self) -> (*mut T, Ghost<&mut Perm<*const [T]>>) {
        <[T] as SlicePermExt<T>>::as_mut_ptr_perm(self)
    }
}

/// Extension trait providing permission-based pointer access for slices.
///
/// `Ext`-suffixed traits add new specification-only capabilities with no
/// runtime std counterpart (see [crate-level naming convention](crate)).
///
/// In Creusot, slices can be decomposed into a raw pointer paired with a
/// ghost permission token. This is used for verified unsafe code that needs
/// to reason about pointer permissions.
///
/// `SlicePermExt<T>` is kept as the older local compatibility layer. The
/// broader `SliceExt<T>` surface above matches the upstream stable helper API.
pub trait SlicePermExt<T> {
    /// Get a raw pointer to the slice data with a ghost permission token.
    ///
    /// Returns `(ptr, ghost_perm)` where `ptr == self.as_ptr()` and
    /// `ghost_perm` grants read access to the slice through the pointer.
    fn as_ptr_perm(&self) -> (*const T, Ghost<&Perm<*const [T]>>);

    /// Get a mutable raw pointer to the slice data with a ghost permission token.
    ///
    /// Returns `(ptr, ghost_perm)` where `ptr == self.as_mut_ptr()` and
    /// `ghost_perm` grants write access to the slice through the pointer.
    fn as_mut_ptr_perm(&mut self) -> (*mut T, Ghost<&mut Perm<*const [T]>>);
}

impl<T> SlicePermExt<T> for [T] {
    fn as_ptr_perm(&self) -> (*const T, Ghost<&Perm<*const [T]>>) {
        (self.as_ptr(), Ghost::conjure())
    }

    fn as_mut_ptr_perm(&mut self) -> (*mut T, Ghost<&mut Perm<*const [T]>>) {
        (self.as_mut_ptr(), Ghost::conjure())
    }
}

/// Trait for specifying the logical semantics of slice index types.
///
/// Each standard library index type (`usize`, `Range<usize>`, etc.) implements
/// this trait with three predicates:
///
/// - `in_bounds(seq)` — whether the index is a valid access into the sequence
/// - `has_value(seq, out)` — whether `out` is the value at this index in `seq`
/// - `resolve_elsewhere(old, fin)` — frame condition: indices outside this
///   range are unchanged between `old` and `fin`
///
/// Reference: Creusot `creusot-std/src/std/slice.rs:132-411` (`SliceIndexSpec`).
///
/// ## Deferred: `RangeInclusive<usize>`
///
/// The helper facade (`start_log`, `end_log`, `is_empty_log`) now exists
/// in `trust-wp-std::std::ops::RangeInclusiveExt` (#2519). The remaining
/// work is wiring `RangeInclusive<usize>` into `SliceIndexSpec`.
pub trait SliceIndexSpec<T> {
    /// The logical output type of indexing. For `usize` this is `T` (via
    /// `Seq::index_logic`); for range types this is `Seq<T>` (subsequence).
    type LogicOutput: PartialEq;

    /// Whether this index is a valid access into a sequence of the given length.
    fn in_bounds(&self, seq: &Seq<T>) -> bool;

    /// Whether `out` matches the value at this index position in `seq`.
    fn has_value(&self, seq: &Seq<T>, out: &Self::LogicOutput) -> bool;

    /// Frame condition: all indices outside this range are unchanged between
    /// `old` and `fin`. Length preservation is asserted separately.
    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool;
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for usize {
    type LogicOutput = T;

    fn in_bounds(&self, seq: &Seq<T>) -> bool {
        Int(*self as i128) < seq.len()
    }

    fn has_value(&self, seq: &Seq<T>, out: &T) -> bool {
        seq.clone().index_logic(Int(*self as i128)) == *out
    }

    #[allow(clippy::cast_sign_loss)] // Seq::len() is logically non-negative
    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool {
        let len = old.len().0 as usize;
        (0..len).filter(|&i| i != *self).all(|i| {
            old.clone().index_logic(Int(i as i128)) == fin.clone().index_logic(Int(i as i128))
        })
    }
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for ops::Range<usize> {
    type LogicOutput = Seq<T>;

    fn in_bounds(&self, seq: &Seq<T>) -> bool {
        Int(self.start as i128) <= Int(self.end as i128) && Int(self.end as i128) <= seq.len()
    }

    fn has_value(&self, seq: &Seq<T>, out: &Seq<T>) -> bool {
        seq.clone()
            .subsequence(Int(self.start as i128), Int(self.end as i128))
            == *out
    }

    #[allow(clippy::cast_sign_loss)] // Seq::len() is logically non-negative
    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool {
        let len = old.len().0 as usize;
        (0..len)
            .filter(|&i| !(self.start <= i && i < self.end))
            .all(|i| {
                old.clone().index_logic(Int(i as i128)) == fin.clone().index_logic(Int(i as i128))
            })
    }
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for ops::RangeTo<usize> {
    type LogicOutput = Seq<T>;

    fn in_bounds(&self, seq: &Seq<T>) -> bool {
        Int(self.end as i128) <= seq.len()
    }

    fn has_value(&self, seq: &Seq<T>, out: &Seq<T>) -> bool {
        seq.clone().subsequence(Int(0), Int(self.end as i128)) == *out
    }

    #[allow(clippy::cast_sign_loss)] // Seq::len() is logically non-negative
    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool {
        let len = old.len().0 as usize;
        (self.end..len).all(|i| {
            old.clone().index_logic(Int(i as i128)) == fin.clone().index_logic(Int(i as i128))
        })
    }
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for ops::RangeFrom<usize> {
    type LogicOutput = Seq<T>;

    fn in_bounds(&self, seq: &Seq<T>) -> bool {
        Int(self.start as i128) <= seq.len()
    }

    fn has_value(&self, seq: &Seq<T>, out: &Seq<T>) -> bool {
        seq.clone().subsequence(Int(self.start as i128), seq.len()) == *out
    }

    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool {
        (0..self.start).all(|i| {
            old.clone().index_logic(Int(i as i128)) == fin.clone().index_logic(Int(i as i128))
        })
    }
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for ops::RangeFull {
    type LogicOutput = Seq<T>;

    fn in_bounds(&self, _seq: &Seq<T>) -> bool {
        true
    }

    fn has_value(&self, seq: &Seq<T>, out: &Seq<T>) -> bool {
        *seq == *out
    }

    fn resolve_elsewhere(&self, _old: &Seq<T>, _fin: &Seq<T>) -> bool {
        true
    }
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for ops::RangeToInclusive<usize> {
    type LogicOutput = Seq<T>;

    fn in_bounds(&self, seq: &Seq<T>) -> bool {
        Int(self.end as i128) < seq.len()
    }

    fn has_value(&self, seq: &Seq<T>, out: &Seq<T>) -> bool {
        seq.clone().subsequence(Int(0), Int(self.end as i128 + 1)) == *out
    }

    #[allow(clippy::cast_sign_loss)] // Seq::len() is logically non-negative
    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool {
        let len = old.len().0 as usize;
        (self.end + 1..len).all(|i| {
            old.clone().index_logic(Int(i as i128)) == fin.clone().index_logic(Int(i as i128))
        })
    }
}

impl<T: Clone + PartialEq> SliceIndexSpec<T> for ops::RangeInclusive<usize> {
    type LogicOutput = Seq<T>;

    fn in_bounds(&self, seq: &Seq<T>) -> bool {
        use crate::std::ops::RangeInclusiveExt;
        let start = Int(self.clone().start_log() as i128);
        let end = Int(self.clone().end_log() as i128);
        start <= end && end < seq.len()
    }

    fn has_value(&self, seq: &Seq<T>, out: &Seq<T>) -> bool {
        use crate::std::ops::RangeInclusiveExt;
        let start = Int(self.clone().start_log() as i128);
        let end = Int(self.clone().end_log() as i128);
        seq.clone().subsequence(start, Int(end.0 + 1)) == *out
    }

    #[allow(clippy::cast_sign_loss)]
    fn resolve_elsewhere(&self, old: &Seq<T>, fin: &Seq<T>) -> bool {
        use crate::std::ops::RangeInclusiveExt;
        let start = self.clone().start_log();
        let end = self.clone().end_log();
        let len = old.len().0 as usize;
        (0..start).chain(end + 1..len).all(|i| {
            old.clone().index_logic(Int(i as i128)) == fin.clone().index_logic(Int(i as i128))
        })
    }
}

/// Mutable slice extension methods for Creusot compatibility.
///
/// `split_off_first_mut` extracts the first element from a `&mut [T]` while
/// shortening the slice reference — the pattern used by Creusot's iterator
/// examples (e.g., `02_iter_mut.rs`).
pub trait SliceMutExt<T> {
    /// Remove and return a mutable reference to the first element, advancing
    /// the slice reference past it.
    ///
    /// Returns `None` if the slice is empty.
    fn split_off_first_mut(&mut self) -> Option<&mut T>;
}

impl<'a, T> SliceMutExt<T> for &'a mut [T] {
    fn split_off_first_mut(&mut self) -> Option<&'a mut T> {
        if self.is_empty() {
            return None;
        }
        // Take ownership of the slice to reborrow with the outer lifetime.
        let slice = std::mem::take(self);
        let (first, rest) = slice.split_first_mut().expect("non-empty checked above");
        *self = rest;
        Some(first)
    }
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
#[doc(hidden)]
pub mod specs {
    /// Contract for `[T]::binary_search`
    ///
    /// If the value is found, returns Ok(index) where the element at index
    /// equals the searched value. If not found, returns Err(index) where
    /// index is the insertion point.
    pub const BINARY_SEARCH: &str = r"
        params: self, x
        ensures: match result {
            Ok(i) => i@ < self@.len() && self@[i@] == *x,
            Err(i) => i@ <= self@.len(),
        }
    ";

    /// Contract for `[T]::binary_search_by`
    ///
    /// Binary search with a comparator function. Like binary_search but
    /// uses a custom comparison closure instead of Ord.
    pub const BINARY_SEARCH_BY: &str = r"
        params: self, f
        ensures: match result {
            Ok(i) => i@ < self@.len(),
            Err(i) => i@ <= self@.len(),
        }
    ";

    /// Contract for `[T]::binary_search_by_key`
    ///
    /// Binary search by key extraction. Extracts a key from each element
    /// and searches for a matching key.
    pub const BINARY_SEARCH_BY_KEY: &str = r"
        params: self, b, f
        ensures: match result {
            Ok(i) => i@ < self@.len(),
            Err(i) => i@ <= self@.len(),
        }
    ";

    /// Contract for `[T]::partition_point`
    ///
    /// Returns the index of the partition point according to the given
    /// predicate (the index of the first element for which the predicate
    /// returns false).
    pub const PARTITION_POINT: &str = r"
        params: self, pred
        ensures: result@ <= self@.len()
    ";

    /// Contract for `[T]::len`
    pub const LEN: &str = r"
        ensures: result@ == self@.len()
    ";

    /// Contract for `[T]::is_empty`
    pub const IS_EMPTY: &str = r"
        ensures: result == (self@.len() == 0)
    ";

    /// Contract for `[T]::get`
    pub const GET: &str = r"
        params: self, index
        ensures: match result {
            Some(v) => index@ < self@.len() && *v == self@[index@],
            None => index@ >= self@.len(),
        }
    ";

    /// Contract for `[T]::first`
    pub const FIRST: &str = r"
        ensures: match result {
            Some(v) => self@.len() > 0 && *v == self@.index_logic(0),
            None => self@.len() == 0,
        }
    ";

    /// Contract for `[T]::last`
    pub const LAST: &str = r"
        ensures: match result {
            Some(v) => self@.len() > 0 && *v == self@[self@.len() - 1],
            None => self@.len() == 0,
        }
    ";

    /// Contract for `[T]::contains`
    pub const CONTAINS: &str = r"
        params: self, x
        ensures: result == exists<i: Int> 0 <= i && i < self@.len() && self@[i] == *x
    ";

    /// Contract for Index trait on slices: `slice[index]`
    pub const INDEX: &str = r"
        params: self, index
        requires: index@ < self@.len()
        ensures: *result == self@[index@]
    ";

    /// Contract for `IndexMut` trait on slices: `slice[index] = value`
    ///
    /// Same as `Vec::INDEX_MUT`: must specify final-state postconditions for
    /// the write-through-reference to be connected to the slice's final view.
    pub const INDEX_MUT: &str = r"
        params: self, index
        requires: index@ < self@.len()
        ensures: *result == self@[index@]
        ensures: (^self)@[index@] == ^result
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i != index@ && i < self@.len() ==>
            (^self)@[i] == self@[i]
    ";

    // ── Generic SliceIndexSpec-based contracts ──────────────────────────
    //
    // These use the `ix.in_bounds(self@)` / `ix.has_value(self@, ...)`
    // / `ix.resolve_elsewhere(...)` predicate surface from `SliceIndexSpec`.
    // They apply to any index type (`usize`, `Range<usize>`, etc.) and
    // are the target contract shape for the unified Vec/slice indexing
    // surface. The existing scalar-only INDEX/INDEX_MUT above are kept
    // for backward compatibility.

    /// Generic Index contract via `SliceIndexSpec` predicates.
    ///
    /// Works for both scalar (`usize`) and range index types.
    pub const INDEX_GENERIC: &str = r"
        params: self, ix
        requires: ix.in_bounds(self@)
        ensures: ix.has_value(self@, result)
    ";

    /// Generic IndexMut contract via `SliceIndexSpec` predicates.
    ///
    /// Includes final-state postconditions and frame condition.
    pub const INDEX_MUT_GENERIC: &str = r"
        params: self, ix
        requires: ix.in_bounds(self@)
        ensures: ix.has_value(self@, result)
        ensures: ix.has_value((^self)@, ^result)
        ensures: ix.resolve_elsewhere(self@, (^self)@)
        ensures: (^self)@.len() == self@.len()
    ";

    /// Generic `get` contract via `SliceIndexSpec` predicates.
    ///
    /// Returns `Some(r)` if in-bounds, `None` otherwise.
    pub const GET_GENERIC: &str = r"
        params: self, ix
        ensures: ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)
        ensures: !ix.in_bounds(self@) ==> result == None
    ";

    /// Generic `get_mut` contract via `SliceIndexSpec` predicates.
    ///
    /// Includes final-state postconditions and frame condition.
    pub const GET_MUT_GENERIC: &str = r"
        params: self, ix
        ensures: ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)
        ensures: ix.in_bounds(self@) ==> ix.has_value((^self)@, ^result)
        ensures: ix.in_bounds(self@) ==> ix.resolve_elsewhere(self@, (^self)@)
        ensures: ix.in_bounds(self@) ==> (^self)@.len() == self@.len()
        ensures: !ix.in_bounds(self@) ==> result == None
    ";

    /// Contract for `[T]::split_at`
    ///
    /// Divides one slice into two at an index, returning `(&[T], &[T])`.
    pub const SPLIT_AT: &str = r"
        params: self, mid
        requires: mid@ <= self@.len()
        ensures: result.0@.len() == mid@
        ensures: result.1@.len() == self@.len() - mid@
    ";

    /// Contract for `[T]::split_at_mut`
    ///
    /// Divides one mutable slice into two at an index.
    pub const SPLIT_AT_MUT: &str = r"
        params: self, mid
        requires: mid@ <= self@.len()
        ensures: result.0@.len() == mid@
        ensures: result.1@.len() == self@.len() - mid@
    ";

    /// Contract for `[T]::windows`
    ///
    /// Returns an iterator over overlapping windows of length `size`.
    /// Panics if `size` is 0.
    pub const WINDOWS: &str = r"
        params: self, size
        requires: size@ > 0
    ";

    /// Contract for `[T]::chunks`
    ///
    /// Returns an iterator over non-overlapping chunks of length `chunk_size`.
    /// Panics if `chunk_size` is 0.
    pub const CHUNKS: &str = r"
        params: self, chunk_size
        requires: chunk_size@ > 0
    ";

    /// Contract for `[T]::iter`
    ///
    /// Returns an iterator over the slice.
    pub const ITER: &str = r"
        ensures: result@ == self@
    ";

    /// Contract for `[T]::iter_mut`
    ///
    /// Returns a mutable iterator over the slice.
    pub const ITER_MUT: &str = r"
        ensures: result@ == self@
    ";

    /// Contract for `[T]::split_first`
    ///
    /// Returns the first and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    pub const SPLIT_FIRST: &str = r"
        ensures: self@.len() == 0 ==> result == None
        ensures: self@.len() > 0 ==> result.is_some()
    ";

    /// Contract for `[T]::split_last`
    ///
    /// Returns the last and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    pub const SPLIT_LAST: &str = r"
        ensures: self@.len() == 0 ==> result == None
        ensures: self@.len() > 0 ==> result.is_some()
    ";

    /// Contract for `[T]::copy_from_slice`
    ///
    /// Copies elements from `src` into `self`. Panics if lengths differ.
    pub const COPY_FROM_SLICE: &str = r"
        params: self, src
        requires: self@.len() == src@.len()
        ensures: (^self)@ == src@
    ";

    /// Contract for `[T]::sort_by`
    ///
    /// Sorts the slice with a comparator function. Only preserves length.
    pub const SORT_BY: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::sort_by_key`
    ///
    /// Sorts the slice by a key extraction function. Only preserves length.
    pub const SORT_BY_KEY: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::sort_unstable_by`
    ///
    /// Sorts the slice with a comparator (unstable). Only preserves length.
    pub const SORT_UNSTABLE_BY: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::sort_unstable_by_key`
    ///
    /// Sorts the slice by a key extraction function (unstable). Only preserves length.
    pub const SORT_UNSTABLE_BY_KEY: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::rotate_left`
    ///
    /// Rotates the slice in-place. Preserves length.
    pub const ROTATE_LEFT: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::rotate_right`
    ///
    /// Rotates the slice in-place. Preserves length.
    pub const ROTATE_RIGHT: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::fill`
    ///
    /// Fills the slice with a given value. Preserves length.
    pub const FILL: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::split_first_mut`
    ///
    /// Returns mutable references to the first element and the rest of the slice,
    /// or `None` if it is empty.
    pub const SPLIT_FIRST_MUT: &str = r#"
        ensures: match result {
            Some((first, rem)) => {
                *first == self@.index_logic(0) &&
                ^first == (^self)@.index_logic(0) &&
                self@.len() > 0 &&
                (^self)@.len() > 0 &&
                (*rem)@ == self@.tail() &&
                (^rem)@ == (^self)@.tail()
            }
            None => self@.len() == 0 && (^self)@ == self@ && self@ == Seq::empty()
        }
    "#;

    /// Contract for `[T]::split_last_mut`
    ///
    /// Returns mutable references to the last element and the rest of the slice,
    /// or `None` if it is empty.
    pub const SPLIT_LAST_MUT: &str = r"
        ensures: self@.len() == 0 ==> result == None
        ensures: self@.len() > 0 ==> result.is_some()
    ";

    /// Contract for `[T]::first_mut`
    ///
    /// Returns a mutable reference to the first element, if any.
    pub const FIRST_MUT: &str = r#"
        ensures: match result {
            Some(r) => self@.len() > 0 && *r == self@.index_logic(0),
            None => self@.len() == 0,
        }
    "#;

    /// Contract for `[T]::last_mut`
    ///
    /// Returns a mutable reference to the last element, if any.
    pub const LAST_MUT: &str = r#"
        ensures: match result {
            Some(r) => self@.len() > 0 && *r == self@.index_logic(self@.len() - 1),
            None => self@.len() == 0,
        }
    "#;

    /// Contract for `[T]::swap`
    ///
    /// Swaps two elements in the slice. The `exchange` clause (and the
    /// pointwise-frame clause) name the swap relation so the
    /// permutation/exchange axiom bundle can chain a swap site into a loop's
    /// `permutation_of` invariant. (Sorting Stage A; matches Creusot's
    /// `(^self)@.exchange(self@, i@, j@)`.)
    pub const SWAP: &str = r"
        params: self, a, b
        requires: a@ < self@.len()
        requires: b@ < self@.len()
        ensures: (^self)@.len() == self@.len()
        ensures: (^self)@.index_logic(a@) == self@.index_logic(b@)
        ensures: (^self)@.index_logic(b@) == self@.index_logic(a@)
        ensures: forall<i: Int> 0 <= i && i < self@.len() && i != a@ && i != b@ ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: (^self)@.exchange(self@, a@, b@)
    ";

    /// Contract for `[T]::reverse`
    ///
    /// Reverses the order of elements in the slice, in place.
    pub const REVERSE: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::sort`
    ///
    /// Sorts the slice in ascending order. Preserves length.
    pub const SORT: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::sort_unstable`
    ///
    /// Sorts the slice in ascending order (unstable). Preserves length.
    pub const SORT_UNSTABLE: &str = r"
        ensures: (^self)@.len() == self@.len()
    ";

    /// Contract for `[T]::dedup`
    ///
    /// Removes consecutive repeated elements. Only preserves len <= old len.
    pub const DEDUP: &str = r"
        ensures: (^self)@.len() <= self@.len()
    ";

    /// Contract for `[T]::iter`
    ///
    /// Returns an iterator over the slice (also handles bare [T]::iter path).
    pub const ITER_BARE: &str = r"
        ensures: result@ == self@
    ";

    /// Contract for `[T]::iter_mut`
    ///
    /// Returns a mutable iterator over the slice (also handles bare [T]::iter_mut path).
    pub const ITER_MUT_BARE: &str = r"
        ensures: result@ == self@
    ";
}

#[cfg(test)]
mod tests {
    use super::{super::test_shim, SliceExt};
    use crate::logic::Int;

    #[test]
    fn test_binary_search_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BINARY_SEARCH);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("match result"));
    }

    #[test]
    fn test_len_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::LEN);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.len()"));
    }

    #[test]
    fn test_is_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::IS_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.len() == 0"));
    }

    #[test]
    fn test_get_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GET);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("match result"));
    }

    #[test]
    fn test_first_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FIRST);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.index_logic(0)"));
    }

    #[test]
    fn test_last_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::LAST);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.len() - 1"));
    }

    #[test]
    fn test_contains_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CONTAINS);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("exists"));
    }

    #[test]
    fn test_index_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::INDEX);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("index@"));
        assert!(spec.ensures[0].contains("self@[index@]"));
    }

    #[test]
    fn test_index_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::INDEX_MUT);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 4);
        assert!(spec.requires[0].contains("index@"));
        assert!(spec.ensures[0].contains("self@[index@]"));
        assert!(spec.ensures[1].contains("(^self)@[index@]"));
        assert!(spec.ensures[2].contains("(^self)@.len()"));
        assert!(spec.ensures[3].contains("forall"));
    }

    // ── Generic spec string parse tests ─────────────────────────────

    #[test]
    fn test_index_generic_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::INDEX_GENERIC);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("ix.in_bounds"));
        assert!(spec.ensures[0].contains("ix.has_value"));
    }

    #[test]
    fn test_index_mut_generic_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::INDEX_MUT_GENERIC);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 4);
        assert!(spec.requires[0].contains("ix.in_bounds"));
        assert!(spec.ensures[0].contains("ix.has_value(self@, result)"));
        assert!(spec.ensures[1].contains("ix.has_value((^self)@"));
        assert!(spec.ensures[2].contains("ix.resolve_elsewhere"));
        assert!(spec.ensures[3].contains("(^self)@.len()"));
    }

    #[test]
    fn test_get_generic_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GET_GENERIC);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.ensures[0].contains("ix.in_bounds"));
        assert!(spec.ensures[0].contains("ix.has_value"));
        assert!(spec.ensures[1].contains("!ix.in_bounds"));
        assert!(spec.ensures[1].contains("None"));
    }

    #[test]
    fn test_get_mut_generic_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GET_MUT_GENERIC);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 5);
        assert!(spec.ensures[0].contains("ix.has_value(self@, r)"));
        assert!(spec.ensures[1].contains("ix.has_value((^self)@"));
        assert!(spec.ensures[2].contains("ix.resolve_elsewhere"));
        assert!(spec.ensures[3].contains("(^self)@.len()"));
        assert!(spec.ensures[4].contains("None"));
    }

    // ── SliceIndexSpec runtime behavior tests ───────────────────────

    #[test]
    fn test_usize_in_bounds() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!(2_usize.in_bounds(&seq));
        assert!(!3_usize.in_bounds(&seq));
        assert!(!100_usize.in_bounds(&seq));
    }

    #[test]
    fn test_usize_has_value() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!(1_usize.has_value(&seq, &20));
        assert!(!1_usize.has_value(&seq, &10));
    }

    #[test]
    fn test_range_in_bounds() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30, 40]);
        assert!((1..3).in_bounds(&seq));
        assert!((0..4).in_bounds(&seq));
        assert!((0..0).in_bounds(&seq));
        assert!(!(0..5).in_bounds(&seq));
        #[allow(clippy::reversed_empty_ranges)] // Intentionally testing reversed range is rejected
        {
            assert!(!(3..2).in_bounds(&seq));
        }
    }

    #[test]
    fn test_range_has_value() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30, 40]);
        let sub = Seq::from(vec![20, 30]);
        assert!((1..3).has_value(&seq, &sub));
        let wrong = Seq::from(vec![10, 20]);
        assert!(!(1..3).has_value(&seq, &wrong));
    }

    #[test]
    fn test_range_to_in_bounds() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!((..2).in_bounds(&seq));
        assert!((..3).in_bounds(&seq));
        assert!(!(..4).in_bounds(&seq));
    }

    #[test]
    fn test_range_from_in_bounds() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!((1..).in_bounds(&seq));
        assert!((3..).in_bounds(&seq));
        assert!(!(4..).in_bounds(&seq));
    }

    #[test]
    fn test_range_full_in_bounds() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!((..).in_bounds(&seq));
        let empty: Seq<i32> = Seq::empty();
        assert!((..).in_bounds(&empty));
    }

    #[test]
    fn test_range_full_has_value() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!((..).has_value(&seq, &seq));
    }

    #[test]
    fn test_range_to_inclusive_in_bounds() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30]);
        assert!((..=1).in_bounds(&seq));
        assert!((..=2).in_bounds(&seq));
        assert!(!(..=3).in_bounds(&seq));
    }

    #[test]
    fn test_range_to_inclusive_has_value() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let seq = Seq::from(vec![10, 20, 30, 40]);
        let sub = Seq::from(vec![10, 20]);
        assert!((..=1).has_value(&seq, &sub));
    }

    #[test]
    fn test_resolve_elsewhere_usize() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let old = Seq::from(vec![10, 20, 30]);
        let fin = Seq::from(vec![10, 99, 30]);
        assert!(1_usize.resolve_elsewhere(&old, &fin));
        assert!(!0_usize.resolve_elsewhere(&old, &fin));
    }

    #[test]
    fn test_resolve_elsewhere_range() {
        use super::SliceIndexSpec;
        use crate::logic::Seq;
        let old = Seq::from(vec![10, 20, 30, 40]);
        let fin = Seq::from(vec![10, 99, 88, 40]);
        assert!((1..3).resolve_elsewhere(&old, &fin));
        assert!(!(0..2).resolve_elsewhere(&old, &fin));
    }

    #[test]
    fn test_to_ref_seq() {
        let arr = [1_i32, 2, 3];
        let seq = arr.as_slice().to_ref_seq();
        assert_eq!(seq.len(), Int::from(arr.len()));
        assert_eq!(seq.get(Int::from(1_usize)), Some(&arr[1]));
    }

    #[test]
    fn test_to_mut_seq_len() {
        let mut arr = [1_i32, 2, 3];
        let seq = arr.as_mut_slice().to_mut_seq();
        assert_eq!(seq.len(), Int::from(arr.len()));
    }

    // ── New spec string parse tests ─────────────────────────────────

    #[test]
    fn test_split_at_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SPLIT_AT);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.requires[0].contains("mid@"));
    }

    #[test]
    fn test_split_at_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SPLIT_AT_MUT);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.requires[0].contains("mid@"));
    }

    #[test]
    fn test_windows_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WINDOWS);
        assert_eq!(spec.requires.len(), 1);
        assert!(spec.requires[0].contains("size@"));
        assert!(spec.ensures.is_empty());
    }

    #[test]
    fn test_chunks_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHUNKS);
        assert_eq!(spec.requires.len(), 1);
        assert!(spec.requires[0].contains("chunk_size@"));
        assert!(spec.ensures.is_empty());
    }

    #[test]
    fn test_slice_iter_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ITER);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@"));
    }

    #[test]
    fn test_slice_iter_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ITER_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@"));
    }

    #[test]
    fn test_split_first_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SPLIT_FIRST);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_split_last_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SPLIT_LAST);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_copy_from_slice_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::COPY_FROM_SLICE);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("self@.len()"));
        assert!(spec.ensures[0].contains("src@"));
    }

    #[test]
    fn test_split_first_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SPLIT_FIRST_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.tail()"));
    }

    #[test]
    fn test_split_last_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SPLIT_LAST_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_first_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FIRST_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.index_logic(0)"));
    }

    #[test]
    fn test_last_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::LAST_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.len() - 1"));
    }

    #[test]
    fn test_swap_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SWAP);
        assert_eq!(spec.requires.len(), 2);
        // len, swap a->b, swap b->a, pointwise frame, exchange bridge.
        assert_eq!(spec.ensures.len(), 5);
        assert!(spec.requires[0].contains("a@"));
        assert!(spec.ensures[0].contains("(^self)@.len()"));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("(^self)@.exchange(self@, a@, b@)")));
    }

    #[test]
    fn test_reverse_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::REVERSE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("(^self)@.len()"));
    }

    #[test]
    fn test_sort_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SORT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("(^self)@.len()"));
    }

    #[test]
    fn test_sort_unstable_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SORT_UNSTABLE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("(^self)@.len()"));
    }

    #[test]
    fn test_dedup_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::DEDUP);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("(^self)@.len()"));
    }

    #[test]
    fn test_binary_search_by_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BINARY_SEARCH_BY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("match result"));
    }

    #[test]
    fn test_binary_search_by_key_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BINARY_SEARCH_BY_KEY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("match result"));
    }

    #[test]
    fn test_partition_point_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::PARTITION_POINT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@.len()"));
    }
}
