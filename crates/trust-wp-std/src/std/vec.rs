// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::vec::Vec<T>`
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These specifications define the contract semantics for Vec methods.
//! trust-wp-driver uses these specs when verifying code that uses Vec.
//!
//! Reference: Creusot's `creusot-std/src/std/vec.rs`
//!
//! ## Design Notes
//!
//! `Vec<T>` views as `Seq<T>` (logical sequence) for verification purposes.
//! The view relationship is: `vec@` produces a `Seq<T>` with the same elements.
//!
//! Key notation:
//! - `self@` - view of the current state (Vec → Seq)
//! - `(^self)@` - view of the final/resulting state (after mutable borrow resolves)
//! - `old(x)` - value of x at function entry

// Allow raw string hashes for spec string literals (consistency over optimization)
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown pedantic warnings for contract notation
#![allow(clippy::doc_markdown)]

use crate::logic::Seq;

/// Specification trait for `Vec<T>` methods (internal).
///
/// This trait documents the contracts for Vec methods using Seq as the
/// logical model. **Users should call standard `Vec` methods directly** —
/// trust-wp-driver resolves these specs internally via the `std_specs` module.
/// The `_spec()` methods here are for testing trust-wp-std itself.
///
/// # View Trait
///
/// The [`View`](crate::logic::View) trait is the preferred way to convert
/// `Vec<T>` to its logical model `Seq<T>`. The `VecSpec::view_spec()` method
/// is kept for backwards compatibility and convenience (takes `&self`).
///
/// ```text
/// use trust_wp_std::prelude::*;
///
/// // Using View trait (preferred)
/// let seq: Seq<i32> = view(vec![1, 2, 3]);
///
/// // Using VecSpec trait
/// let seq: Seq<i32> = vec![1, 2, 3].view_spec();
/// ```
///
/// # Specifications
///
/// ## View relationship
/// ```text
/// impl<T: Clone> View for Vec<T> {
///     type ViewTy = Seq<T>;
///     fn view(self) -> Seq<T>;
/// }
/// ```
///
/// ## new
/// ```text
/// #[ensures(result@.len() == 0)]
/// fn new() -> Vec<T>;
/// ```
///
/// ## len
/// ```text
/// #[ensures(result@ == self@.len())]
/// fn len(&self) -> usize;
/// ```
///
/// ## is_empty
/// ```text
/// #[ensures(result == (self@.len() == 0))]
/// fn is_empty(&self) -> bool;
/// ```
///
/// ## push
/// ```text
/// #[ensures((^self)@ == self@.push_back(value))]
/// fn push(&mut self, value: T);
/// ```
///
/// ## pop
/// ```text
/// #[ensures(match result {
///     Some(t) => {
///         self@.len() > 0 &&
///         self@ == (^self)@.push_back(t)
///     },
///     None => self@.len() == 0 && (^self)@ == self@
/// })]
/// fn pop(&mut self) -> Option<T>;
/// ```
///
/// ## get
/// ```text
/// #[ensures(match result {
///     Some(r) => index@ < self@.len() && *r == self@.index_logic(index@),
///     None => index@ >= self@.len()
/// })]
/// fn get(&self, index: usize) -> Option<&T>;
/// ```
///
/// ## first / last
/// ```text
/// #[ensures(match result {
///     Some(r) => self@.len() > 0 && *r == self@.index_logic(0),
///     None => self@.len() == 0
/// })]
/// fn first(&self) -> Option<&T>;
///
/// #[ensures(match result {
///     Some(r) => self@.len() > 0 && *r == self@.index_logic(self@.len() - 1),
///     None => self@.len() == 0
/// })]
/// fn last(&self) -> Option<&T>;
/// ```
pub trait VecSpec<T> {
    /// Get the logical view of this Vec as a Seq.
    fn view_spec(&self) -> Seq<T>
    where
        T: Clone;

    /// Specification: result@ == self@.len()
    fn len_spec(&self) -> usize;

    /// Specification: result == (self@.len() == 0)
    fn is_empty_spec(&self) -> bool;

    /// Specification: (^self)@ == self@.push_back(value)
    fn push_spec(&mut self, value: T);

    /// Specification: match result { Some(t) => self@ == (^self)@.push_back(t), None => ... }
    fn pop_spec(&mut self) -> Option<T>;

    /// Specification: ensures(self@.len() == 0)
    fn clear_spec(&mut self);

    /// Specification: first element if non-empty
    fn first_spec(&self) -> Option<&T>;

    /// Specification: last element if non-empty
    fn last_spec(&self) -> Option<&T>;

    /// Specification: get element by index
    fn get_spec(&self, index: usize) -> Option<&T>;

    /// Specification: get mutable element by index
    fn get_mut_spec(&mut self, index: usize) -> Option<&mut T>;

    /// Specification: capacity is at least len
    fn capacity_spec(&self) -> usize;

    /// Specification: reserve preserves elements
    fn reserve_spec(&mut self, additional: usize);

    /// Specification: shrink_to_fit preserves elements
    fn shrink_to_fit_spec(&mut self);

    /// Specification: truncate to len
    fn truncate_spec(&mut self, len: usize);

    /// Specification: resize to new_len, filling with value
    fn resize_spec(&mut self, new_len: usize, value: T)
    where
        T: Clone;

    /// Specification: insert element at index
    fn insert_spec(&mut self, index: usize, element: T);

    /// Specification: remove element at index
    fn remove_spec(&mut self, index: usize) -> T;

    /// Specification: swap two elements
    ///
    /// ```text
    /// #[requires(a@ < self@.len())]
    /// #[requires(b@ < self@.len())]
    /// #[ensures((^self)@.len() == self@.len())]
    /// #[ensures((^self)@.index_logic(a@) == self@.index_logic(b@))]
    /// #[ensures((^self)@.index_logic(b@) == self@.index_logic(a@))]
    /// #[ensures(forall<i: Int> 0 <= i && i < self@.len() && i != a@ && i != b@ ==>
    ///     (^self)@.index_logic(i) == self@.index_logic(i))]
    /// fn swap(&mut self, a: usize, b: usize);
    /// ```
    fn swap_spec(&mut self, a: usize, b: usize);

    /// Specification: check if element exists
    ///
    /// ```text
    /// #[ensures(result == exists<i: Int> 0 <= i && i < self@.len() &&
    ///     self@.index_logic(i) == *x)]
    /// fn contains(&self, x: &T) -> bool;
    /// ```
    fn contains_spec(&self, x: &T) -> bool
    where
        T: PartialEq;
}

impl<T> VecSpec<T> for Vec<T> {
    fn view_spec(&self) -> Seq<T>
    where
        T: Clone,
    {
        Seq::from(self.clone())
    }

    fn len_spec(&self) -> usize {
        self.len()
    }

    fn is_empty_spec(&self) -> bool {
        self.is_empty()
    }

    fn push_spec(&mut self, value: T) {
        self.push(value);
    }

    fn pop_spec(&mut self) -> Option<T> {
        self.pop()
    }

    fn clear_spec(&mut self) {
        self.clear();
    }

    fn first_spec(&self) -> Option<&T> {
        self.first()
    }

    fn last_spec(&self) -> Option<&T> {
        self.last()
    }

    fn get_spec(&self, index: usize) -> Option<&T> {
        self.get(index)
    }

    fn get_mut_spec(&mut self, index: usize) -> Option<&mut T> {
        self.get_mut(index)
    }

    fn capacity_spec(&self) -> usize {
        self.capacity()
    }

    fn reserve_spec(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn shrink_to_fit_spec(&mut self) {
        self.shrink_to_fit();
    }

    fn truncate_spec(&mut self, len: usize) {
        self.truncate(len);
    }

    fn resize_spec(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        self.resize(new_len, value);
    }

    fn insert_spec(&mut self, index: usize, element: T) {
        self.insert(index, element);
    }

    fn remove_spec(&mut self, index: usize) -> T {
        self.remove(index)
    }

    fn swap_spec(&mut self, a: usize, b: usize) {
        self.swap(a, b);
    }

    fn contains_spec(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        self.contains(x)
    }
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
///
/// These are structured as data that the driver can query.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Vec::new`
    pub const NEW: &str = r#"
        ensures: result@.len() == 0
    "#;

    /// Contract for `Vec::len`
    pub const LEN: &str = r#"
        ensures: result@ == self@.len()
    "#;

    /// Contract for `Vec::is_empty`
    pub const IS_EMPTY: &str = r#"
        ensures: result == (self@.len() == 0)
    "#;

    /// Contract for `Vec::push`
    pub const PUSH: &str = r#"
        ensures: (^self)@ == self@.push_back(value)
    "#;

    /// Contract for `Vec::pop`
    pub const POP: &str = r#"
        ensures: match result {
            Some(t) => self@.len() > 0 && self@ == (^self)@.push_back(t),
            None => self@.len() == 0 && (^self)@ == self@,
        }
    "#;

    /// Contract for `Vec::clear`
    pub const CLEAR: &str = r#"
        ensures: (^self)@.len() == 0
    "#;

    /// Contract for `Vec::first`
    pub const FIRST: &str = r#"
        ensures: match result {
            Some(r) => self@.len() > 0 && *r == self@[0],
            None => self@.len() == 0,
        }
    "#;

    /// Contract for `Vec::last`
    pub const LAST: &str = r#"
        ensures: match result {
            Some(r) => self@.len() > 0 && *r == self@[self@.len() - 1],
            None => self@.len() == 0,
        }
    "#;

    /// Contract for `Vec::get`
    pub const GET: &str = r#"
        params: self, index
        ensures: match result {
            Some(r) => index@ < self@.len() && *r == self@.index_logic(index@),
            None => index@ >= self@.len(),
        }
    "#;

    /// Contract for `Vec::capacity`
    pub const CAPACITY: &str = r#"
        ensures: result@ >= self@.len()
    "#;

    /// Contract for `Vec::reserve`
    pub const RESERVE: &str = r#"
        params: self, additional
        ensures: (^self)@ == self@
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: (^self).capacity()@ >= self@.len() + additional@
    "#;

    /// Contract for `Vec::reserve_exact`
    pub const RESERVE_EXACT: &str = r#"
        params: self, additional
        ensures: (^self)@ == self@
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: (^self).capacity()@ >= self@.len() + additional@
    "#;

    /// Contract for `Vec::with_capacity`
    pub const WITH_CAPACITY: &str = r#"
        params: capacity
        ensures: result@.len() == 0
        ensures: result.capacity()@ >= capacity@
    "#;

    /// Contract for `Vec::truncate`
    pub const TRUNCATE: &str = r#"
        params: self, len
        ensures: if len@ < self@.len() {
            (^self)@.len() == len@ &&
            forall<i: Int> 0 <= i && i < len@ ==> (^self)@.index_logic(i) == self@.index_logic(i)
        } else {
            (^self)@ == self@
        }
    "#;

    /// Contract for `Vec::insert`
    pub const INSERT: &str = r#"
        params: self, index, element
        requires: index@ <= self@.len()
        ensures: (^self)@.len() == self@.len() + 1
        ensures: (^self)@.index_logic(index@) == element
        ensures: forall<i: Int> 0 <= i && i < index@ ==> (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: forall<i: Int> index@ < i && i < (^self)@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i - 1)
    "#;

    /// Contract for `Vec::remove`
    pub const REMOVE: &str = r#"
        params: self, index
        requires: index@ < self@.len()
        ensures: result == self@.index_logic(index@)
        ensures: (^self)@.len() == self@.len() - 1
        ensures: forall<i: Int> 0 <= i && i < index@ ==> (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: forall<i: Int> index@ <= i && i < (^self)@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i + 1)
    "#;

    /// Contract for `Vec::get_mut`
    pub const GET_MUT: &str = r#"
        params: self, index
        ensures: match result {
            Some(r) => index@ < self@.len() && *r == self@.index_logic(index@),
            None => index@ >= self@.len(),
        }
    "#;

    /// Contract for Index trait: `vec[index]`
    pub const INDEX: &str = r#"
        params: self, index
        requires: index@ < self@.len()
        ensures: *result == self@.index_logic(index@)
    "#;

    /// Contract for IndexMut trait: `vec[index] = value`
    ///
    /// In addition to the read-only Index postcondition (*result == initial element),
    /// IndexMut must specify:
    /// - The final view's element at `index` equals the final value of the returned reference
    /// - The frame condition: all other indices are unchanged
    /// - Length is preserved
    ///
    /// Without these, the solver has no connection between writing through the
    /// returned `&mut T` and the Vec's final Seq view, causing `unknown (incomplete)`
    /// results. See Creusot's `IndexMut` spec for the reference pattern.
    pub const INDEX_MUT: &str = r#"
        params: self, index
        requires: index@ < self@.len()
        ensures: *result == self@.index_logic(index@)
        ensures: (^self)@.index_logic(index@) == ^result
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i != index@ && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
    "#;

    /// Contract for `Vec::shrink_to_fit`
    pub const SHRINK_TO_FIT: &str = r#"
        ensures: (^self)@ == self@
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: (^self).capacity()@ >= self@.len()
    "#;

    /// Contract for `Vec::shrink_to`
    pub const SHRINK_TO: &str = r#"
        ensures: (^self)@ == self@
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: (^self).capacity()@ >= (^self)@.len()
    "#;

    /// Contract for `Vec::resize` (with Clone value)
    pub const RESIZE: &str = r#"
        params: self, new_len, value
        ensures: (^self)@.len() == new_len@
        ensures: forall<i: Int> 0 <= i && i < min(new_len@, self@.len()) ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: forall<i: Int> self@.len() <= i && i < new_len@ ==>
            (^self)@.index_logic(i) == value
    "#;

    /// Contract for `Vec::swap`
    ///
    /// The final `exchange` clause names the already-asserted pointwise swap
    /// relation as `exchange`, so the permutation/exchange axiom bundle
    /// (`exchange ==> permutation_of`) can chain a swap site into a loop's
    /// `permutation_of` invariant. (Sorting Stage A.)
    pub const SWAP: &str = r#"
        params: self, a, b
        requires: a@ < self@.len()
        requires: b@ < self@.len()
        ensures: (^self)@.len() == self@.len()
        ensures: (^self)@.index_logic(a@) == self@.index_logic(b@)
        ensures: (^self)@.index_logic(b@) == self@.index_logic(a@)
        ensures: forall<i: Int> 0 <= i && i < self@.len() && i != a@ && i != b@ ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: (^self)@.exchange(self@, a@, b@)
    "#;

    /// Contract for `Vec::contains`
    pub const CONTAINS: &str = r#"
        params: self, x
        ensures: result == exists<i: Int> 0 <= i && i < self@.len() &&
            self@.index_logic(i) == *x
    "#;

    /// Contract for `Vec::extend_from_slice`
    ///
    /// Appends all elements from the slice to the vec. The resulting vec
    /// has length equal to old length + slice length, with old elements
    /// preserved and new elements appended in order.
    pub const EXTEND_FROM_SLICE: &str = r#"
        params: self, other
        ensures: (^self)@.len() == self@.len() + other@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: forall<i: Int> 0 <= i && i < other@.len() ==>
            (^self)@.index_logic(self@.len() + i) == other@.index_logic(i)
    "#;

    /// Contract for `Vec::extend` (Extend trait impl)
    ///
    /// Extends the vector with the contents of an iterator. We only
    /// guarantee that old elements are preserved (length may grow by
    /// any amount depending on the iterator).
    pub const EXTEND: &str = r#"
        params: self, iter
        ensures: (^self)@.len() >= self@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
    "#;

    // ── Generic SliceIndexSpec-based contracts ──────────────────────────
    //
    // These use the `ix.in_bounds(self@)` / `ix.has_value(self@, ...)`
    // / `ix.resolve_elsewhere(...)` predicate surface from `SliceIndexSpec`.
    // Semantically identical to `slice::specs::*_GENERIC` but provided
    // here for completeness (Vec deref-coerces to slice for indexing).
    //
    // See: `crate::std::slice::SliceIndexSpec`

    /// Generic Index contract for Vec via `SliceIndexSpec`.
    pub const INDEX_GENERIC: &str = r#"
        params: self, ix
        requires: ix.in_bounds(self@)
        ensures: ix.has_value(self@, result)
    "#;

    /// Generic IndexMut contract for Vec via `SliceIndexSpec`.
    pub const INDEX_MUT_GENERIC: &str = r#"
        params: self, ix
        requires: ix.in_bounds(self@)
        ensures: ix.has_value(self@, result)
        ensures: ix.has_value((^self)@, ^result)
        ensures: ix.resolve_elsewhere(self@, (^self)@)
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Generic `Vec::get` contract via `SliceIndexSpec`.
    pub const GET_GENERIC: &str = r#"
        params: self, ix
        ensures: ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)
        ensures: !ix.in_bounds(self@) ==> result == None
    "#;

    /// Generic `Vec::get_mut` contract via `SliceIndexSpec`.
    pub const GET_MUT_GENERIC: &str = r#"
        params: self, ix
        ensures: ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)
        ensures: ix.in_bounds(self@) ==> ix.has_value((^self)@, ^result)
        ensures: ix.in_bounds(self@) ==> ix.resolve_elsewhere(self@, (^self)@)
        ensures: ix.in_bounds(self@) ==> (^self)@.len() == self@.len()
        ensures: !ix.in_bounds(self@) ==> result == None
    "#;

    /// Contract for `Vec::append`
    ///
    /// Moves all elements from `other` into `self`, leaving `other` empty.
    pub const APPEND: &str = r#"
        params: self, other
        ensures: (^self)@.len() == self@.len() + other@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: forall<i: Int> 0 <= i && i < other@.len() ==>
            (^self)@.index_logic(self@.len() + i) == other@.index_logic(i)
        ensures: (^other)@.len() == 0
    "#;

    /// Contract for `Vec::split_off`
    ///
    /// Splits the collection into two at the given index.
    pub const SPLIT_OFF: &str = r#"
        params: self, at
        requires: at@ <= self@.len()
        ensures: (^self)@.len() == at@
        ensures: result@.len() == self@.len() - at@
        ensures: forall<i: Int> 0 <= i && i < at@ ==>
            (^self)@.index_logic(i) == self@.index_logic(i)
        ensures: forall<i: Int> 0 <= i && i < result@.len() ==>
            result@.index_logic(i) == self@.index_logic(at@ + i)
    "#;

    /// Contract for `Vec::retain`
    ///
    /// Retains only the elements specified by the predicate.
    pub const RETAIN: &str = r#"
        params: self, f
        ensures: (^self)@.len() <= self@.len()
    "#;

    /// Contract for `Vec::dedup`
    ///
    /// Removes consecutive repeated elements.
    pub const DEDUP: &str = r#"
        ensures: (^self)@.len() <= self@.len()
    "#;

    /// Contract for `Vec::reverse`
    ///
    /// Reverses the order of elements in-place.
    pub const REVERSE: &str = r#"
        ensures: (^self)@.len() == self@.len()
        ensures: forall<i: Int> 0 <= i && i < self@.len() ==>
            (^self)@.index_logic(i) == self@.index_logic(self@.len() - 1 - i)
    "#;

    /// Contract for `Vec::sort`
    ///
    /// Sorts the slice. Only preserves length.
    pub const SORT: &str = r#"
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Contract for `Vec::sort_unstable`
    ///
    /// Sorts the slice (unstable). Only preserves length.
    pub const SORT_UNSTABLE: &str = r#"
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Contract for `Vec::first_mut`
    ///
    /// Returns a mutable reference to the first element, if any.
    pub const FIRST_MUT: &str = r#"
        ensures: match result {
            Some(r) => self@.len() > 0 && *r == self@.index_logic(0),
            None => self@.len() == 0,
        }
    "#;

    /// Contract for `Vec::last_mut`
    ///
    /// Returns a mutable reference to the last element, if any.
    pub const LAST_MUT: &str = r#"
        ensures: match result {
            Some(r) => self@.len() > 0 && *r == self@.index_logic(self@.len() - 1),
            None => self@.len() == 0,
        }
    "#;

    /// Contract for `Vec::as_slice`
    ///
    /// Returns a slice containing the entire vector.
    pub const AS_SLICE: &str = r#"
        ensures: result@ == self@
    "#;

    /// Contract for `Vec::as_mut_slice`
    ///
    /// Returns a mutable slice of the entire vector.
    pub const AS_MUT_SLICE: &str = r#"
        ensures: result@ == self@
    "#;

    /// Contract for `Vec::swap_remove`
    ///
    /// Removes the element at `index` and replaces it with the last element.
    /// This does not preserve ordering but is O(1).
    pub const SWAP_REMOVE: &str = r#"
        params: self, index
        requires: index@ < self@.len()
        ensures: result == self@[index@]
        ensures: (^self)@.len() == self@.len() - 1
    "#;

    /// Contract for `Vec::sort_by`
    ///
    /// Sorts the slice with a comparator function. Only preserves length.
    pub const SORT_BY: &str = r#"
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Contract for `Vec::sort_by_key`
    ///
    /// Sorts the slice by a key extraction function. Only preserves length.
    pub const SORT_BY_KEY: &str = r#"
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Contract for `Vec::sort_unstable_by`
    ///
    /// Sorts the slice with a comparator (unstable). Only preserves length.
    pub const SORT_UNSTABLE_BY: &str = r#"
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Contract for `Vec::sort_unstable_by_key`
    ///
    /// Sorts the slice by a key extraction function (unstable). Only preserves length.
    pub const SORT_UNSTABLE_BY_KEY: &str = r#"
        ensures: (^self)@.len() == self@.len()
    "#;

    /// Contract for `Vec::from_elem` (used by `vec![val; count]` macro)
    ///
    /// Creates a new Vec with `count` copies of `elem`.
    pub const FROM_ELEM: &str = r#"
        params: elem, count
        ensures: result@.len() == count@
        ensures: forall<i> 0 <= i && i < count@ ==> result@.index_logic(i) == elem
    "#;

    /// Contract for `Vec::drain` — removes a range of elements, returning
    /// a drain iterator. Prevents opaque-call fallback.
    pub const DRAIN: &str = r#"
        params: self, range
    "#;

    /// Contract for `Vec::retain_mut` — retains only elements for which
    /// the predicate returns true. Like retain, but with mutable references.
    pub const RETAIN_MUT: &str = r#"
        params: self, f
        ensures: (^self)@.len() <= self@.len()
    "#;

    /// Contract for `Vec::dedup_by` — removes consecutive duplicates
    /// using a comparison function. Length cannot increase.
    pub const DEDUP_BY: &str = r#"
        params: self, same_bucket
        ensures: (^self)@.len() <= self@.len()
    "#;

    /// Contract for `Vec::dedup_by_key` — removes consecutive duplicates
    /// using a key extraction function. Length cannot increase.
    pub const DEDUP_BY_KEY: &str = r#"
        params: self, key
        ensures: (^self)@.len() <= self@.len()
    "#;

    /// Contract for `Vec::flatten` (via Deref to [T])
    /// Prevents opaque-call fallback for iter-based flatten patterns.
    pub const ITER_FLATTEN_VEC: &str = r#"
        params: self
    "#;
}

#[cfg(test)]
mod tests;
