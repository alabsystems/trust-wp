// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite set type for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `FSet<T>` is a logical finite set type used in specifications and ghost code.
//! Unlike `HashSet`, it has no capacity limits and is designed for verification.
//!
//! At the SMT level, `FSet<T>` is encoded as:
//! - An SMT set `(Set T)` or array `(Array T Bool)` for membership
//! - An SMT integer for cardinality
//!
//! Reference: Creusot's `creusot-std/src/logic/fset.rs`

// Allow cast_sign_loss for Int to usize conversions in runtime model
#![allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
// Allow must_use for builder methods that chain
#![allow(clippy::must_use_candidate)]
// Builder pattern methods returning Self don't need must_use in logical model
#![allow(clippy::return_self_not_must_use)]
// Logical types use by-value semantics to match Creusot's Copy phantom types.
// Parameters are intentionally taken by value even when only used by reference.
#![allow(clippy::needless_pass_by_value)]

use std::{borrow::Borrow, collections::HashSet, hash::Hash};

use super::{Int, Mapping};

/// A finite set type for specifications.
///
/// `FSet<T>` models sets of elements in specifications. Unlike `HashSet`,
/// it is a logical concept with no capacity limits. In contracts:
///
/// ```text
/// #[ensures((^self)@ == self@.insert(v))]
/// fn insert(&mut self, v: T)
/// ```
///
/// Where `@` is the view operator that converts `HashSet<T>` to `FSet<T>`.
#[derive(Debug)]
#[must_use]
pub struct FSet<T> {
    /// Internal storage (for runtime representation in tests)
    set: HashSet<T>,
}

impl<T> FSet<T>
where
    T: Eq + Hash,
{
    /// Create an empty set.
    ///
    /// SMT encoding: `set_len = 0, forall x. !contains(x)`
    pub fn empty() -> Self {
        Self {
            set: HashSet::new(),
        }
    }

    /// Create an empty set (Creusot-compatible alias for [`empty`](Self::empty)).
    pub fn new() -> Self {
        Self::empty()
    }

    /// Unwrap into the inner value (Creusot compatibility).
    ///
    /// In Creusot, this unwraps a `GhostBox<FSet>` into its inner `FSet`.
    /// Here it is an identity operation since `FSet` is not ghost-wrapped.
    pub fn into_inner(self) -> Self {
        self
    }

    /// Get the number of elements in the set.
    ///
    /// SMT encoding: returns `set_len` (cardinality)
    pub fn len(&self) -> Int {
        Int::from(self.set.len())
    }

    /// Check if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    /// Insert an element into the set.
    ///
    /// Returns a new set with the element added.
    ///
    /// SMT encoding:
    /// ```smt
    /// new_set = set_add(set, x)
    /// new_len = if contains(x) then set_len else set_len + 1
    /// ```
    pub fn insert(mut self, x: T) -> Self {
        self.set.insert(x);
        self
    }

    /// Create a set containing only the given element.
    pub fn singleton(x: T) -> Self {
        Self::empty().insert(x)
    }

    /// Remove an element from the set.
    ///
    /// Returns a new set with the element removed.
    ///
    /// SMT encoding:
    /// ```smt
    /// new_set = set_remove(set, x)
    /// new_len = if contains(x) then set_len - 1 else set_len
    /// ```
    pub fn remove(mut self, x: &T) -> Self {
        self.set.remove(x);
        self
    }

    /// Check if the set contains an element.
    ///
    /// SMT encoding: `set_member(x, set)`
    ///
    /// Accepts borrowed membership queries so callers can reuse an existing
    /// value instead of cloning solely to satisfy the logical API.
    pub fn contains<Q>(&self, x: Q) -> bool
    where
        Q: Borrow<T>,
    {
        self.set.contains(x.borrow())
    }

    /// Return the union of two sets.
    ///
    /// An element is in the result if it is in `self` _or_ in `other`.
    ///
    /// SMT encoding: `set_union(self, other)`
    pub fn union(mut self, other: Self) -> Self {
        for x in other.set {
            self.set.insert(x);
        }
        self
    }

    /// Return the intersection of two sets.
    ///
    /// An element is in the result if it is in `self` _and_ in `other`.
    ///
    /// SMT encoding: `set_inter(self, other)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn intersection(self, other: Self) -> Self
    where
        T: Clone,
    {
        Self {
            set: self.set.intersection(&other.set).cloned().collect(),
        }
    }

    /// Return the difference of two sets.
    ///
    /// An element is in the result if it is in `self` but not in `other`.
    ///
    /// SMT encoding: `set_diff(self, other)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn difference(self, other: Self) -> Self
    where
        T: Clone,
    {
        Self {
            set: self.set.difference(&other.set).cloned().collect(),
        }
    }

    /// Check if every element of `self` is in `other`.
    ///
    /// SMT encoding: `forall x. self.contains(x) ==> other.contains(x)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn is_subset(self, other: Self) -> bool {
        self.set.is_subset(&other.set)
    }

    /// Check if every element of `other` is in `self`.
    ///
    /// SMT encoding: `other.is_subset(self)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn is_superset(self, other: Self) -> bool {
        self.set.is_superset(&other.set)
    }

    /// Check if two sets are disjoint (have no elements in common).
    ///
    /// SMT encoding: `forall x. !self.contains(x) || !other.contains(x)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn disjoint(self, other: Self) -> bool {
        self.set.is_disjoint(&other.set)
    }

    /// Get an arbitrary element from the set, returning an owned value.
    ///
    /// Returns `None` if the set is empty.
    /// If the set is nonempty, returns some element (which one is unspecified).
    ///
    /// SMT encoding: `set_pick(set)` (with axiom that result is in set if nonempty)
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn peek(self) -> Option<T>
    where
        T: Clone,
    {
        self.set.iter().next().cloned()
    }

    /// Extensional equality — two sets are `ext_eq` if they contain the same elements.
    ///
    /// `s1.ext_eq(s2)` iff `forall x. s1.contains(x) == s2.contains(x)`.
    ///
    /// This is semantically identical to `PartialEq` for sets, but exists as a
    /// separate method to match Creusot's API where `ext_eq` is an explicit SMT
    /// builtin `set.Fset.(==)`.
    ///
    /// Takes `self` by value to match Creusot's `Copy` `FSet` semantics.
    pub fn ext_eq(self, other: Self) -> bool {
        self.set == other.set
    }

    /// Ghost helper: mutable insert in place.
    pub fn insert_ghost(&mut self, x: T) -> bool {
        self.set.insert(x)
    }

    /// Ghost helper: mutable remove in place.
    pub fn remove_ghost(&mut self, x: &T) -> bool {
        self.set.remove(x)
    }

    /// Ghost helper: contains check by reference.
    pub fn contains_ghost(&self, x: &T) -> bool {
        self.set.contains(x)
    }

    /// Ghost helper: current set cardinality.
    pub fn len_ghost(&self) -> Int {
        Int::from(self.set.len())
    }

    /// Ghost helper: set emptiness.
    pub fn is_empty_ghost(&self) -> bool {
        self.set.is_empty()
    }

    /// Filter elements by a predicate mapping.
    ///
    /// Returns the subset of elements `x` in `self` for which `f.get(x)` is `true`.
    ///
    /// SMT encoding: `set.Fset.filter`
    ///
    /// Creusot: `#[builtin("set.Fset.filter")]`
    pub fn filter(self, f: Mapping<T, bool>) -> Self
    where
        T: Clone,
    {
        let set = self
            .set
            .into_iter()
            .filter(|x| f.clone().get(x.clone()))
            .collect();
        Self { set }
    }

    /// Return the image of the set under a mapping function.
    ///
    /// For each element `x` in `self`, the result contains `f.get(x)`.
    ///
    /// SMT encoding: `set.Fset.map`
    ///
    /// Creusot: wraps the Why3 builtin `set.Fset.map`
    pub fn map<U>(self, f: Mapping<T, U>) -> FSet<U>
    where
        T: Clone,
        U: Eq + Hash + Clone,
    {
        let set = self.set.into_iter().map(|x| f.clone().get(x)).collect();
        FSet { set }
    }

    /// Generalized union — for each element `x` in `self`, compute `f.get(x)`
    /// (an `FSet<U>`), then take the union of all resulting sets.
    ///
    /// This is the set-theory analogue of `flat_map`.
    ///
    /// SMT postcondition:
    /// ```text
    /// forall y. result.contains(y) == exists x. self.contains(x) && f.get(x).contains(y)
    /// ```
    ///
    /// Creusot: defined recursively via `peek`/`remove`
    pub fn unions<U>(self, f: Mapping<T, FSet<U>>) -> FSet<U>
    where
        T: Clone,
        U: Eq + Hash + Clone,
    {
        let mut result = HashSet::new();
        for x in self.set {
            let mapped_set = f.clone().get(x);
            for y in mapped_set.set {
                result.insert(y);
            }
        }
        FSet { set: result }
    }
}

impl<T> Clone for FSet<T>
where
    T: Clone + Eq + Hash,
{
    fn clone(&self) -> Self {
        Self {
            set: self.set.clone(),
        }
    }
}

impl<T> PartialEq for FSet<T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        self.set == other.set
    }
}

impl<T> Eq for FSet<T> where T: Eq + Hash {}

impl<T> Default for FSet<T>
where
    T: Eq + Hash,
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<T> From<HashSet<T>> for FSet<T>
where
    T: Eq + Hash,
{
    fn from(set: HashSet<T>) -> Self {
        Self { set }
    }
}

#[allow(clippy::implicit_hasher)]
impl<T> From<FSet<T>> for HashSet<T>
where
    T: Eq + Hash,
{
    fn from(fset: FSet<T>) -> Self {
        fset.set
    }
}

impl<T> From<std::collections::BTreeSet<T>> for FSet<T>
where
    T: Eq + Hash,
{
    fn from(btree: std::collections::BTreeSet<T>) -> Self {
        Self {
            set: btree.into_iter().collect(),
        }
    }
}

/// Internal specification string constants consumed by trust-wp-driver's
/// table-backed logical lookup path and related local tests.
#[doc(hidden)]
pub mod specs {
    /// Contract for `FSet::insert_ghost` (mutable in-place insert in ghost blocks)
    ///
    /// Frame axiom: inserting element `arg1` does not affect other elements.
    /// Args: self=arg0, x=arg1
    pub const INSERT_GHOST: &str = r"
        params: self, arg1
        ensures: (^self).contains(arg1)
        ensures: forall<y: _> y != arg1 ==> (^self).contains(y) == self.contains(y)
        ensures: result == !self.contains(arg1)
        ensures: result ==> (^self).len() == self.len() + 1
        ensures: !result ==> (^self).len() == self.len()
    ";

    /// Contract for `FSet::remove_ghost` (mutable in-place remove in ghost blocks)
    ///
    /// Frame axiom: removing element `*arg1` does not affect other elements.
    /// Args: self=arg0, x=arg1 (passed by ref)
    pub const REMOVE_GHOST: &str = r"
        params: self, arg1
        ensures: !(^self).contains(*arg1)
        ensures: forall<y: _> y != *arg1 ==> (^self).contains(y) == self.contains(y)
        ensures: result == self.contains(*arg1)
        ensures: result ==> (^self).len() == self.len() - 1
        ensures: !result ==> (^self).len() == self.len()
    ";

    /// Contract for `FSet::contains_ghost` (contains check by reference)
    /// Args: self=arg0, x=arg1 (passed by ref)
    pub const CONTAINS_GHOST: &str = r"
        params: self, arg1
        ensures: result == self.contains(*arg1)
    ";

    /// Contract for `FSet::len_ghost` (length in ghost blocks)
    pub const LEN_GHOST: &str = r"
        params: self
        ensures: result == self.len()
    ";

    /// Contract for `FSet::contains` (logical contains check)
    /// Args: self=arg0, x=arg1
    pub const CONTAINS: &str = r"
        params: self, arg1
        ensures: result == self.contains(arg1)
    ";

    /// Contract for `FSet::len` (logical length)
    pub const LEN: &str = r"
        params: self
        ensures: result == self.len()
    ";

    /// Contract for `FSet::insert` (logical, returns new set)
    ///
    /// Frame axiom: inserting element `arg1` does not affect other elements.
    /// Len interaction: inserting a new element increments len, reinserting is idempotent.
    /// Args: self=arg0, x=arg1
    pub const INSERT: &str = r"
        params: self, arg1
        ensures: result.contains(arg1)
        ensures: forall<y: _> y != arg1 ==> result.contains(y) == self.contains(y)
        ensures: self.contains(arg1) ==> result.len() == self.len()
        ensures: !self.contains(arg1) ==> result.len() == self.len() + 1
    ";

    /// Contract for `FSet::remove` (logical, returns new set)
    ///
    /// Frame axiom: removing element `*arg1` does not affect other elements.
    /// Len interaction: removing a present element decrements len.
    /// Args: self=arg0, x=arg1 (passed by ref)
    pub const REMOVE: &str = r"
        params: self, arg1
        ensures: !result.contains(*arg1)
        ensures: forall<y: _> y != *arg1 ==> result.contains(y) == self.contains(y)
        ensures: self.contains(*arg1) ==> result.len() == self.len() - 1
        ensures: !self.contains(*arg1) ==> result.len() == self.len()
    ";

    /// Contract for `FSet::peek` (logical, returns arbitrary element)
    ///
    /// Peek returns some element from a non-empty set, with the axiom that
    /// the result is contained in the set. The set must be non-empty for the
    /// postcondition to be meaningful (caller provides `!s.is_empty()`).
    /// Args: self=arg0
    pub const PEEK: &str = r"
        params: self
        ensures: self.contains(result)
    ";

    /// Contract for `FSet::is_empty` (logical, emptiness check)
    ///
    /// Links `is_empty()` to `len() == 0` so the solver can reason about
    /// emptiness in terms of cardinality.
    /// Args: self=arg0
    pub const IS_EMPTY: &str = r"
        params: self
        ensures: result == (self.len() == 0)
    ";

    /// Contract for `FSet::empty` / `FSet::new`
    pub const EMPTY: &str = r"
        params:
        ensures: result.len() == 0
        ensures: forall<x: _> !result.contains(x)
    ";

    /// Contract for `FSet::singleton` (create set with one element)
    /// Args: x=arg1
    pub const SINGLETON: &str = r"
        params: arg1
        ensures: result.contains(arg1)
        ensures: result.len() == 1
        ensures: forall<y: _> y != arg1 ==> !result.contains(y)
    ";

    /// Contract for `FSet::union` (set union)
    /// Args: self=arg0, other=arg1
    pub const UNION: &str = r"
        params: self, arg1
        ensures: forall<x: _> result.contains(x) == (self.contains(x) || arg1.contains(x))
    ";

    /// Contract for `FSet::intersection` (set intersection)
    /// Args: self=arg0, other=arg1
    pub const INTERSECTION: &str = r"
        params: self, arg1
        ensures: forall<x: _> result.contains(x) == (self.contains(x) && arg1.contains(x))
    ";

    /// Contract for `FSet::difference` (set difference)
    /// Args: self=arg0, other=arg1
    pub const DIFFERENCE: &str = r"
        params: self, arg1
        ensures: forall<x: _> result.contains(x) == (self.contains(x) && !arg1.contains(x))
    ";

    /// Contract for `FSet::is_subset` (subset check)
    /// Args: self=arg0, other=arg1
    pub const IS_SUBSET: &str = r"
        params: self, arg1
        ensures: result == (forall<x: _> self.contains(x) ==> arg1.contains(x))
    ";

    /// Contract for `FSet::is_superset` (superset check)
    /// Args: self=arg0, other=arg1
    pub const IS_SUPERSET: &str = r"
        params: self, arg1
        ensures: result == (forall<x: _> arg1.contains(x) ==> self.contains(x))
    ";

    /// Contract for `FSet::disjoint` (disjointness check)
    /// Args: self=arg0, other=arg1
    pub const DISJOINT: &str = r"
        params: self, arg1
        ensures: result == (forall<x: _> !self.contains(x) || !arg1.contains(x))
    ";

    /// Contract for `FSet::ext_eq` (extensional equality)
    /// Args: self=arg0, other=arg1
    pub const EXT_EQ: &str = r"
        params: self, arg1
        ensures: result == (forall<x: _> self.contains(x) == arg1.contains(x))
    ";

    /// Contract for `FSet::is_empty_ghost` (ghost-block emptiness check)
    pub const IS_EMPTY_GHOST: &str = r"
        params: self
        ensures: result == (self.len() == 0)
    ";

    /// Contract for `FSet::into_inner` (identity unwrap)
    pub const INTO_INNER: &str = r"
        params: self
        ensures: result == self
    ";
}

#[cfg(test)]
mod tests;
