// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core `Seq<T>` implementation: constructors, accessors, logical collection
//! operations, and ghost helpers.

use std::{borrow::Borrow, collections::HashMap, hash::Hash};

use super::Seq;
use crate::logic::{Int, Mapping};

impl<T> Seq<T> {
    /// Create an empty sequence.
    ///
    /// SMT encoding: `seq_len = 0`
    pub const fn empty() -> Self
    where
        T: Sized,
    {
        Self {
            elements: Vec::new(),
        }
    }

    /// Create an empty sequence (Creusot-compatible alias for [`empty`](Self::empty)).
    pub const fn new() -> Self
    where
        T: Sized,
    {
        Self::empty()
    }

    /// Unwrap into the inner value (Creusot compatibility).
    ///
    /// In Creusot, this unwraps a `GhostBox<Seq>` into its inner `Seq`.
    /// Here it is an identity operation since `Seq` is not ghost-wrapped.
    pub fn into_inner(self) -> Self {
        self
    }

    /// Create a sequence with a single element.
    ///
    /// SMT encoding: `seq_len = 1, seq_contents[0] = x`
    pub fn singleton(x: T) -> Self {
        Self { elements: vec![x] }
    }

    /// Get the length of the sequence.
    ///
    /// SMT encoding: returns `seq_len`
    pub fn len(&self) -> Int {
        Int::from(self.elements.len())
    }

    /// Check if the sequence is empty.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Iterate over sequence elements by reference.
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.elements.iter()
    }

    /// Get element at index (returns None if out of bounds).
    ///
    /// SMT encoding: `if 0 <= ix < seq_len then Some(seq_contents[ix]) else None`
    ///
    /// Returns `Option<T>` (owned value) like Creusot's `Seq::get`.
    pub fn get(&self, ix: Int) -> Option<T>
    where
        T: Clone,
    {
        if ix.0 < 0 {
            return None;
        }
        let idx = ix.0 as usize;
        self.elements.get(idx).cloned()
    }

    /// Get element at index (panics if out of bounds).
    ///
    /// Used in specifications where bounds are guaranteed.
    /// SMT encoding: `seq_contents[ix]` (with implicit bounds constraint)
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    /// Returns owned `T` like Creusot's `IndexLogic<Int>`.
    pub fn index_logic(self, ix: Int) -> T
    where
        T: Clone,
    {
        let idx = ix.0 as usize;
        self.elements[idx].clone()
    }

    /// Get element at index, returning a reference.
    ///
    /// This is the "unsized" variant of `index_logic` that returns `&T`
    /// instead of `T`, allowing it to work with `?Sized` types.
    ///
    /// Matches Creusot's `Seq::index_logic_unsized(self, ix: Int) -> &T`.
    ///
    /// Reference: `creusot-std/src/logic/seq.rs:100`
    pub fn index_logic_unsized(&self, ix: Int) -> &T {
        let idx = ix.0 as usize;
        &self.elements[idx]
    }

    /// Append an element to the end.
    ///
    /// SMT encoding:
    /// ```smt
    /// new_seq_contents = store(seq_contents, seq_len, x)
    /// new_seq_len = seq_len + 1
    /// ```
    pub fn push_back(mut self, x: T) -> Self {
        self.elements.push(x);
        self
    }

    /// Prepend an element to the front.
    ///
    /// SMT encoding: shifts all indices by 1, sets index 0 to x
    pub fn push_front(mut self, x: T) -> Self {
        self.elements.insert(0, x);
        self
    }

    /// Return the sequence without its last element.
    ///
    /// Equivalent to `self.subsequence(0, self.len() - 1)`.
    /// Panics if empty.
    ///
    /// Matches Creusot's `Seq::pop_back(self) -> Self` signature.
    pub fn pop_back(mut self) -> Self {
        self.elements.pop().expect("pop_back on empty Seq");
        self
    }

    /// Return the sequence without its first element.
    ///
    /// Equivalent to `self.subsequence(1, self.len())`.
    /// Panics if empty.
    ///
    /// Matches Creusot's `Seq::tail(self) -> Self` signature.
    pub fn tail(mut self) -> Self {
        self.elements.remove(0);
        self
    }

    /// Alias for `tail()` — removes and discards the first element.
    ///
    /// Matches Creusot's `Seq::pop_front(self) -> Self`.
    pub fn pop_front(self) -> Self {
        self.tail()
    }

    /// Get a subsequence from start (inclusive) to end (exclusive).
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn subsequence(self, start: Int, end: Int) -> Self
    where
        T: Clone,
    {
        let s = start.0 as usize;
        let e = end.0 as usize;
        Self {
            elements: self.elements[s..e].to_vec(),
        }
    }

    /// Concatenate two sequences.
    pub fn concat(mut self, other: Self) -> Self {
        self.elements.extend(other.elements);
        self
    }

    /// Returns a new sequence with the element at index `ix` replaced by `x`.
    ///
    /// If `ix` is out of bounds, the result is undefined (panics in runtime model).
    ///
    /// SMT encoding: `seq_contents = store(seq_contents, ix, x)`
    ///
    /// # Example
    ///
    /// ```text
    /// let s = Seq::from(vec![1, 2, 3]);
    /// let s2 = s.set(Int(1), 42);
    /// assert_eq!(s2.get(Int(1)), Some(&42));
    /// ```
    pub fn set(mut self, ix: Int, x: T) -> Self {
        let idx = ix.0 as usize;
        self.elements[idx] = x;
        self
    }

    /// Returns `true` if the sequence contains the element `x`.
    ///
    /// SMT encoding: `exists i. 0 <= i < len && seq_contents[i] = x`
    ///
    /// Accepts borrowed membership queries so logical checks do not require
    /// cloning the searched-for element.
    pub fn contains<Q>(&self, x: Q) -> bool
    where
        T: PartialEq,
        Q: Borrow<T>,
    {
        self.elements.iter().any(|element| element == x.borrow())
    }

    /// Returns `true` if the sequence is sorted in ascending order.
    ///
    /// SMT encoding: `forall i,j. 0 <= i <= j < len => seq[i] <= seq[j]`
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn sorted(self) -> bool
    where
        T: Ord,
    {
        self.elements.windows(2).all(|w| w[0] <= w[1])
    }

    /// Returns `true` if the sequence is sorted between indices `start` and `end`.
    ///
    /// Returns `true` for empty or single-element ranges (vacuously true).
    ///
    /// SMT encoding: `forall i,j. start <= i <= j < end => seq[i] <= seq[j]`
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn sorted_range(self, start: Int, end: Int) -> bool
    where
        T: Ord,
    {
        let s = start.0 as usize;
        let e = end.0 as usize;
        let slice = &self.elements[s..e];
        slice.windows(2).all(|w| w[0] <= w[1])
    }

    /// Returns `true` if `other` is a permutation of `self`.
    ///
    /// Two sequences are permutations of each other if they contain the same
    /// elements with the same multiplicities (same multiset).
    ///
    /// SMT encoding: Uses `permut` predicate from seq theory.
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn permutation_of(self, other: Self) -> bool
    where
        T: Ord + Clone,
    {
        if self.elements.len() != other.elements.len() {
            return false;
        }
        let mut s1: Vec<T> = self.elements;
        let mut s2: Vec<T> = other.elements;
        s1.sort();
        s2.sort();
        s1 == s2
    }

    /// Count the number of occurrences of element `x` in the sequence.
    ///
    /// SMT encoding: `sum(i, 0, len, if seq[i] = x then 1 else 0)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn count(self, x: T) -> Int
    where
        T: PartialEq,
    {
        let cnt = self.elements.iter().filter(|e| **e == x).count();
        Int::from(cnt)
    }

    /// Returns `true` if `other` is `self` with elements at `i` and `j` swapped.
    ///
    /// SMT encoding: Uses `exchange` predicate from seq theory.
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn exchange(self, other: Self, i: Int, j: Int) -> bool
    where
        T: PartialEq,
    {
        if self.elements.len() != other.elements.len() {
            return false;
        }
        let i_idx = i.0 as usize;
        let j_idx = j.0 as usize;
        let len = self.elements.len();

        if i_idx >= len || j_idx >= len {
            return false;
        }

        // Check that swapping i and j in self gives other
        for k in 0..len {
            let expected = if k == i_idx {
                &self.elements[j_idx]
            } else if k == j_idx {
                &self.elements[i_idx]
            } else {
                &self.elements[k]
            };
            if other.elements[k] != *expected {
                return false;
            }
        }
        true
    }

    /// Reverse the sequence.
    ///
    /// SMT encoding: `seq.Reverse.reverse`
    pub fn reverse(mut self) -> Self {
        self.elements.reverse();
        self
    }

    /// Prepend an element to the sequence (Creusot internal primitive).
    ///
    /// `cons(x, s)` is equivalent to `s.push_front(x)`.
    /// In Creusot this is `#[builtin("seq.Seq.cons")]`.
    ///
    /// SMT encoding: `seq.Seq.cons`
    pub fn cons(x: T, mut seq: Self) -> Self {
        seq.elements.insert(0, x);
        seq
    }

    /// Create a sequence of length `n` where element `i` is `mapping.get(i)`.
    ///
    /// SMT encoding: `seq.Seq.create`
    ///
    /// Creusot: `#[builtin("seq.Seq.create")]`
    pub fn create(n: Int, mapping: Mapping<Int, T>) -> Self
    where
        T: Clone,
    {
        let len = n.0 as usize;
        let mut elements = Vec::with_capacity(len);
        for i in 0..len {
            elements.push(mapping.clone().get(Int(i as i128)));
        }
        Self { elements }
    }

    /// Map each element through a mapping function.
    ///
    /// Returns a new sequence of the same length where element `i` is
    /// `mapping.get(self[i])`.
    ///
    /// SMT encoding: recursive definition with pointwise postcondition
    ///
    /// Creusot contract:
    /// ```text
    /// #[ensures(result.len() == self.len())]
    /// #[ensures(forall<i> 0 <= i && i < self.len() ==> result[i] == m[self[i]])]
    /// ```
    pub fn map<U>(self, m: Mapping<T, U>) -> Seq<U>
    where
        T: Eq + std::hash::Hash + Clone,
        U: Clone,
    {
        let elements = self
            .elements
            .into_iter()
            .map(|x| m.clone().get(x))
            .collect();
        Seq { elements }
    }

    /// Flat-map each element through a mapping that returns a sequence.
    ///
    /// Each element `x` is mapped to a `Seq<U>` via `other.get(x)`, and
    /// all resulting sequences are concatenated in order.
    ///
    /// SMT encoding: recursive definition
    ///
    /// Creusot definition:
    /// ```text
    /// if self.len() == 0 { Seq::empty() }
    /// else { other.get(self[0]).concat(self.tail().flat_map(other)) }
    /// ```
    pub fn flat_map<U>(self, other: Mapping<T, Seq<U>>) -> Seq<U>
    where
        T: Eq + std::hash::Hash + Clone,
        U: Clone,
    {
        let mut result = Vec::new();
        for x in self.elements {
            let mapped_seq = other.clone().get(x);
            result.extend(mapped_seq.elements);
        }
        Seq { elements: result }
    }

    /// Extensional equality — two sequences are ext_eq if they have the
    /// same length and identical elements at every index.
    ///
    /// SMT encoding: `seq.Seq.(==)`
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn ext_eq(self, other: Self) -> bool
    where
        T: PartialEq,
    {
        self.elements == other.elements
    }

    /// Range-bounded permutation check.
    ///
    /// Returns `true` if `self` and `other` are permutations of each other
    /// within the range `[start, end)`, and identical outside that range.
    ///
    /// SMT encoding: `seq.Permut.permut`
    ///
    /// Takes `self` by value to match Creusot's `Copy` Seq semantics.
    pub fn permut(self, other: Self, start: Int, end: Int) -> bool
    where
        T: Ord + Clone,
    {
        if self.elements.len() != other.elements.len() {
            return false;
        }
        let s = start.0 as usize;
        let e = end.0 as usize;
        let len = self.elements.len();
        if s > e || e > len {
            return false;
        }
        // Elements outside [start, end) must be identical
        for i in 0..s {
            if self.elements[i] != other.elements[i] {
                return false;
            }
        }
        for i in e..len {
            if self.elements[i] != other.elements[i] {
                return false;
            }
        }
        // Elements inside [start, end) must be a permutation
        let mut inner_self: Vec<T> = self.elements[s..e].to_vec();
        let mut inner_other: Vec<T> = other.elements[s..e].to_vec();
        inner_self.sort();
        inner_other.sort();
        inner_self == inner_other
    }

    /// Ghost helper: sequence length.
    pub fn len_ghost(&self) -> Int {
        Int::from(self.elements.len())
    }

    /// Ghost helper: emptiness check.
    pub fn is_empty_ghost(&self) -> bool {
        self.elements.is_empty()
    }

    /// Ghost helper: push back in place.
    pub fn push_back_ghost(&mut self, x: T) {
        self.elements.push(x);
    }

    /// Ghost helper: push front in place.
    pub fn push_front_ghost(&mut self, x: T) {
        self.elements.insert(0, x);
    }

    /// Ghost helper: immutable element access.
    pub fn get_ghost(&self, index: Int) -> Option<&T> {
        if index.0 < 0 {
            return None;
        }
        self.elements.get(index.0 as usize)
    }

    /// Ghost helper: mutable element access.
    pub fn get_mut_ghost(&mut self, index: Int) -> Option<&mut T> {
        if index.0 < 0 {
            return None;
        }
        self.elements.get_mut(index.0 as usize)
    }

    /// Ghost helper: pop back in place.
    pub fn pop_back_ghost(&mut self) -> Option<T> {
        self.elements.pop()
    }

    /// Ghost helper: pop front in place.
    pub fn pop_front_ghost(&mut self) -> Option<T> {
        if self.elements.is_empty() {
            None
        } else {
            Some(self.elements.remove(0))
        }
    }
}

impl<A, B> Seq<(A, B)> {
    /// Returns `true` if the sequence contains the pair `(a, b)`.
    ///
    /// This tuple-specialized helper keeps the collect bridge from nesting
    /// `any` inside `all` when checking `HashMap` membership.
    pub fn contains_pair(&self, a: &A, b: &B) -> bool
    where
        A: PartialEq,
        B: PartialEq,
    {
        self.elements.iter().any(|(x, y)| x == a && y == b)
    }

    /// Returns `true` if every pair in the sequence is present in `map`.
    ///
    /// This direct loop form is cheaper for proof search than a nested
    /// iterator witness and is used by the `HashMap::from_iter_post` bridge.
    pub fn matches_map(&self, map: &HashMap<A, B>) -> bool
    where
        A: Eq + Hash,
        B: PartialEq,
    {
        for (key, value) in &self.elements {
            if map.get(key) != Some(value) {
                return false;
            }
        }
        true
    }
}

impl<T: Clone> Seq<&T> {
    /// Convert `Seq<&T>` to `Seq<T>` by cloning each element.
    ///
    /// In Creusot, `&T` is equivalent to `T` in pearlite (logic context),
    /// so `to_owned_seq` is the identity function (`#[builtin("identity")]`).
    /// In trust-wp's runtime model, this clones each element.
    ///
    /// Reference: `creusot-std/src/logic/seq.rs` — `impl<T> Seq<&T>`
    pub fn to_owned_seq(self) -> Seq<T> {
        Seq {
            elements: self.elements.into_iter().cloned().collect(),
        }
    }
}
