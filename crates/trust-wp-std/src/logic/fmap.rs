// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite map type for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `FMap<K, V>` is a logical finite map type used in specifications and ghost code.
//! Unlike `HashMap`, it has no capacity limits and is designed for verification.
//!
//! At the SMT level, `FMap<K, V>` is encoded as:
//! - An SMT array `(Array K (Option V))` for contents
//! - An SMT integer for length (number of keys with Some value)
//!
//! Reference: Creusot's `creusot-std/src/logic/fmap.rs`

// Allow cast_sign_loss for Int to usize conversions in runtime model
#![allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
// Allow must_use for builder methods that chain
#![allow(clippy::must_use_candidate)]
// Builder pattern methods returning Self don't need must_use in logical model
#![allow(clippy::return_self_not_must_use)]

use std::{borrow::Borrow, collections::HashMap, hash::Hash, marker::PhantomData, ops::Index};

use super::{
    ra::{UnitRA, RA},
    Int, Seq,
};

/// A finite map type for specifications.
///
/// `FMap<K, V>` models key-value mappings in specifications. Unlike `HashMap`,
/// it is a logical concept with no capacity limits. In contracts:
///
/// ```text
/// #[ensures((^self)@ == self@.insert(k, v))]
/// fn insert(&mut self, k: K, v: V)
/// ```
///
/// Where `@` is the view operator that converts `HashMap<K, V>` to `FMap<K, V>`.
#[derive(Debug)]
#[must_use]
pub struct FMap<K, V> {
    /// Internal storage (for runtime representation in tests)
    map: HashMap<K, V>,
}

impl<K, V> FMap<K, V> {
    /// Create an empty map.
    ///
    /// SMT encoding: `map_len = 0, forall k. map_contents[k] = None`
    pub fn empty() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Create an empty map (Creusot-compatible alias for [`empty`](Self::empty)).
    pub fn new() -> Self {
        Self::empty()
    }

    /// Unwrap into the inner value (Creusot compatibility).
    ///
    /// In Creusot, this unwraps a `GhostBox<FMap>` into its inner `FMap`.
    /// Here it is an identity operation since `FMap` is not ghost-wrapped.
    pub fn into_inner(self) -> Self {
        self
    }

    /// Convert the map contents into a sequence of key/value pairs.
    ///
    /// This is a witness-oriented helper for iterator-history proofs. The
    /// returned sequence is a runtime collection of the current map entries;
    /// proof search sees it through the dedicated `fmap_into_seq` bridge.
    pub fn into_seq(self) -> Seq<(K, V)> {
        Seq::from(self.map.into_iter().collect::<Vec<_>>())
    }

    /// Get the number of key-value pairs in the map.
    ///
    /// SMT encoding: returns `map_len`
    pub fn len(&self) -> Int {
        Int::from(self.map.len())
    }

    /// Check if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<K, V> FMap<K, V>
where
    K: Eq + Hash,
{
    /// Insert a key-value pair into the map.
    ///
    /// Returns a new map with the key-value pair added or updated.
    ///
    /// Consumes `self` to match the value-oriented logical APIs used by the
    /// other collection types in `trust-wp-std`.
    ///
    /// SMT encoding:
    /// ```smt
    /// new_map_contents = store(map_contents, k, Some(v))
    /// new_map_len = if contains(k) then map_len else map_len + 1
    /// ```
    pub fn insert(mut self, k: K, v: V) -> Self {
        self.map.insert(k, v);
        self
    }

    /// Create a map containing only the given key-value pair.
    pub fn singleton(k: K, v: V) -> Self {
        Self::empty().insert(k, v)
    }

    /// Remove a key from the map.
    ///
    /// Returns a new map with the key removed.
    ///
    /// Consumes `self` to match the value-oriented logical APIs used by the
    /// other collection types in `trust-wp-std`.
    ///
    /// SMT encoding:
    /// ```smt
    /// new_map_contents = store(map_contents, k, None)
    /// new_map_len = if contains(k) then map_len - 1 else map_len
    /// ```
    pub fn remove<Q>(mut self, k: Q) -> Self
    where
        Q: Borrow<K>,
    {
        self.map.remove(k.borrow());
        self
    }

    /// Get the value associated with a key.
    ///
    /// Returns `Some(v)` if the key is present, `None` otherwise.
    ///
    /// SMT encoding: `map_contents[k]`
    pub fn get<Q>(&self, k: Q) -> Option<&V>
    where
        Q: Borrow<K>,
    {
        self.map.get(k.borrow())
    }

    /// Get the value associated with a key, panicking if not found.
    ///
    /// Used in specifications where the key is guaranteed to exist.
    ///
    /// SMT encoding: `unwrap(map_contents[k])` (with implicit contains constraint)
    pub fn lookup<Q>(&self, k: Q) -> V
    where
        Q: Borrow<K>,
        V: Clone,
    {
        self.lookup_ref(k).clone()
    }

    fn lookup_ref<Q>(&self, k: Q) -> &V
    where
        Q: Borrow<K>,
    {
        self.map
            .get(k.borrow())
            .expect("key not found in FMap::lookup")
    }

    /// Check if the map contains a key.
    ///
    /// SMT encoding: `map_contents[k] != None`
    pub fn contains<Q>(&self, k: Q) -> bool
    where
        Q: Borrow<K>,
    {
        self.map.contains_key(k.borrow())
    }

    /// Check if two maps are disjoint (have no keys in common).
    ///
    /// SMT encoding: `forall k. !self.contains(k) || !other.contains(k)`
    pub fn disjoint(&self, other: &Self) -> bool {
        for k in self.map.keys() {
            if other.contains(k) {
                return false;
            }
        }
        true
    }

    /// Check if all key-value pairs in self are also in other.
    ///
    /// SMT encoding: `forall k. self.contains(k) ==> other.get(k) == self.get(k)`
    pub fn subset(&self, other: &Self) -> bool
    where
        V: PartialEq,
    {
        for (k, v) in &self.map {
            match other.get(k) {
                Some(other_v) if v == other_v => {}
                _ => return false,
            }
        }
        true
    }

    /// Return the union of two disjoint maps.
    ///
    /// If the maps are not disjoint, behavior is undefined (panics in runtime).
    ///
    /// SMT encoding:
    /// ```smt
    /// forall k. !self.contains(k) ==> result.get(k) == other.get(k)
    /// forall k. !other.contains(k) ==> result.get(k) == self.get(k)
    /// result.len() == self.len() + other.len()
    /// ```
    pub fn union(mut self, other: Self) -> Self
    where
        V: Clone,
    {
        assert!(self.disjoint(&other), "FMap::union requires disjoint maps");
        for (k, v) in other.map {
            self.map.insert(k, v);
        }
        self
    }

    /// Merge two maps, combining conflicting values with `f`.
    pub fn merge<F>(self, other: Self, f: F) -> Self
    where
        K: Clone,
        V: Clone,
        F: Fn((V, V)) -> V,
    {
        let mut result = other;
        for (k, v_left) in self.map {
            if let Some(v_right) = result.map.get(&k).cloned() {
                result.map.insert(k, f((v_left, v_right)));
            } else {
                result.map.insert(k, v_left);
            }
        }
        result
    }

    /// Extensional equality (same key/value mapping).
    ///
    /// Consumes both maps to match the value-oriented logical APIs used by the
    /// other collection types in `trust-wp-std`.
    ///
    /// Runtime equality requires `V: PartialEq` so the test model matches the
    /// logical contract's value-level semantics.
    pub fn ext_eq(self, other: Self) -> bool
    where
        V: PartialEq,
    {
        let mut other_map = other.map;
        if self.map.len() != other_map.len() {
            return false;
        }
        self.map.into_iter().all(|(key, value)| {
            other_map
                .remove(&key)
                .is_some_and(|other_value| other_value == value)
        })
    }

    /// Ghost helper: mutable insert used from `ghost!` blocks.
    pub fn insert_ghost(&mut self, k: K, v: V) -> Option<V> {
        self.map.insert(k, v)
    }

    /// Ghost helper: mutable remove used from `ghost!` blocks.
    pub fn remove_ghost(&mut self, k: &K) -> Option<V> {
        self.map.remove(k)
    }

    /// Ghost helper: mutable access by key.
    pub fn get_mut_ghost(&mut self, k: &K) -> Option<&mut V> {
        self.map.get_mut(k)
    }

    /// Ghost helper: immutable access by key.
    pub fn get_ghost(&self, k: &K) -> Option<&V> {
        self.map.get(k)
    }

    /// Ghost helper: contains check by reference key.
    pub fn contains_ghost(&self, k: &K) -> bool {
        self.map.contains_key(k)
    }

    /// Ghost helper: current map length.
    pub fn len_ghost(&self) -> Int {
        Int::from(self.map.len())
    }

    /// Ghost helper: emptiness check.
    pub fn is_empty_ghost(&self) -> bool {
        self.map.is_empty()
    }

    /// Ghost helper: mutable split view for aliasing-style proof code.
    ///
    /// Returns an exclusive reference to the value at `key` and a
    /// [`FMapGhostSplit`] handle that can mutate all *other* entries.
    ///
    /// # Safety (internal)
    ///
    /// This function creates mutable aliasing internally: the returned
    /// `&mut V` points into the same `HashMap` that
    /// `FMapGhostSplit::map_mut()` accesses via raw pointer. This is
    /// sound because:
    ///
    /// 1. The `HashMap` is pre-reserved so inserts through the split will
    ///    not trigger reallocation (enforced by capacity check in
    ///    `FMapGhostSplit::insert_ghost`).
    /// 2. `FMapGhostSplit::insert_ghost` and `remove_ghost` take `&mut self`,
    ///    so the borrow checker prevents calling them while the `&mut V` is
    ///    still live (both borrow the same `FMapGhostSplit` lifetime).
    /// 3. The pinned-key guard in `insert_ghost`/`remove_ghost` prevents
    ///    modifying the entry that the returned `&mut V` points to.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not present in the map.
    pub fn split_mut_ghost<'a>(&'a mut self, key: &K) -> (&'a mut V, FMapGhostSplit<'a, K, V>)
    where
        K: Clone,
    {
        // Pre-reserve capacity so that subsequent insert_ghost calls
        // through the FMapGhostSplit do not trigger HashMap reallocation,
        // which would invalidate the raw pointer backing the returned
        // `&mut V`.  We reserve enough for a reasonable number of ghost
        // operations (8 slots beyond current usage).
        self.map.reserve(8);

        let value_ptr = std::ptr::from_mut::<V>(
            self.map
                .get_mut(key)
                .expect("split_mut_ghost requires key to be present"),
        );
        let capacity_after_reserve = self.map.capacity();
        let split = FMapGhostSplit {
            map: core::ptr::from_mut(self),
            pinned_key: key.clone(),
            capacity_at_split: capacity_after_reserve,
            _marker: PhantomData,
        };
        // SAFETY: `value_ptr` was obtained from a live HashMap entry.
        // The HashMap has been pre-reserved so inserts through the split
        // will not reallocate (enforced by capacity check in insert_ghost).
        let value_ref = unsafe { &mut *value_ptr };
        (value_ref, split)
    }
}

/// Mutable split view returned by `FMap::split_mut_ghost`.
///
/// The `capacity_at_split` field tracks the `HashMap` capacity at split
/// creation time.  `insert_ghost` panics if the map would exceed this
/// capacity, preventing reallocation that would invalidate the `&mut V`
/// pointer returned alongside this split.
pub struct FMapGhostSplit<'a, K, V> {
    map: *mut FMap<K, V>,
    pinned_key: K,
    capacity_at_split: usize,
    _marker: PhantomData<&'a mut FMap<K, V>>,
}

impl<'a, K, V> FMapGhostSplit<'a, K, V>
where
    K: Eq + Hash + Clone,
{
    fn map_mut(&mut self) -> &mut HashMap<K, V> {
        // SAFETY: `self.map` was created from an exclusive `&mut FMap` in
        // `split_mut_ghost` and the lifetime is bounded by `'a`.
        //
        // Callers (insert_ghost, remove_ghost) guard against the pinned
        // key, preventing overlap with the `&mut V` returned by the parent
        // `split_mut_ghost` call.
        unsafe { &mut (*self.map).map }
    }

    pub fn insert_ghost(&mut self, k: K, v: V) -> Option<V> {
        if k == self.pinned_key {
            return None;
        }
        let cap = self.capacity_at_split;
        let map = self.map_mut();
        // Guard: if this insert would add a new key and exceed the
        // capacity reserved at split time, panic rather than allow
        // HashMap reallocation (which would invalidate the sibling
        // `&mut V` pointer from split_mut_ghost).
        if !map.contains_key(&k) {
            assert!(
                map.len() < cap,
                "FMapGhostSplit::insert_ghost: would exceed pre-reserved capacity, \
                 risking HashMap reallocation and dangling pointer UB"
            );
        }
        map.insert(k, v)
    }

    pub fn remove_ghost(&mut self, k: &K) -> Option<V> {
        if *k == self.pinned_key {
            return None;
        }
        self.map_mut().remove(k)
    }

    /// Get an immutable reference to a value by key.
    ///
    /// Returns `None` if the key matches the pinned key (that entry is
    /// exclusively borrowed through the sibling `&mut V` from
    /// `split_mut_ghost`), or if the key does not exist in the map.
    ///
    /// Reference: Creusot's `FMap::get_ghost` is available on split handles.
    pub fn get_ghost(&self, k: &K) -> Option<&V> {
        if *k == self.pinned_key {
            return None;
        }
        // SAFETY: `self.map` was created from an exclusive `&mut FMap` in
        // `split_mut_ghost` and the lifetime is bounded by `'a`. We only
        // access entries that are NOT the pinned key, so no aliasing with
        // the sibling `&mut V`.
        let map = unsafe { &(*self.map).map };
        map.get(k)
    }

    /// Get a mutable reference to a value by key.
    ///
    /// Returns `None` if the key matches the pinned key (that entry is
    /// exclusively borrowed through the sibling `&mut V` from
    /// `split_mut_ghost`), or if the key does not exist in the map.
    ///
    /// Reference: Creusot's `FMap::get_mut_ghost` is available on split handles.
    pub fn get_mut_ghost(&mut self, k: &K) -> Option<&mut V> {
        if *k == self.pinned_key {
            return None;
        }
        self.map_mut().get_mut(k)
    }
}

impl<K, V> Clone for FMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<K, V> RA for FMap<K, V> {
    fn op(&self, _other: &Self) -> Option<Self> {
        panic!("ghost code only")
    }

    fn can_update(&self, _target: &Self) -> bool {
        panic!("ghost code only")
    }

    fn core(&self) -> Option<Self> {
        panic!("ghost code only")
    }

    fn incl(&self, other: &Self) -> bool {
        let _ = other;
        panic!("ghost code only")
    }
}

impl<K, V> UnitRA for FMap<K, V> {
    #[crate::logic(open)]
    fn unit() -> Self {
        Self::empty()
    }
}

impl<K, V> PartialEq for FMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<K, V> Eq for FMap<K, V>
where
    K: Eq + Hash,
    V: Eq,
{
}

impl<K, V> Default for FMap<K, V>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<K, V> From<HashMap<K, V>> for FMap<K, V>
where
    K: Eq + Hash,
{
    fn from(map: HashMap<K, V>) -> Self {
        Self { map }
    }
}

#[allow(clippy::implicit_hasher)]
impl<K, V> From<FMap<K, V>> for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn from(fmap: FMap<K, V>) -> Self {
        fmap.map
    }
}

impl<K, V> From<std::collections::BTreeMap<K, V>> for FMap<K, V>
where
    K: Eq + Hash,
{
    fn from(btree: std::collections::BTreeMap<K, V>) -> Self {
        Self {
            map: btree.into_iter().collect(),
        }
    }
}

impl<K, V> From<Seq<(K, V)>> for FMap<K, V>
where
    K: Eq + Hash,
{
    fn from(seq: Seq<(K, V)>) -> Self {
        Self {
            map: seq.into_iter().collect(),
        }
    }
}

impl<K, V> Index<&K> for FMap<K, V>
where
    K: Eq + Hash,
{
    type Output = V;

    fn index(&self, key: &K) -> &V {
        self.lookup_ref(key)
    }
}

impl<K, V> Index<K> for FMap<K, V>
where
    K: Eq + Hash,
{
    type Output = V;

    fn index(&self, key: K) -> &V {
        self.lookup_ref(&key)
    }
}

/// Internal specification string constants consumed by trust-wp-driver's
/// table-backed logical lookup path and related local tests.
#[doc(hidden)]
pub mod specs {
    /// Contract for `FMap::insert_ghost` (mutable in-place insert in ghost blocks)
    ///
    /// Frame axiom: inserting key `arg1` does not affect other keys.
    /// Args: self=arg0, k=arg1, v=arg2
    pub const INSERT_GHOST: &str = r"
        params: self, arg1, arg2
        ensures: (^self).contains(arg1)
        ensures: (^self).lookup(arg1) == arg2
        ensures: forall<k2: _> k2 != arg1 ==> (^self).contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != arg1 && self.contains(k2) ==> (^self).lookup(k2) == self.lookup(k2)
        ensures: match result {
            Some(prev) => self.contains(arg1) && prev == self.lookup(arg1) && (^self).len() == self.len(),
            None => !self.contains(arg1) && (^self).len() == self.len() + 1,
        }
    ";

    /// Contract for `FMap::remove_ghost` (mutable in-place remove in ghost blocks)
    ///
    /// Frame axiom: removing key `*arg1` does not affect other keys.
    /// Args: self=arg0, k=arg1 (passed by ref)
    pub const REMOVE_GHOST: &str = r"
        params: self, arg1
        ensures: !(^self).contains(*arg1)
        ensures: forall<k2: _> k2 != *arg1 ==> (^self).contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != *arg1 && self.contains(k2) ==> (^self).lookup(k2) == self.lookup(k2)
        ensures: match result {
            Some(prev) => self.contains(*arg1) && prev == self.lookup(*arg1) && (^self).len() == self.len() - 1,
            None => !self.contains(*arg1) && (^self).len() == self.len(),
        }
    ";

    /// Contract for `FMap::get_ghost` (immutable key lookup in ghost blocks)
    /// Args: self=arg0, k=arg1 (passed by ref)
    pub const GET_GHOST: &str = r"
        params: self, arg1
        ensures: match result {
            Some(v) => self.contains(*arg1) && *v == self.lookup(*arg1),
            None => !self.contains(*arg1),
        }
    ";

    /// Contract for `FMap::get_mut_ghost` (mutable key lookup in ghost blocks)
    ///
    /// Reference: Creusot `creusot-std/src/logic/fmap.rs:351-367` `get_mut_ghost`:
    /// ```text
    /// #[ensures(if self.contains(*key) {
    ///     match result { None => false, Some(r) =>
    ///         (^self).contains(*key) && self[*key] == *r && (^self)[*key] == ^r }
    ///   } else { result == None && *self == ^self })]
    /// #[ensures(forall<k: K> k != *key ==> (*self).get(k) == (^self).get(k))]
    /// #[ensures((*self).len() == (^self).len())]
    /// ```
    /// The match clause below is the result-directed equivalent of the first
    /// clause (`Some` forces containment; `None` forces absence and, with the
    /// frame clauses, `*self == ^self`). The `get`-equality frame is rendered
    /// as the contains/lookup pair — the table idiom for map equality (see
    /// `INSERT_GHOST`).
    ///
    /// The value write-back `(^self)[*key] == ^r` is deliberately NOT
    /// rendered: `^r` is the final value of the `&mut V` inside the `Some`
    /// payload, and the encoder cannot carry a prophecy for an
    /// `Option<&mut V>` payload binder today — `Final` on a pattern-bound
    /// variable collapses to the binder itself
    /// (`trust-wp-ay match_enc/deref_collapse.rs`), and `Final` on the
    /// Datatype-sorted result carrier collapses to the carrier
    /// (`pure_encoding/wrapper.rs` Phase 1b), so `^r` would alias `*r` (the
    /// PRE-write payload) and the clause would invert into the false premise
    /// `(^self)[*key] == old value`. Until the encoder gives Option payloads
    /// a prophecy slot, the touched entry's post-value stays unconstrained:
    /// fail-open to unknown, never to false-accept. (The `^self` mentions in
    /// the clauses below still advance the receiver's carrier, so post-call
    /// asserts are judged against the post-state, not a stale map.)
    ///
    /// Args: self=arg0, k=arg1 (passed by ref)
    pub const GET_MUT_GHOST: &str = r"
        params: self, arg1
        ensures: match result {
            Some(v) => self.contains(*arg1) && *v == self.lookup(*arg1) && (^self).contains(*arg1),
            None => !self.contains(*arg1) && !(^self).contains(*arg1),
        }
        ensures: forall<k2: _> k2 != *arg1 ==> (^self).contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != *arg1 && self.contains(k2) ==> (^self).lookup(k2) == self.lookup(k2)
        ensures: (^self).len() == self.len()
    ";

    /// Contract for `FMap::contains_ghost` (contains check by reference)
    /// Args: self=arg0, k=arg1 (passed by ref)
    pub const CONTAINS_GHOST: &str = r"
        params: self, arg1
        ensures: result == self.contains(*arg1)
    ";

    /// Contract for `FMap::len_ghost` (length in ghost blocks)
    pub const LEN_GHOST: &str = r"
        params: self
        ensures: result == self.len()
    ";

    /// Contract for `FMap::lookup` (get value or panic)
    /// Args: self=arg0, k=arg1
    pub const LOOKUP: &str = r"
        params: self, arg1
        requires: self.contains(arg1)
        ensures: result == self.lookup(arg1)
    ";

    /// Contract for `FMap::insert` (logical, returns new map)
    ///
    /// Frame axiom: inserting key `arg1` does not affect other keys.
    /// Args: self=arg0, k=arg1, v=arg2
    pub const INSERT: &str = r"
        params: self, arg1, arg2
        ensures: result.contains(arg1)
        ensures: result.lookup(arg1) == arg2
        ensures: forall<k2: _> k2 != arg1 ==> result.contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != arg1 && self.contains(k2) ==> result.lookup(k2) == self.lookup(k2)
    ";

    /// Contract for `FMap::contains` (logical contains check)
    /// Args: self=arg0, k=arg1
    pub const CONTAINS: &str = r"
        params: self, arg1
        ensures: result == self.contains(arg1)
    ";

    /// Contract for `FMap::get` (logical get returning Option)
    /// Args: self=arg0, k=arg1
    pub const GET: &str = r"
        params: self, arg1
        ensures: match result {
            Some(v) => self.contains(arg1) && *v == self.lookup(arg1),
            None => !self.contains(arg1),
        }
    ";

    /// Contract for `FMap::len` (logical length)
    ///
    /// The `result >= 0` clause is the standard cardinality non-negativity
    /// fact required by loop variants like `iter@.len()` over an FMap iterator
    /// (#bucket-B-fmap-iter). Without it, `loop_variant_nonneg` cannot
    /// discharge the `iter@.len() >= 0` obligation at the loop entry.
    pub const LEN: &str = r"
        params: self
        ensures: result == self.len()
        ensures: result >= 0
    ";

    /// Contract for `FMap::empty` / `FMap::new`
    pub const EMPTY: &str = r"
        params:
        ensures: result.len() == 0
        ensures: forall<k: _> !result.contains(k)
    ";

    /// Contract for `FMap::remove` (logical, returns new map)
    ///
    /// Frame axiom: removing key `arg1` does not affect other keys.
    /// Args: self=arg0, k=arg1
    pub const REMOVE: &str = r"
        params: self, arg1
        ensures: !result.contains(arg1)
        ensures: forall<k2: _> k2 != arg1 ==> result.contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != arg1 && self.contains(k2) ==> result.lookup(k2) == self.lookup(k2)
    ";

    /// Contract for `FMap::index` (Index trait: `map[key]`)
    ///
    /// Delegates to `lookup` — requires the key to be present.
    /// Args: self=arg0, key=arg1
    pub const INDEX: &str = r"
        params: self, arg1
        requires: self.contains(arg1)
        ensures: *result == self.lookup(arg1)
    ";

    /// Contract for `FMap::singleton`
    /// Args: k=arg0, v=arg1 (no self — associated function)
    pub const SINGLETON: &str = r"
        params: arg0, arg1
        ensures: result.contains(arg0)
        ensures: result.lookup(arg0) == arg1
        ensures: result.len() == 1
    ";

    /// Contract for `FMap::ext_eq`
    /// Args: self=arg0, other=arg1
    pub const EXT_EQ: &str = r"
        params: self, arg1
        ensures: result == (self.len() == arg1.len() &&
            forall<k: _> self.contains(k) ==> arg1.contains(k) && arg1.lookup(k) == self.lookup(k))
    ";

    /// Contract for `FMap::disjoint`
    /// Args: self=arg0, other=arg1
    pub const DISJOINT: &str = r"
        params: self, arg1
        ensures: result == forall<k: _> !self.contains(k) || !arg1.contains(k)
    ";

    /// Contract for `FMap::subset`
    /// Args: self=arg0, other=arg1
    pub const SUBSET: &str = r"
        params: self, arg1
        ensures: result == forall<k: _> self.contains(k) ==> arg1.contains(k) && arg1.lookup(k) == self.lookup(k)
    ";

    /// Contract for `RA::incl` on `FMap<K, V>`.
    ///
    /// The compat `ViewRel::rel_mono` law only needs inclusion to mean
    /// pointwise subset on fragments.
    pub const RA_INCL: &str = r"
        params: self, arg1
        ensures: result == self.subset(arg1)
    ";

    /// Contract for `UnitRA::unit` on `FMap<K, V>`.
    pub const UNIT_RA_UNIT: &str = r"
        params:
        ensures: result == FMap::empty()
    ";

    /// Contract for `FMap::union` (disjoint union)
    /// Args: self=arg0, other=arg1
    pub const UNION: &str = r"
        params: self, arg1
        requires: self.disjoint(&arg1)
        ensures: result.len() == self.len() + arg1.len()
        ensures: forall<k: _> self.contains(k) ==> result.contains(k) && result.lookup(k) == self.lookup(k)
        ensures: forall<k: _> arg1.contains(k) ==> result.contains(k) && result.lookup(k) == arg1.lookup(k)
        ensures: forall<k: _> result.contains(k) ==> self.contains(k) || arg1.contains(k)
    ";

    /// Contract for `FMap::merge` (possibly-overlapping union with resolver)
    /// Args: self=arg0, other=arg1, resolver=arg2
    pub const MERGE: &str = r"
        params: self, arg1, arg2
        ensures: forall<k: _> result.contains(k) == (self.contains(k) || arg1.contains(k))
        ensures: forall<k: _> self.contains(k) && !arg1.contains(k) ==> result.lookup(k) == self.lookup(k)
        ensures: forall<k: _> !self.contains(k) && arg1.contains(k) ==> result.lookup(k) == arg1.lookup(k)
    ";

    /// Contract for `FMap::split_mut_ghost` (split mutable access in ghost blocks)
    ///
    /// Returns `(&mut V, FMapGhostSplit)` for the given key. The returned
    /// value reference points to `self.lookup(key)`.
    ///
    /// Reference: Creusot `creusot-std/src/logic/fmap.rs:389-397`
    /// `split_mut_ghost` (there typed `(&mut V, &mut Self)`):
    /// ```text
    /// #[requires(self.contains(*key))]
    /// #[ensures(*result.1 == (*self).remove(*key))]
    /// #[ensures(self[*key] == *result.0 && ^self == (^result.1).insert(*key, ^result.0))]
    /// ```
    /// `*result.1 == (*self).remove(*key)` is rendered below by its GROUND
    /// consequences only: key absence and `remove`'s length law (`len - 1`,
    /// since `requires` guarantees the key is present). The pointwise
    /// contains/lookup frame foralls of the remove-model are deliberately
    /// omitted: they have no consumer until the parent write-back exists
    /// (the corpus observes the PARENT map, not the split view), and each
    /// extra forall is carried into every downstream proof_assert slice —
    /// measured to push the ghost_map tail obligations from ~5-29s into
    /// 20-83s e-matching grind (whole-test budget blowout). Sound either
    /// way: fewer premises can only under-approximate.
    ///
    /// The parent write-back `^self == (^result.1).insert(*key, ^result.0)`
    /// is deliberately NOT rendered: `^result.1` denotes the split view at
    /// borrow end, and the substitution-chain state tracking has no sound
    /// carrier for that generation at the split call site — instantiating it
    /// against a fixed `Final` depth would equate the parent's post-state
    /// with an intermediate split generation (a false-accept vector). The
    /// parent's post-split state therefore stays (almost) unconstrained:
    /// fail-open to unknown, never to false-accept.
    ///
    /// `(^self).contains(*arg1)` IS rendered: it is a ground consequence of
    /// the write-back (`insert` always makes its key present), and its
    /// `^self` mention is load-bearing — the parent is mutated through the
    /// split borrow, so its carrier must ADVANCE (havoc) at the split site.
    /// Without any `^self` mention the parent would stay bound to its
    /// pre-split carrier and post-split asserts would be judged against
    /// stale entries — a confidently-wrong counterexample instead of an
    /// honest unknown.
    ///
    /// Args: self=arg0, key=arg1 (passed by ref)
    pub const SPLIT_MUT_GHOST: &str = r"
        params: self, arg1
        requires: self.contains(*arg1)
        ensures: *result.0 == self.lookup(*arg1)
        ensures: (^self).contains(*arg1)
        ensures: !(*result.1).contains(*arg1)
        ensures: (*result.1).len() == self.len() - 1
    ";

    /// Contract for `FMap::is_empty` (emptiness check)
    pub const IS_EMPTY: &str = r"
        params: self
        ensures: result == (self.len() == 0)
    ";

    /// Contract for `FMap::into_inner` (identity unwrap)
    pub const INTO_INNER: &str = r"
        params: self
        ensures: result == self
    ";

    /// Contract for `FMap::is_empty_ghost` (ghost-block emptiness check)
    pub const IS_EMPTY_GHOST: &str = r"
        params: self
        ensures: result == (self.len() == 0)
    ";

    /// Contract for `FMapGhostSplit::insert_ghost` (insert through split handle)
    ///
    /// Reference: Creusot `creusot-std/src/logic/fmap.rs:389-397` — the split
    /// handle is a plain `&mut FMap` there (`result.1` of `split_mut_ghost`,
    /// seeded with `*result.1 == (*self).remove(*key)`), so inserts through it
    /// carry `FMap::insert_ghost`'s own contract
    /// (`creusot-std/src/logic/fmap.rs:418-426`:
    /// `^self == (*self).insert(key, value)`, `result == (*self).get(key)`).
    /// The clauses below mirror `INSERT_GHOST` verbatim.
    ///
    /// `self`/`^self` here are the SPLIT VIEW's own state (the carrier bound
    /// to `result.1` of `split_mut_ghost`), NOT the parent map: the split
    /// view is the pin-removed map, and the parent's post-state is related to
    /// the split view only through the (unrendered) parent write-back
    /// `^parent == (^split).insert(pin, ^value_ref)` — which is what
    /// pin-shadows split-handle writes at the pinned key. Asserting these
    /// effects on the parent's carrier instead would smuggle the pinned-key
    /// insert past the pin (false premise on the parent).
    ///
    /// Args: self=arg0 (FMapGhostSplit), k=arg1, v=arg2
    pub const GHOST_SPLIT_INSERT: &str = r"
        params: self, arg1, arg2
        ensures: (^self).contains(arg1)
        ensures: (^self).lookup(arg1) == arg2
        ensures: forall<k2: _> k2 != arg1 ==> (^self).contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != arg1 && self.contains(k2) ==> (^self).lookup(k2) == self.lookup(k2)
        ensures: match result {
            Some(prev) => self.contains(arg1) && prev == self.lookup(arg1) && (^self).len() == self.len(),
            None => !self.contains(arg1) && (^self).len() == self.len() + 1,
        }
    ";

    /// Contract for `FMapGhostSplit::remove_ghost` (remove through split handle)
    ///
    /// Reference: Creusot `creusot-std/src/logic/fmap.rs:389-397` — the split
    /// handle is a plain `&mut FMap` there, so removes through it carry
    /// `FMap::remove_ghost`'s own contract
    /// (`creusot-std/src/logic/fmap.rs:443-450`:
    /// `^self == (*self).remove(*key)`, `result == (*self).get(*key)`).
    /// The clauses below mirror `REMOVE_GHOST` verbatim. As with
    /// `GHOST_SPLIT_INSERT`, `self`/`^self` are the split view's own state.
    ///
    /// Args: self=arg0 (FMapGhostSplit), k=arg1 (passed by ref)
    pub const GHOST_SPLIT_REMOVE: &str = r"
        params: self, arg1
        ensures: !(^self).contains(*arg1)
        ensures: forall<k2: _> k2 != *arg1 ==> (^self).contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != *arg1 && self.contains(k2) ==> (^self).lookup(k2) == self.lookup(k2)
        ensures: match result {
            Some(prev) => self.contains(*arg1) && prev == self.lookup(*arg1) && (^self).len() == self.len() - 1,
            None => !self.contains(*arg1) && (^self).len() == self.len(),
        }
    ";
}

// ── Iterator support ──────────────────────────────────────────────────

/// Owning iterator over an `FMap<K, V>`.
///
/// Produced by `FMap::into_iter()`. Yields `(K, V)` pairs in arbitrary order.
///
/// Reference: Creusot `creusot-std/src/logic/fmap.rs` `FMapIter`.
pub struct FMapIter<K, V> {
    inner: std::collections::hash_map::IntoIter<K, V>,
}

impl<K, V> IntoIterator for FMap<K, V> {
    type Item = (K, V);
    type IntoIter = FMapIter<K, V>;

    fn into_iter(self) -> FMapIter<K, V> {
        FMapIter {
            inner: self.map.into_iter(),
        }
    }
}

impl<K, V> Iterator for FMapIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> super::super::std::iter::IteratorSpec for FMapIter<K, V> {
    fn produces(self, visited: super::Seq<Self::Item>, o: Self) -> bool {
        let remaining = o.inner.size_hint().0;
        let total = self.inner.size_hint().0;
        super::Int::from(total) == visited.len() + super::Int::from(remaining)
    }

    fn completed(&mut self) -> bool {
        self.inner.size_hint().0 == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fmap_empty() {
        let map: FMap<i32, i32> = FMap::empty();
        assert!(map.is_empty());
        assert_eq!(map.len(), Int(0));
    }

    #[test]
    fn test_fmap_singleton() {
        let map = FMap::singleton(1, "one");
        assert!(!map.is_empty());
        assert_eq!(map.len(), Int(1));
        assert_eq!(map.get(1), Some(&"one"));
        assert_eq!(map.get(2), None);
    }

    #[test]
    fn test_fmap_insert() {
        let map: FMap<i32, i32> = FMap::empty();
        let map = map.insert(1, 10).insert(2, 20).insert(3, 30);
        assert_eq!(map.len(), Int(3));
        assert_eq!(map.lookup(1), 10);
        assert_eq!(map.lookup(2), 20);
        assert_eq!(map.lookup(3), 30);
    }

    #[test]
    fn test_fmap_insert_overwrite() {
        let map = FMap::singleton(1, 10);
        let map = map.insert(1, 42);
        assert_eq!(map.len(), Int(1));
        assert_eq!(map.lookup(1), 42);
    }

    #[test]
    fn test_fmap_remove() {
        let map = FMap::empty().insert(1, 10).insert(2, 20);
        let map = map.remove(1);
        assert_eq!(map.len(), Int(1));
        assert!(!map.contains(1));
        assert!(map.contains(2));
    }

    #[test]
    fn test_fmap_contains() {
        let map = FMap::singleton(1, 10);
        assert!(map.contains(1));
        assert!(!map.contains(2));
    }

    #[test]
    fn test_fmap_into_seq_matches_map() {
        let map_for_seq = FMap::empty().insert(1, 10).insert(2, 20);
        let map_for_check = HashMap::from([(1, 10), (2, 20)]);

        let seq = map_for_seq.into_seq();

        assert_eq!(seq.len(), 2);
        assert!(seq.matches_map(&map_for_check));
    }

    #[test]
    fn test_fmap_ext_eq() {
        let map1 = FMap::empty().insert(1, 10).insert(2, 20);
        let map2 = FMap::empty().insert(2, 20).insert(1, 10);
        let map3 = FMap::empty().insert(1, 10);
        let map4 = FMap::empty().insert(1, 999).insert(2, 20);
        assert!(map1.ext_eq(map2));
        assert!(!FMap::empty().insert(1, 10).insert(2, 20).ext_eq(map3));
        assert!(!FMap::empty().insert(1, 10).insert(2, 20).ext_eq(map4));
    }

    #[derive(Debug, PartialEq, Eq, Hash)]
    struct NonCloneKey(i32);

    #[derive(Debug, PartialEq, Eq)]
    struct NonCloneValue(&'static str);

    #[test]
    fn test_fmap_insert_remove_do_not_require_clone() {
        let map = FMap::empty()
            .insert(NonCloneKey(1), NonCloneValue("one"))
            .insert(NonCloneKey(2), NonCloneValue("two"));
        let map = map.remove(NonCloneKey(1));

        assert_eq!(map.len(), Int(1));
        assert!(!map.contains(NonCloneKey(1)));
        assert_eq!(map.get(NonCloneKey(2)), Some(&NonCloneValue("two")));
    }

    #[test]
    fn test_fmap_disjoint() {
        let map1 = FMap::empty().insert(1, 10).insert(2, 20);
        let map2 = FMap::empty().insert(3, 30).insert(4, 40);
        let map3 = FMap::empty().insert(2, 200).insert(5, 50);
        assert!(map1.disjoint(&map2));
        assert!(!map1.disjoint(&map3));
    }

    #[test]
    fn test_fmap_subset() {
        let map1 = FMap::empty().insert(1, 10);
        let map2 = FMap::empty().insert(1, 10).insert(2, 20);
        let map3 = FMap::empty().insert(1, 100);
        assert!(map1.subset(&map2));
        assert!(!map2.subset(&map1));
        assert!(!map1.subset(&map3)); // same key, different value
    }

    #[test]
    fn test_fmap_union() {
        let map1 = FMap::empty().insert(1, 10);
        let map2 = FMap::empty().insert(2, 20);
        let union = map1.union(map2);
        assert_eq!(union.len(), Int(2));
        assert_eq!(union.lookup(1), 10);
        assert_eq!(union.lookup(2), 20);
    }

    #[test]
    #[should_panic(expected = "disjoint")]
    fn test_fmap_union_not_disjoint() {
        let map1 = FMap::singleton(1, 10);
        let map2 = FMap::singleton(1, 20);
        let _ = map1.union(map2);
    }

    #[test]
    fn test_fmap_merge_preserves_non_overlapping_values() {
        let map1 = FMap::empty().insert(1, 10).insert(2, 20);
        let map2 = FMap::empty().insert(2, 200).insert(3, 30);
        let merged = map1.merge(map2, |(left, right)| left + right);

        assert_eq!(merged.len(), Int(3));
        assert_eq!(merged.lookup(1), 10);
        assert_eq!(merged.lookup(2), 220);
        assert_eq!(merged.lookup(3), 30);
    }

    #[test]
    fn test_split_mut_ghost_value_mutation() {
        let mut map = FMap::empty().insert(1, 10).insert(2, 20);
        {
            let (val, _split) = map.split_mut_ghost(&2);

            // The borrowed value is the one at the pinned key.
            assert_eq!(*val, 20);
            *val = 200;
        }
        // After the split scope ends, verify the map reflects the mutation.
        assert_eq!(map.lookup(2), 200);
    }

    /// Helper to end a mutable borrow by consuming the reference.
    fn end_borrow<T>(_: T) {}

    #[test]
    fn test_split_mut_ghost_insert_remove() {
        let mut map = FMap::empty().insert(1, 10).insert(2, 20).insert(3, 30);
        {
            let (val, mut split) = map.split_mut_ghost(&2);
            // Verify the pinned value, then end the &mut V borrow before
            // using split operations (split methods take &mut self).
            assert_eq!(*val, 20);
            end_borrow(val);

            // Insert/remove through the split works for non-pinned keys.
            split.insert_ghost(4, 40);
            split.remove_ghost(&1);
        }
        // After dropping both val and split, verify map state.
        assert!(!map.contains(1));
        assert!(map.contains(2));
        assert!(map.contains(3));
        assert!(map.contains(4));
        assert_eq!(map.lookup(4), 40);
    }

    #[test]
    fn test_split_mut_ghost_pinned_key_guard() {
        let mut map = FMap::empty().insert(1, 10).insert(2, 20);
        let (val, mut split) = map.split_mut_ghost(&1);

        // Pinned-key operations are rejected without touching the HashMap,
        // so they are safe even while val is alive.
        assert_eq!(split.insert_ghost(1, 999), None);
        assert_eq!(split.remove_ghost(&1), None);

        // End the &mut V borrow before non-pinned operations.
        end_borrow(val);

        // Non-pinned key operations still work.
        assert!(split.insert_ghost(2, 200).is_some());
    }

    #[test]
    fn test_split_mut_ghost_get_ghost() {
        let mut map = FMap::empty().insert(1, 10).insert(2, 20).insert(3, 30);
        let (_val, split) = map.split_mut_ghost(&1);

        // Can read non-pinned keys.
        assert_eq!(split.get_ghost(&2), Some(&20));
        assert_eq!(split.get_ghost(&3), Some(&30));

        // Pinned key returns None (exclusively borrowed through val).
        assert_eq!(split.get_ghost(&1), None);

        // Missing key returns None.
        assert_eq!(split.get_ghost(&99), None);
    }

    #[test]
    fn test_split_mut_ghost_get_mut_ghost() {
        let mut map = FMap::empty().insert(1, 10).insert(2, 20).insert(3, 30);
        let (val, mut split) = map.split_mut_ghost(&1);

        // Can mutate non-pinned keys.
        if let Some(v) = split.get_mut_ghost(&2) {
            *v = 200;
        }
        assert_eq!(split.get_ghost(&2), Some(&200));

        // Pinned key returns None.
        assert_eq!(split.get_mut_ghost(&1), None);

        // Missing key returns None.
        assert_eq!(split.get_mut_ghost(&99), None);

        // End the val borrow before drop.
        end_borrow(val);
    }

    #[test]
    #[should_panic(expected = "key to be present")]
    fn test_split_mut_ghost_missing_key_panics() {
        let mut map: FMap<i32, i32> = FMap::empty().insert(1, 10);
        let _ = map.split_mut_ghost(&99);
    }
}
