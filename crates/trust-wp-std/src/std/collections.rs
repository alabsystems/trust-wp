// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::collections` types (`HashMap`, `HashSet`)
//!
//! These specs define verification contracts for the standard library's
//! hash-based collection types. At the SMT level, `HashMap` is modeled
//! via its view `@` as an `FMap<K, V>`, and `HashSet` via `@` as `FSet<T>`.
//!
//! Reference: Creusot `creusot-contracts/src/std/collections.rs`

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
#[doc(hidden)]
pub mod specs {
    /// Contract for `HashMap::new`
    pub const HASHMAP_NEW: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `HashMap::with_capacity`
    pub const HASHMAP_WITH_CAPACITY: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `HashMap::len`
    pub const HASHMAP_LEN: &str = r"
        ensures: result@ == self@.len()
    ";

    /// Contract for `HashMap::is_empty`
    pub const HASHMAP_IS_EMPTY: &str = r"
        ensures: result == (self@.len() == 0)
    ";

    /// Contract for `HashMap::insert`
    pub const HASHMAP_INSERT: &str = r"
        params: self, k, v
        ensures: (^self)@.contains(k)
        ensures: (^self)@.lookup(k) == v
        ensures: match result {
            Some(old) => self@.contains(k) && old == self@.lookup(k) && (^self)@.len() == self@.len(),
            None => !self@.contains(k) && (^self)@.len() == self@.len() + 1,
        }
    ";

    /// Contract for `HashMap::remove`
    pub const HASHMAP_REMOVE: &str = r"
        params: self, k
        ensures: !(^self)@.contains(*k)
        ensures: match result {
            Some(old) => self@.contains(*k) && old == self@.lookup(*k) && (^self)@.len() == self@.len() - 1,
            None => !self@.contains(*k) && (^self)@.len() == self@.len(),
        }
    ";

    /// Contract for `HashMap::get`
    pub const HASHMAP_GET: &str = r"
        params: self, k
        ensures: match result {
            Some(v) => self@.contains(*k) && *v == self@.lookup(*k),
            None => !self@.contains(*k),
        }
    ";

    /// Contract for `HashMap::get_mut`
    pub const HASHMAP_GET_MUT: &str = r"
        params: self, k
        ensures: match result {
            Some(v) => self@.contains(*k) && *v == self@.lookup(*k),
            None => !self@.contains(*k),
        }
    ";

    /// Contract for `HashMap::contains_key`
    pub const HASHMAP_CONTAINS_KEY: &str = r"
        params: self, k
        ensures: result == self@.contains(*k)
    ";

    /// Contract for `HashMap::clear`
    pub const HASHMAP_CLEAR: &str = r"
        ensures: (^self)@.len() == 0
    ";

    /// Contract for `HashMap::iter`
    pub const HASHMAP_ITER: &str = r"
        ensures: self@ == result@
    ";

    /// Contract for `HashMap::iter_mut`
    ///
    /// Mirrors Creusot's `HashMap::iter_mut` extern spec
    /// (`reference/creusot/creusot-std/src/std/collections/hash_map.rs:29-32`).
    /// The prophecy-threading clauses are written in both `get(k) == Some(v)`
    /// and `[k]`/`lookup(k)` forms so the encoder can match either trigger
    /// pattern when reasoning about `it.collect()` callers. This is what
    /// `roundtrip_hashmap_iter_mut`
    /// (`tests/should_succeed/cc/collections.rs`) needs to relate `^xs@`
    /// through the iterator into `^result@[k]` after `it.collect()` —
    /// because `ITERATOR_COLLECT` provides `r@ == it@`, identifying the
    /// HashMap's view with the IterMut's view at the collect call site.
    pub const HASHMAP_ITER_MUT: &str = r"
        ensures: self@ == result@
        ensures: forall<k: _> self@.contains(k) == (^self)@.contains(k)
        ensures: forall<k: _> self@.contains(k) == result@.contains(k)
        ensures: forall<k: _> self@.contains(k) ==> *result@[k] == self@[k] && ^result@[k] == (^self)@[k]
        ensures: forall<k: _, v: _> self@.get(k) == Some(v) ==> result@.contains(k) && *result@[k] == v
        ensures: forall<k: _, v: _> (^self)@.get(k) == Some(v) ==> result@.contains(k) && ^result@[k] == v
    ";

    /// Contract for `HashMap::into_iter` (owned and reference forms)
    pub const HASHMAP_INTO_ITER: &str = r"
        params: self
        ensures: self@ == result@
    ";

    /// Contract for `HashMap::into_iter` on `&mut HashMap`
    pub const HASHMAP_INTO_ITER_MUT: &str = r"
        params: self
        ensures: forall<k: _> (*self)@.contains(k) == (^self)@.contains(k)
        ensures: forall<k: _> (*self)@.contains(k) == result@.contains(k)
    ";

    /// Contract for `HashSet::new`
    pub const HASHSET_NEW: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `HashSet::with_capacity`
    pub const HASHSET_WITH_CAPACITY: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `HashSet::len`
    pub const HASHSET_LEN: &str = r"
        ensures: result@ == self@.len()
    ";

    /// Contract for `HashSet::is_empty`
    pub const HASHSET_IS_EMPTY: &str = r"
        ensures: result == (self@.len() == 0)
    ";

    /// Contract for `HashSet::insert`
    pub const HASHSET_INSERT: &str = r"
        ensures: (^self)@.contains(value)
        ensures: result == !self@.contains(value)
        ensures: result ==> (^self)@.len() == self@.len() + 1
        ensures: !result ==> (^self)@.len() == self@.len()
    ";

    /// Contract for `HashSet::remove`
    pub const HASHSET_REMOVE: &str = r"
        ensures: !(^self)@.contains(*value)
        ensures: result == self@.contains(*value)
        ensures: result ==> (^self)@.len() == self@.len() - 1
        ensures: !result ==> (^self)@.len() == self@.len()
    ";

    /// Contract for `HashSet::contains`
    pub const HASHSET_CONTAINS: &str = r"
        ensures: result == self@.contains(*value)
    ";

    /// Contract for `HashSet::clear`
    pub const HASHSET_CLEAR: &str = r"
        ensures: (^self)@.len() == 0
    ";

    /// Contract for `HashSet::iter`
    pub const HASHSET_ITER: &str = r"
        ensures: self@ == result@
    ";

    /// Contract for `HashSet::into_iter` (owned and reference forms)
    pub const HASHSET_INTO_ITER: &str = r"
        params: self
        ensures: self@ == result@
    ";

    /// Contract for `HashSet::intersection`
    pub const HASHSET_INTERSECTION: &str = r"
        params: self, other
        ensures: result@ == self@.intersection(other@)
    ";

    /// Contract for `HashSet::difference`
    pub const HASHSET_DIFFERENCE: &str = r"
        params: self, other
        ensures: result@ == self@.difference(other@)
    ";

    /// Contract for `<HashMap as FromIterator>::from_iter` (i.e. `Iterator::collect()`)
    ///
    /// When collecting an iterator into a `HashMap`, the collected result's
    /// logical map view satisfies the reusable `FromIteratorSpec` bridge. This
    /// closes the roundtrip gap: `into_iter` seeds the iterator history, and
    /// `from_iter_post` carries the produced `(K, V)` sequence into the map
    /// membership relation needed by `collect()` proofs. (#2116)
    pub const HASHMAP_FROM_ITER: &str = r"
        params: iter
        ensures: result.from_iter_post(iter@)
    ";

    /// Contract for `<HashSet as FromIterator>::from_iter` (i.e. `Iterator::collect()`)
    pub const HASHSET_FROM_ITER: &str = r"
        params: iter
        ensures: result@ == iter@
    ";

    // ── BTreeMap specs ──────────────────────────────────────────────

    /// Contract for `BTreeMap::new`
    pub const BTREEMAP_NEW: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `BTreeMap::len`
    pub const BTREEMAP_LEN: &str = r"
        ensures: result@ == self@.len()
    ";

    /// Contract for `BTreeMap::is_empty`
    pub const BTREEMAP_IS_EMPTY: &str = r"
        ensures: result == (self@.len() == 0)
    ";

    /// Contract for `BTreeMap::insert`
    pub const BTREEMAP_INSERT: &str = r"
        params: self, k, v
        ensures: (^self)@.contains(k)
        ensures: (^self)@.lookup(k) == v
        ensures: match result {
            Some(old) => self@.contains(k) && old == self@.lookup(k) && (^self)@.len() == self@.len(),
            None => !self@.contains(k) && (^self)@.len() == self@.len() + 1,
        }
    ";

    /// Contract for `BTreeMap::remove`
    pub const BTREEMAP_REMOVE: &str = r"
        params: self, k
        ensures: !(^self)@.contains(*k)
        ensures: match result {
            Some(old) => self@.contains(*k) && old == self@.lookup(*k) && (^self)@.len() == self@.len() - 1,
            None => !self@.contains(*k) && (^self)@.len() == self@.len(),
        }
    ";

    /// Contract for `BTreeMap::get`
    pub const BTREEMAP_GET: &str = r"
        params: self, k
        ensures: match result {
            Some(v) => self@.contains(*k) && *v == self@.lookup(*k),
            None => !self@.contains(*k),
        }
    ";

    /// Contract for `BTreeMap::get_mut`
    pub const BTREEMAP_GET_MUT: &str = r"
        params: self, k
        ensures: match result {
            Some(v) => self@.contains(*k) && *v == self@.lookup(*k),
            None => !self@.contains(*k),
        }
    ";

    /// Contract for `BTreeMap::contains_key`
    pub const BTREEMAP_CONTAINS_KEY: &str = r"
        params: self, k
        ensures: result == self@.contains(*k)
    ";

    /// Contract for `BTreeMap::clear`
    pub const BTREEMAP_CLEAR: &str = r"
        ensures: (^self)@.len() == 0
    ";

    /// Contract for `BTreeMap::iter`
    pub const BTREEMAP_ITER: &str = r"
        ensures: self@ == result@
    ";

    /// Contract for `BTreeMap::keys`
    pub const BTREEMAP_KEYS: &str = r"
        params: self
    ";

    /// Contract for `BTreeMap::values`
    pub const BTREEMAP_VALUES: &str = r"
        params: self
    ";

    /// Contract for `BTreeMap::into_iter`
    pub const BTREEMAP_INTO_ITER: &str = r"
        params: self
        ensures: self@ == result@
    ";

    // ── BTreeSet specs ──────────────────────────────────────────────

    /// Contract for `BTreeSet::new`
    pub const BTREESET_NEW: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `BTreeSet::len`
    pub const BTREESET_LEN: &str = r"
        ensures: result@ == self@.len()
    ";

    /// Contract for `BTreeSet::is_empty`
    pub const BTREESET_IS_EMPTY: &str = r"
        ensures: result == (self@.len() == 0)
    ";

    /// Contract for `BTreeSet::insert`
    pub const BTREESET_INSERT: &str = r"
        ensures: (^self)@.contains(value)
        ensures: result == !self@.contains(value)
        ensures: result ==> (^self)@.len() == self@.len() + 1
        ensures: !result ==> (^self)@.len() == self@.len()
    ";

    /// Contract for `BTreeSet::remove`
    pub const BTREESET_REMOVE: &str = r"
        ensures: !(^self)@.contains(*value)
        ensures: result == self@.contains(*value)
        ensures: result ==> (^self)@.len() == self@.len() - 1
        ensures: !result ==> (^self)@.len() == self@.len()
    ";

    /// Contract for `BTreeSet::contains`
    pub const BTREESET_CONTAINS: &str = r"
        ensures: result == self@.contains(*value)
    ";

    /// Contract for `BTreeSet::clear`
    pub const BTREESET_CLEAR: &str = r"
        ensures: (^self)@.len() == 0
    ";

    /// Contract for `BTreeSet::iter`
    pub const BTREESET_ITER: &str = r"
        ensures: self@ == result@
    ";

    /// Contract for `BTreeSet::into_iter`
    pub const BTREESET_INTO_ITER: &str = r"
        params: self
        ensures: self@ == result@
    ";

    // ── HashMap additional methods ──────────────────────────────────

    /// Contract for `HashMap::keys`
    pub const HASHMAP_KEYS: &str = r"
        params: self
    ";

    /// Contract for `HashMap::values`
    pub const HASHMAP_VALUES: &str = r"
        params: self
    ";

    /// Contract for `HashMap::retain`
    pub const HASHMAP_RETAIN: &str = r"
        params: self, f
        ensures: (^self)@.len() <= self@.len()
    ";

    /// Contract for `HashMap::entry`
    pub const HASHMAP_ENTRY: &str = r"
        params: self, key
    ";

    /// Contract for `HashSet::retain`
    pub const HASHSET_RETAIN: &str = r"
        params: self, f
        ensures: (^self)@.len() <= self@.len()
    ";

    /// Contract for `HashSet::union`
    pub const HASHSET_UNION: &str = r"
        params: self, other
        ensures: result@ == self@.union(other@)
    ";

    /// Contract for `HashSet::is_subset`
    pub const HASHSET_IS_SUBSET: &str = r"
        params: self, other
        ensures: result == self@.is_subset(other@)
    ";

    /// Contract for `HashSet::is_superset`
    pub const HASHSET_IS_SUPERSET: &str = r"
        params: self, other
        ensures: result == other@.is_subset(self@)
    ";

    /// Contract for `HashSet::is_disjoint`
    pub const HASHSET_IS_DISJOINT: &str = r"
        params: self, other
        ensures: result == (self@.intersection(other@).len() == 0)
    ";

    // ── BTreeMap additional methods ────────────────────────────────

    /// Contract for `BTreeMap::iter_mut`
    pub const BTREEMAP_ITER_MUT: &str = r"
        params: self
        ensures: self@ == result@
    ";

    /// Contract for `BTreeMap::retain`
    pub const BTREEMAP_RETAIN: &str = r"
        params: self, f
        ensures: (^self)@.len() <= self@.len()
    ";

    /// Contract for `BTreeMap::entry`
    pub const BTREEMAP_ENTRY: &str = r"
        params: self, key
    ";

    /// Contract for `BTreeMap::into_keys`
    pub const BTREEMAP_INTO_KEYS: &str = r"
        params: self
    ";

    /// Contract for `BTreeMap::into_values`
    pub const BTREEMAP_INTO_VALUES: &str = r"
        params: self
    ";

    /// Contract for `BTreeMap::from_iter` (FromIterator)
    pub const BTREEMAP_FROM_ITER: &str = r"
        params: iter
        ensures: result@ == iter@
    ";

    // ── BTreeSet additional methods ────────────────────────────────

    /// Contract for `BTreeSet::retain`
    pub const BTREESET_RETAIN: &str = r"
        params: self, f
        ensures: (^self)@.len() <= self@.len()
    ";

    /// Contract for `BTreeSet::intersection`
    pub const BTREESET_INTERSECTION: &str = r"
        params: self, other
        ensures: result@ == self@.intersection(other@)
    ";

    /// Contract for `BTreeSet::difference`
    pub const BTREESET_DIFFERENCE: &str = r"
        params: self, other
        ensures: result@ == self@.difference(other@)
    ";

    /// Contract for `BTreeSet::union`
    pub const BTREESET_UNION: &str = r"
        params: self, other
        ensures: result@ == self@.union(other@)
    ";

    /// Contract for `BTreeSet::is_subset`
    pub const BTREESET_IS_SUBSET: &str = r"
        params: self, other
        ensures: result == self@.is_subset(other@)
    ";

    /// Contract for `BTreeSet::is_superset`
    pub const BTREESET_IS_SUPERSET: &str = r"
        params: self, other
        ensures: result == other@.is_subset(self@)
    ";

    /// Contract for `BTreeSet::is_disjoint`
    pub const BTREESET_IS_DISJOINT: &str = r"
        params: self, other
        ensures: result == (self@.intersection(other@).len() == 0)
    ";

    /// Contract for `BTreeSet::from_iter` (FromIterator)
    pub const BTREESET_FROM_ITER: &str = r"
        params: iter
        ensures: result@ == iter@
    ";

    // ── HashMap Entry API ──────────────────────────────────────────

    /// Contract for `HashMap::Entry::or_insert` — inserts default if vacant.
    pub const HASHMAP_ENTRY_OR_INSERT: &str = r"
        params: self, default
    ";

    /// Contract for `HashMap::Entry::or_insert_with` — inserts computed default if vacant.
    pub const HASHMAP_ENTRY_OR_INSERT_WITH: &str = r"
        params: self, default
    ";

    /// Contract for `HashMap::Entry::or_default` — inserts Default::default if vacant.
    pub const HASHMAP_ENTRY_OR_DEFAULT: &str = r"
        params: self
    ";

    /// Contract for `HashMap::Entry::and_modify` — modifies occupied entry.
    pub const HASHMAP_ENTRY_AND_MODIFY: &str = r"
        params: self, f
    ";

    /// Contract for `HashMap::Entry::key` — returns reference to the key.
    pub const HASHMAP_ENTRY_KEY: &str = r"
        params: self
    ";

    // ── HashMap additional methods ────────────────────────────────

    /// Contract for `HashMap::values_mut`
    pub const HASHMAP_VALUES_MUT: &str = r"
        params: self
    ";

    /// Contract for `HashMap::into_keys` — consumes map, returns key iterator.
    pub const HASHMAP_INTO_KEYS: &str = r"
        params: self
    ";

    /// Contract for `HashMap::into_values` — consumes map, returns value iterator.
    pub const HASHMAP_INTO_VALUES: &str = r"
        params: self
    ";

    /// Contract for `HashMap::drain` — removes all entries, returns drain iterator.
    pub const HASHMAP_DRAIN: &str = r"
        params: self
        ensures: (^self)@.len() == 0
    ";

    /// Contract for `<HashMap as Extend>::extend` — extends map from iterator.
    pub const HASHMAP_EXTEND: &str = r"
        params: self, iter
    ";

    /// Contract for `HashSet::extend` — extends set from iterator.
    pub const HASHSET_EXTEND: &str = r"
        params: self, iter
    ";

    // ── BTreeMap Entry API ────────────────────────────────────────

    /// Contract for `BTreeMap::Entry::or_insert`
    pub const BTREEMAP_ENTRY_OR_INSERT: &str = r"
        params: self, default
    ";

    /// Contract for `BTreeMap::Entry::or_insert_with`
    pub const BTREEMAP_ENTRY_OR_INSERT_WITH: &str = r"
        params: self, default
    ";

    /// Contract for `BTreeMap::Entry::or_default`
    pub const BTREEMAP_ENTRY_OR_DEFAULT: &str = r"
        params: self
    ";

    /// Contract for `BTreeMap::Entry::and_modify`
    pub const BTREEMAP_ENTRY_AND_MODIFY: &str = r"
        params: self, f
    ";

    /// Contract for `BTreeMap::Entry::key`
    pub const BTREEMAP_ENTRY_KEY: &str = r"
        params: self
    ";

    /// Contract for `BTreeMap::values_mut`
    pub const BTREEMAP_VALUES_MUT: &str = r"
        params: self
    ";

    // ── VecDeque specs ────────────────────────────────────────────

    /// Contract for `VecDeque::new`
    pub const VECDEQUE_NEW: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `VecDeque::with_capacity`
    pub const VECDEQUE_WITH_CAPACITY: &str = r"
        ensures: result@.len() == 0
    ";

    /// Contract for `VecDeque::len`
    pub const VECDEQUE_LEN: &str = r"
        ensures: result@ == self@.len()
    ";

    /// Contract for `VecDeque::is_empty`
    pub const VECDEQUE_IS_EMPTY: &str = r"
        ensures: result == (self@.len() == 0)
    ";

    /// Contract for `VecDeque::push_back`
    pub const VECDEQUE_PUSH_BACK: &str = r"
        params: self, value
        ensures: (^self)@.len() == self@.len() + 1
    ";

    /// Contract for `VecDeque::push_front`
    pub const VECDEQUE_PUSH_FRONT: &str = r"
        params: self, value
        ensures: (^self)@.len() == self@.len() + 1
    ";

    /// Contract for `VecDeque::pop_back`
    pub const VECDEQUE_POP_BACK: &str = r"
        ensures: match result {
            Some(_) => self@.len() > 0 && (^self)@.len() == self@.len() - 1,
            None => self@.len() == 0 && (^self)@ == self@,
        }
    ";

    /// Contract for `VecDeque::pop_front`
    pub const VECDEQUE_POP_FRONT: &str = r"
        ensures: match result {
            Some(_) => self@.len() > 0 && (^self)@.len() == self@.len() - 1,
            None => self@.len() == 0 && (^self)@ == self@,
        }
    ";

    /// Contract for `VecDeque::clear`
    pub const VECDEQUE_CLEAR: &str = r"
        ensures: (^self)@.len() == 0
    ";

    /// Contract for `VecDeque::contains`
    pub const VECDEQUE_CONTAINS: &str = r"
        params: self, x
    ";

    /// Contract for `VecDeque::get`
    pub const VECDEQUE_GET: &str = r"
        params: self, index
    ";

    /// Contract for `VecDeque::iter`
    pub const VECDEQUE_ITER: &str = r"
        ensures: self@ == result@
    ";

    /// Contract for `VecDeque::into_iter`
    pub const VECDEQUE_INTO_ITER: &str = r"
        params: self
        ensures: self@ == result@
    ";

    /// Contract for `VecDeque::drain`
    pub const VECDEQUE_DRAIN: &str = r"
        params: self, range
    ";

    // ── HashMap Index/IndexMut ─────────────────────────────────────

    /// Contract for `HashMap::index` (Index trait impl)
    pub const HASHMAP_INDEX: &str = r"
        params: self, key
        requires: self@.contains(key@)
        ensures: self@.get(key@) == Some(result)
    ";

    /// Contract for `HashMap::index_mut` (IndexMut trait impl)
    pub const HASHMAP_INDEX_MUT: &str = r"
        params: self, key
        requires: self@.contains(key@)
        ensures: self@.get(key@) == Some(*result)
    ";
}

#[cfg(test)]
mod tests {
    use super::specs::*;

    #[test]
    fn test_hashmap_new_spec_parses() {
        assert!(HASHMAP_NEW.contains("ensures"));
        assert!(HASHMAP_NEW.contains("result@.len() == 0"));
    }

    #[test]
    fn test_hashmap_insert_spec_parses() {
        assert!(HASHMAP_INSERT.contains("ensures"));
        assert!(HASHMAP_INSERT.contains("(^self)@.contains(k)"));
    }

    #[test]
    fn test_hashset_new_spec_parses() {
        assert!(HASHSET_NEW.contains("ensures"));
        assert!(HASHSET_NEW.contains("result@.len() == 0"));
    }

    #[test]
    fn test_hashset_insert_spec_parses() {
        assert!(HASHSET_INSERT.contains("ensures"));
        assert!(HASHSET_INSERT.contains("(^self)@.contains(value)"));
    }

    #[test]
    fn test_hashmap_iter_spec_parses() {
        assert!(HASHMAP_ITER.contains("ensures"));
        assert!(HASHMAP_ITER.contains("self@ == result@"));
    }

    #[test]
    fn test_hashmap_iter_mut_spec_parses() {
        assert!(HASHMAP_ITER_MUT.contains("ensures"));
        // Membership-equivalence between self / ^self / result views.
        assert!(HASHMAP_ITER_MUT.contains("self@.contains(k) == (^self)@.contains(k)"));
        // Prophecy-threading clause (see roundtrip_hashmap_iter_mut).
        assert!(HASHMAP_ITER_MUT.contains("^result@[k] == (^self)@[k]"));
        assert!(HASHMAP_ITER_MUT.contains("(^self)@.get(k) == Some(v)"));
    }

    #[test]
    fn test_hashset_intersection_spec_parses() {
        assert!(HASHSET_INTERSECTION.contains("ensures"));
        assert!(HASHSET_INTERSECTION.contains("intersection"));
    }

    #[test]
    fn test_hashmap_from_iter_spec_parses() {
        assert!(HASHMAP_FROM_ITER.contains("ensures"));
        assert!(HASHMAP_FROM_ITER.contains("from_iter_post"));
        assert!(HASHMAP_FROM_ITER.contains("params: iter"));
    }

    #[test]
    fn test_hashset_from_iter_spec_parses() {
        assert!(HASHSET_FROM_ITER.contains("ensures"));
        assert!(HASHSET_FROM_ITER.contains("result@ == iter@"));
        assert!(HASHSET_FROM_ITER.contains("params: iter"));
    }
}
