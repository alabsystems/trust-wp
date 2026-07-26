// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for iterator protocol methods.
//!
//! This module models the core iterator protocol used in contracts:
//! - `produces(visited, o)` tracks a transition from one iterator state to another
//! - `completed()` indicates that an iterator is exhausted
//!
//! These methods are used by std-spec contracts (for example `Iterator::next`) and
//! encoded in `trust-wp-ay` as logical predicates.
//!
//! # Driver-side lowering (#2172, #2238)
//!
//! For supported std iterator types, the driver rewrites `produces` and
//! `completed` calls to Seq-based formulas before SMT emission:
//!
//! - `Vec::IntoIter`: `it.produces(v, next)` → `it@.ext_eq(v.concat(next@))`
//! - `slice::IterMut`: snapshot-aware content-equality with `*visited[i]`
//!   deref for pre-mutation values (#2238)
//!
//! The Rust bodies below are runtime-testable placeholders and fallback
//! approximations. They are **not** the verification source of truth for
//! rewritten iterator types.

mod chain;
mod cloned;
mod copied;
mod empty;
mod enumerate;
mod filter;
mod filter_map;
mod fuse;
mod map;
mod map_inv;
mod once;
mod peekable;
mod range;
mod repeat;
mod rev;
mod skip;
pub mod specs;
mod take;
mod zip;

use std::{collections::HashMap, hash::Hash};

pub use chain::ChainExt;
pub use cloned::ClonedExt;
pub use copied::CopiedExt;
pub use enumerate::EnumerateExt;
pub use filter::FilterExt;
pub use filter_map::FilterMapExt;
pub use fuse::FuseExt;
pub use map::MapExt;
pub use map_inv::MapInv;
pub use peekable::PeekableExt;
pub use rev::RevExt;
pub use skip::SkipExt;
pub use take::TakeExt;
pub use zip::ZipExt;

use crate::{
    ghost::Snapshot,
    logic::{Int, Seq},
    std::vec::VecSpec,
    trusted,
};

/// Specification model for iterators.
///
/// This mirrors Creusot's core protocol methods and gives trust-wp contract
/// expressions stable method names (`produces`, `completed`) across iterator types.
pub trait IteratorSpec: Iterator + Sized {
    /// Relational production predicate.
    ///
    /// The default concrete model uses sequence-length conservation:
    /// `len(self) == len(visited) + len(o)`.
    ///
    /// Logic-mode in Creusot's design — implementers override with
    /// `#[logic(open)]`.
    #[crate::logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;

    /// Exhaustion predicate (`next()` will return `None`).
    ///
    /// Logic-mode (prophetic, because of `&mut self`) in Creusot.
    #[crate::logic(prophetic)]
    fn completed(&mut self) -> bool;

    /// Map with invariant: applies `func` to each element along with a snapshot
    /// of the elements produced so far.
    ///
    /// This is a Creusot-specific combinator that gives the mapping closure access
    /// to the production history, enabling invariant-carrying iteration patterns.
    ///
    /// Reference: `creusot-std/src/std/iter.rs` lines 57-63
    #[trusted]
    fn map_inv<B, F>(self, func: F) -> MapInv<Self, F>
    where
        F: FnMut(Self::Item, Snapshot<Seq<Self::Item>>) -> B,
    {
        MapInv {
            iter: self,
            func,
            produced: Snapshot::new_phantom(),
        }
    }
}

impl<T> IteratorSpec for std::vec::IntoIter<T> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }

    fn completed(&mut self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> IteratorSpec for std::slice::Iter<'a, T> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }

    fn completed(&mut self) -> bool {
        self.len() == 0
    }
}

/// Snapshot-aware `IteratorSpec` for `slice::IterMut`.
///
/// # Verification model (#2238)
///
/// At the SMT level, the driver rewrites `it.produces(visited, next)` to:
///
/// ```text
/// it@.len() == visited.len() + next@.len()
/// && forall<i: Int> 0 <= i && i < visited.len() ==>
///     *visited.index_logic(i) == it@.index_logic(i)
/// && forall<i: Int> 0 <= i && i < next@.len() ==>
///     next@.index_logic(i) == it@.index_logic(visited.len() + i)
/// ```
///
/// The `*visited[i]` (Deref) captures the **pre-mutation snapshot** of each
/// element. `IterMut` yields `&mut T` references, so dereferencing gives the
/// value at the time the reference was created — the "current" value in
/// separation logic terms. This matches the original container content
/// *before* any writes through the yielded reference.
///
/// Later writes through `&mut T` are described by the `^visited[i]` (Final)
/// notation in postconditions, not by the produced-history sequence.
///
/// # Runtime fallback
///
/// The runtime `produces` body uses length-only conservation because at
/// runtime, `self` (the iterator) no longer contains the already-yielded
/// prefix — there is no way to compare `visited` elements against the
/// original slice content. This is an intentional limitation of the runtime
/// approximation; the verification model (applied by the driver rewrite)
/// provides the stronger content-aware semantics.
impl<'a, T> IteratorSpec for std::slice::IterMut<'a, T> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }

    fn completed(&mut self) -> bool {
        self.len() == 0
    }
}

impl<K, V> IteratorSpec for std::collections::hash_map::IntoIter<K, V> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }

    fn completed(&mut self) -> bool {
        self.len() == 0
    }
}

impl<'a, K, V> IteratorSpec for std::collections::hash_map::Iter<'a, K, V> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }

    fn completed(&mut self) -> bool {
        self.len() == 0
    }
}

impl<'a, K, V> IteratorSpec for std::collections::hash_map::IterMut<'a, K, V> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }

    fn completed(&mut self) -> bool {
        self.len() == 0
    }
}

impl<I: IteratorSpec> IteratorSpec for &mut I {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable!()
    }

    fn completed(&mut self) -> bool {
        unreachable!()
    }
}

/// Specification model for collection construction from iterator history.
///
/// This is the receiver-style analogue of Creusot's `FromIterator` postcondition.
/// Creusot uses `B::from_iter_post(prod, result)` (static), but trust-wp uses
/// `result.from_iter_post(prod)` (receiver) because the current method-call
/// dispatch path resolves receiver-typed logic methods cleanly.
///
/// Reference: `creusot-std/src/std/iter.rs` — `FromIteratorSpec`
pub trait FromIteratorSpec<A>: FromIterator<A> {
    /// Postcondition relating the collected result to the production history.
    ///
    /// For `Vec<T>`: `self.from_iter_post(prod)` ≡ `self@.ext_eq(prod)`
    /// (the collected vector's view equals the produced element sequence).
    ///
    /// Marked `#[logic(open)]` so the impl body is inlined at call sites,
    /// allowing the encoder to reason about the structural relationship
    /// between the collected result and the produced sequence.
    #[allow(clippy::wrong_self_convention)] // Spec-only: name matches Creusot convention
    #[crate::logic(open)]
    fn from_iter_post(&self, prod: Seq<A>) -> bool;
}

impl<T: Clone + PartialEq> FromIteratorSpec<T> for Vec<T> {
    fn from_iter_post(&self, prod: Seq<T>) -> bool {
        self.view_spec().ext_eq(prod)
    }
}

impl<K, V> FromIteratorSpec<(K, V)> for HashMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn from_iter_post(&self, prod: Seq<(K, V)>) -> bool {
        self.len() == prod.len() && prod.matches_map(self)
    }
}

/// Specification model for double-ended (reversible) iterators.
///
/// Mirrors Creusot's `DoubleEndedIteratorSpec` — provides `produces_back`
/// which is the reverse analogue of `IteratorSpec::produces`.
///
/// For `Vec::IntoIter`:
/// - forward: `it.produces(visited, next)` ≡ `it@.ext_eq(visited.concat(next@))`
/// - reverse: `it.produces_back(visited, next)` ≡ `it@.ext_eq(next@.concat(visited.reverse()))`
///
/// Reference: `creusot-std/src/std/iter.rs` — `DoubleEndedIteratorSpec`
pub trait DoubleEndedIteratorSpec: DoubleEndedIterator + IteratorSpec {
    /// Reverse production predicate.
    ///
    /// `self.produces_back(visited, o)` means: starting from state `self`,
    /// consuming elements from the back yields `visited` (in consumption
    /// order), leaving iterator in state `o`.
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool;
}

impl<T> DoubleEndedIteratorSpec for std::vec::IntoIter<T> {
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        // Reverse: original content = remaining ++ reverse(visited)
        // Length-conservation fallback for runtime testing.
        Int::from(self.len()) == visited.len() + Int::from(o.len())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn test_into_iter_produces_len_partition() {
        let iter = vec![1, 2, 3].into_iter();
        let visited = Seq::from(vec![10, 20]);
        let tail = vec![30].into_iter();
        assert!(iter.produces(visited, tail));
    }

    #[test]
    fn test_into_iter_completed() {
        let mut iter = Vec::<i32>::new().into_iter();
        assert!(iter.completed());
    }

    #[test]
    fn test_slice_iter_produces_len_partition() {
        let data = [1, 2, 3];
        let iter = data.iter();
        let visited = Seq::from(vec![&data[0]]);
        let tail = data[1..].iter();
        assert!(iter.produces(visited, tail));
    }

    #[test]
    fn test_slice_iter_mut_completed() {
        let mut data: [i32; 0] = [];
        let mut iter = data.iter_mut();
        assert!(iter.completed());
    }

    #[test]
    fn test_slice_iter_mut_not_completed() {
        let mut data = [1i32, 2, 3];
        let mut iter = data.iter_mut();
        assert!(!iter.completed());
    }

    #[test]
    fn test_slice_iter_mut_produces_len_partition() {
        let mut data = [10i32, 20, 30];
        let iter = data.iter_mut();
        // Full length: 3 == 2 + 1
        let mut a = 10i32;
        let mut b = 20i32;
        let visited = Seq::from(vec![&mut a, &mut b]);
        let mut tail = [30i32];
        let remainder = tail.iter_mut();
        // The runtime fallback checks length only, not content.
        assert!(iter.produces(visited, remainder));
    }

    #[test]
    fn test_slice_iter_mut_produces_empty_visited() {
        let mut data = [10i32, 20, 30];
        let mut data2 = [10i32, 20, 30];
        let iter = data.iter_mut();
        // 0 elements visited, all 3 remaining
        let visited: Seq<&mut i32> = Seq::from(vec![]);
        let remainder = data2.iter_mut();
        assert!(iter.produces(visited, remainder));
    }

    #[test]
    fn test_slice_iter_mut_produces_all_visited() {
        let mut data = [10i32, 20, 30];
        let iter = data.iter_mut();
        // All 3 elements visited, none remaining
        let mut a = 10i32;
        let mut b = 20i32;
        let mut c = 30i32;
        let visited = Seq::from(vec![&mut a, &mut b, &mut c]);
        let mut empty: [i32; 0] = [];
        let remainder = empty.iter_mut();
        assert!(iter.produces(visited, remainder));
    }

    #[test]
    fn test_slice_iter_mut_produces_length_mismatch_rejected() {
        let mut data = [10i32, 20, 30];
        let iter = data.iter_mut(); // len 3
                                    // Only 1 visited + 1 remaining = 2 != 3
        let mut a = 10i32;
        let visited = Seq::from(vec![&mut a]);
        let mut tail = [20i32];
        let remainder = tail.iter_mut();
        assert!(!iter.produces(visited, remainder));
    }

    /// Demonstrates the snapshot-value invariant: dereferencing `&mut T`
    /// elements in the visited sequence gives the original pre-mutation
    /// values, even after the references are later mutated.
    ///
    /// At the SMT level, the driver rewrite enforces:
    /// `*visited[i] == it@[i]` -- the dereferenced visited element equals
    /// the iterator's original view at that position.
    #[test]
    fn test_slice_iter_mut_snapshot_deref_gives_original_value() {
        let mut data = [10i32, 20, 30];
        let mut iter = data.iter_mut();

        // Yield first two elements
        let first = iter.next().unwrap();
        assert_eq!(*first, 10); // pre-mutation snapshot
        let second = iter.next().unwrap();
        assert_eq!(*second, 20); // pre-mutation snapshot

        // Mutate through the yielded references
        *first = 100;
        *second = 200;

        // The snapshot values (*first at yield time) were 10 and 20,
        // NOT the post-mutation 100 and 200. The verification model
        // captures this: *visited[0] == 10, *visited[1] == 20,
        // while ^visited[0] == 100, ^visited[1] == 200.
        assert_eq!(data[0], 100); // post-mutation
        assert_eq!(data[1], 200); // post-mutation
        assert_eq!(data[2], 30); // untouched
    }

    /// Verifies that IterMut's completed predicate correctly transitions
    /// after consuming all elements.
    #[test]
    fn test_slice_iter_mut_completed_after_consumption() {
        let mut data = [1i32, 2];
        let mut iter = data.iter_mut();
        assert!(!iter.completed());
        let _ = iter.next(); // consume first
        assert!(!iter.completed());
        let _ = iter.next(); // consume second
        assert!(iter.completed()); // now exhausted
    }

    /// Verify the `VEC_ITER_MUT` spec (used by the driver for `iter_mut()`
    /// constructor calls) correctly seeds the view connection `result@ == self@`
    /// and the completed/non-completed state from source length.
    ///
    /// This is a Phase 3 test for #2238: the view-seeding postcondition is
    /// critical because the produces decomposition axiom relates visited
    /// elements to `it@[i]` — without `result@ == self@`, the solver cannot
    /// connect `it@` back to the original slice content.
    #[test]
    fn test_vec_iter_mut_spec_parses_and_seeds_view() {
        let spec = crate::std::test_shim::parse_spec_string(specs::VEC_ITER_MUT);
        assert!(
            spec.requires.is_empty(),
            "iter_mut should have no preconditions"
        );
        assert_eq!(
            spec.ensures.len(),
            3,
            "iter_mut should have 3 postconditions: view seed + completed + non-completed"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@") && e.contains("self@")),
            "iter_mut must seed the view connection result@ == self@ for #2238"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("completed()")),
            "iter_mut must constrain the completed state from source length"
        );
    }

    // Range content-aware produces
    #[test]
    fn test_range_produces_content_aware() {
        let range = 0i32..5;
        let visited = Seq::from(vec![0i32, 1, 2]);
        let tail = 3i32..5;
        assert!(range.produces(visited, tail));
    }

    #[test]
    fn test_range_produces_empty_visited() {
        let range = 3i32..7;
        let visited = Seq::from(vec![]);
        let tail = 3i32..7;
        assert!(range.produces(visited, tail));
    }

    #[test]
    fn test_range_produces_wrong_element_rejected() {
        let range = 0i32..5;
        // visited has wrong element value (99 instead of 0)
        let visited = Seq::from(vec![99i32]);
        let tail = 1i32..5;
        assert!(!range.produces(visited, tail));
    }

    #[test]
    fn test_range_completed() {
        let mut empty_range = 5i32..5;
        assert!(empty_range.completed());

        let mut nonempty_range = 0i32..3;
        assert!(!nonempty_range.completed());
    }

    // Empty iterator
    #[test]
    fn test_empty_produces() {
        let e = std::iter::empty::<i32>();
        let visited = Seq::from(vec![]);
        let next = std::iter::empty::<i32>();
        assert!(e.produces(visited, next));
    }

    #[test]
    fn test_empty_completed() {
        let mut e = std::iter::empty::<i32>();
        assert!(e.completed());
    }

    // Once iterator
    #[test]
    fn test_once_produces_nothing() {
        let o = std::iter::once(42i32);
        let visited = Seq::from(vec![]);
        let next = std::iter::once(42i32);
        assert!(o.produces(visited, next));
    }

    #[test]
    fn test_once_produces_one_element() {
        let o = std::iter::once(42i32);
        let visited = Seq::from(vec![42i32]);
        let next = std::iter::once(42i32);
        assert!(o.produces(visited, next));
    }

    // Repeat iterator
    #[test]
    fn test_repeat_produces() {
        let r = std::iter::repeat(7i32);
        let visited = Seq::from(vec![7i32, 7, 7]);
        let next = std::iter::repeat(7i32);
        assert!(r.produces(visited, next));
    }

    #[test]
    fn test_repeat_never_completed() {
        let mut r = std::iter::repeat(7i32);
        assert!(!r.completed());
    }

    #[test]
    fn test_fuse_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_FUSE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("result.iter() == self"));
    }

    #[test]
    fn test_cloned_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_CLONED);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("result.iter() == self"));
    }

    #[test]
    fn test_copied_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_COPIED);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.iter() == self")));
        assert!(spec.ensures.iter().any(|e| e.contains("result@ == self@")));
    }

    #[test]
    fn test_skip_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_SKIP);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.iter() == self")));
        assert!(spec.ensures.iter().any(|e| e.contains("result.n() == n")));
    }

    #[test]
    fn test_enumerate_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_ENUMERATE);
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.requires.iter().any(|r| r.contains("completed()")));
        assert!(spec
            .requires
            .iter()
            .any(|r| r.contains("core::usize::MAX@")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.iter() == self")));
        assert!(spec.ensures.iter().any(|e| e.contains("result.n()@ == 0")));
    }

    #[test]
    fn test_zip_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_ZIP);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.requires[0].contains("U::into_iter.precondition"));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.itera() == self")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("U::into_iter.postcondition")));
    }

    // FromIteratorSpec tests
    #[test]
    fn test_vec_from_iter_post_matching() {
        let v = vec![1i32, 2, 3];
        let prod = Seq::from(vec![1i32, 2, 3]);
        assert!(v.from_iter_post(prod));
    }

    #[test]
    fn test_vec_from_iter_post_empty() {
        let v: Vec<i32> = vec![];
        let prod = Seq::from(vec![]);
        assert!(v.from_iter_post(prod));
    }

    #[test]
    fn test_vec_from_iter_post_mismatch() {
        let v = vec![1i32, 2, 3];
        let prod = Seq::from(vec![4i32, 5, 6]);
        assert!(!v.from_iter_post(prod));
    }

    #[test]
    fn test_vec_from_iter_post_length_mismatch() {
        let v = vec![1i32, 2];
        let prod = Seq::from(vec![1i32, 2, 3]);
        assert!(!v.from_iter_post(prod));
    }

    #[test]
    fn test_hashmap_from_iter_post_matching() {
        let mut map = HashMap::new();
        map.insert(1i32, "one");
        map.insert(2i32, "two");
        let prod = Seq::from(vec![(1i32, "one"), (2i32, "two")]);
        assert!(map.from_iter_post(prod));
    }

    #[test]
    fn test_hashmap_from_iter_post_mismatch() {
        let mut map = HashMap::new();
        map.insert(1i32, "one");
        let prod = Seq::from(vec![(1i32, "uno")]);
        assert!(!map.from_iter_post(prod));
    }

    #[test]
    fn test_hashmap_into_iter_spec_len_only() {
        let map = HashMap::from([(1i32, "one"), (2i32, "two")]);
        let it = map.clone().into_iter();
        let mut o = map.into_iter();
        let _ = o.next();
        let visited = Seq::from(vec![(1i32, "one")]);

        assert!(it.produces(visited, o));
    }

    #[test]
    fn test_hashmap_iter_spec_len_only() {
        let map = HashMap::from([(1i32, 10i32), (2i32, 20i32)]);
        let it = map.iter();
        let mut o = map.iter();
        let _ = o.next();
        let visited = Seq::from(vec![(&1i32, &10i32)]);

        assert!(it.produces(visited, o));
    }

    #[test]
    fn test_collect_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITERATOR_COLLECT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(
            spec.ensures.iter().any(|e| e.contains("from_iter_post")),
            "ITERATOR_COLLECT should keep from_iter_post bridge"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ == self@")),
            "ITERATOR_COLLECT should include extensional view round-trip"
        );
    }

    #[test]
    fn test_vec_from_iter_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::VEC_FROM_ITER);
        assert!(!spec.ensures.is_empty());
        assert!(
            spec.ensures.iter().any(|e| e.contains("from_iter_post")),
            "Vec from_iter spec should reference from_iter_post; got {:?}",
            spec.ensures
        );
    }

    // DoubleEndedIteratorSpec tests
    #[test]
    fn test_into_iter_produces_back_len_partition() {
        let iter = vec![1, 2, 3].into_iter();
        let visited = Seq::from(vec![10, 20]);
        let tail = vec![30].into_iter();
        assert!(iter.produces_back(visited, tail));
    }

    #[test]
    fn test_rev_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITERATOR_REV);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("result.iter() == self"));
    }

    #[test]
    fn test_next_back_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::DOUBLE_ENDED_NEXT_BACK);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("produces_back"));
    }

    // Map adapter spec
    #[test]
    fn test_map_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_MAP);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.iter() == self")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.func() == f")));
    }

    // Filter adapter spec
    #[test]
    fn test_filter_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_FILTER);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.iter() == self")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.func() == f")));
    }

    // FilterMap adapter spec
    #[test]
    fn test_filter_map_spec_parses() {
        let spec = crate::std::test_shim::parse_spec_string(specs::ITER_FILTER_MAP);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.iter() == self")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.func() == f")));
    }
}
