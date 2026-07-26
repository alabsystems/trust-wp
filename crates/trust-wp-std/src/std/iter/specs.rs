// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Internal specification definitions for trust-wp-driver lookup.

/// Contract for `Iterator::next`.
pub const ITERATOR_NEXT: &str = r"
    params: self
    ensures: match result {
        None => self.completed(),
        Some(v) => (*self).produces(seq![v], ^self),
    }
";

/// Contract for `Vec::iter` (and slice `iter` aliases).
///
/// Seeds the iterator's view from the source collection's content and
/// seeds the completed/non-completed state from the source length.
/// The `result@ == self@` postcondition connects the iterator's view to
/// the original slice content, enabling the produces decomposition axiom
/// to relate visited elements back to the source. (#2238)
pub const VEC_ITER: &str = r"
    params: self
    ensures: result@ == self@
    ensures: self@.len() == 0 ==> result.completed()
    ensures: self@.len() > 0 ==> !result.completed()
";

/// Contract for `Vec::iter_mut` (and slice `iter_mut` aliases).
///
/// Seeds the iterator's completed/non-completed state from the source
/// collection's length **and connects the iterator's view to the source
/// collection's content** via `result@ == self@`. This view-seeding
/// postcondition is critical for the produces decomposition axiom (#2238):
/// without it, the quantified content-equality axiom
/// `produces(it, visited, next) ==> it@[i] == visited[i]` has no ground
/// connection to the original slice, making the content facts useless.
///
/// The iterator's `produces` predicate uses a snapshot-aware model:
/// `*visited[i]` gives the pre-mutation value at each position, while
/// `^visited[i]` describes the post-mutation final value. This is lowered
/// by the driver rewrite in `iterator_spec_rewrite/simple.rs`.
pub const VEC_ITER_MUT: &str = r"
    params: self
    ensures: result@ == self@
    ensures: self@.len() == 0 ==> result.completed()
    ensures: self@.len() > 0 ==> !result.completed()
";

/// Contract for `Vec::into_iter` (owned iterator constructor).
///
/// Seeds the iterator state's view (`result@`) from the source
/// collection's view (`self@`), connecting the `produces` rewrite
/// chain to the original content. (#2172)
pub const VEC_INTO_ITER: &str = r"
    params: self
    ensures: result@.ext_eq(self@)
";

/// Contract for `<Range<T> as IntoIterator>::into_iter`.
///
/// Seeds the iterator's logical start/end from the range fields,
/// connecting the `produces` rewrite chain to the original bounds.
pub const RANGE_INTO_ITER: &str = r"
    params: self
    ensures: result.start_log() == self.start.deep_model()
    ensures: result.end_log() == self.end.deep_model()
";

/// Contract for `core::iter::empty`.
pub const ITER_EMPTY: &str = r"
    ensures: result.completed()
";

/// Contract for `core::iter::once`.
pub const ITER_ONCE: &str = r"
    params: value
    ensures: result@ == Some(value)
";

/// Contract for `core::iter::repeat`.
pub const ITER_REPEAT: &str = r"
    params: value
    ensures: result@ == value
";

/// Contract for `Iterator::fuse`.
pub const ITER_FUSE: &str = r"
    params: self
    ensures: result.iter() == self
";

/// Contract for `Iterator::cloned`.
pub const ITER_CLONED: &str = r"
    params: self
    ensures: result.iter() == self
";

/// Contract for `Iterator::copied`.
pub const ITER_COPIED: &str = r"
    params: self
    ensures: result.iter() == self
    ensures: result@ == self@
";

/// Contract for `Iterator::skip`.
pub const ITER_SKIP: &str = r"
    params: self, n
    ensures: result.iter() == self
    ensures: result.n() == n
";

/// Contract for `Iterator::take`.
pub const ITER_TAKE: &str = r"
    params: self, n
    ensures: result.iter() == self
    ensures: result.n() == n
";

/// Contract for `Iterator::enumerate`.
pub const ITER_ENUMERATE: &str = r"
    params: self
    requires: forall<i: &mut _> (*i).completed() ==> (*i).produces(Seq::empty(), ^i)
    requires: forall<s: Seq, i: _> self.produces(s, i) ==> s.len() < core::usize::MAX@
    ensures: result.iter() == self
    ensures: result.n()@ == 0
";

/// Contract for `Iterator::zip`.
pub const ITER_ZIP: &str = r"
    params: self, other
    requires: U::into_iter.precondition((other,))
    ensures: result.itera() == self
    ensures: U::into_iter.postcondition((other,), result.iterb())
";

/// Contract for `Iterator::collect`.
///
/// The collected result must satisfy the reusable `FromIteratorSpec`
/// bridge for its concrete output type. This lets `Vec`, `HashMap`, and
/// other collection types supply a structural postcondition without
/// duplicating the `collect()` lowering. (#2116)
///
/// The `result@ == self@` clause is the round-trip bridge: when the
/// iterator's view sort matches the result collection's view sort
/// (e.g., `HashMap::IntoIter` ↔ `HashMap` both view as `FMap`, `Vec::IntoIter`
/// ↔ `Vec` both view as `Seq`, `HashSet::IntoIter` ↔ `HashSet` both view
/// as `FSet`), the collected result extensionally matches the source. The
/// solver applies this clause when the view sorts unify; otherwise it is
/// vacuous. This closes the `xs.into_iter().collect()` ext-equality gap
/// (#bucket-B-cc-collections).
///
/// Note: post-borrowck MIR does NOT inline `collect()` to `FromIterator::from_iter`,
/// so `Iterator::collect` is the path that actually appears at call sites.
/// The `FromIterator::from_iter` entries in collections.rs handle the rare
/// case of direct `from_iter` calls.
pub const ITERATOR_COLLECT: &str = r"
    params: self
    ensures: result.from_iter_post(self@)
    ensures: result@ == self@
";

/// Contract for `<Vec<T> as FromIterator<T>>::from_iter`.
///
/// Constrains the result through the `FromIteratorSpec` relation:
/// the collected Vec's view satisfies `from_iter_post(prod)` where `prod`
/// is the iterator's view (the produced element sequence). For Vec,
/// `from_iter_post(prod)` ≡ `result@.ext_eq(prod)`. (#2217)
///
/// This spec handles direct `from_iter` calls on Vec. The more common
/// `Iterator::collect` path uses `ITERATOR_COLLECT` above.
pub const VEC_FROM_ITER: &str = r"
    params: iter
    ensures: result.from_iter_post(iter@)
";

/// Contract for `Iterator::map`.
///
/// Wraps the iterator and closure, preserving both in the result.
/// The `produces` predicate on `Map` relates inner-iterator production to
/// the closure's application on each element.
///
/// Reference: `creusot-std/src/std/iter.rs` — `Iterator::map` extern spec
pub const ITER_MAP: &str = r"
    params: self, f
    ensures: result.iter() == self
    ensures: result.func() == f
";

/// Contract for `Iterator::filter`.
///
/// Wraps the iterator and predicate, preserving both in the result.
/// The `produces` predicate on `Filter` relates inner-iterator production to
/// the predicate selecting a subsequence of elements.
///
/// Reference: `creusot-std/src/std/iter.rs` — `Iterator::filter` extern spec
pub const ITER_FILTER: &str = r"
    params: self, f
    ensures: result.iter() == self
    ensures: result.func() == f
";

/// Contract for `Iterator::filter_map`.
///
/// Wraps the iterator and closure, preserving both in the result.
/// The `produces` predicate on `FilterMap` relates inner-iterator production
/// to the closure selecting and transforming a subsequence of elements.
///
/// Reference: `creusot-std/src/std/iter.rs` — `Iterator::filter_map` extern spec
pub const ITER_FILTER_MAP: &str = r"
    params: self, f
    ensures: result.iter() == self
    ensures: result.func() == f
";

/// Contract for `Iterator::rev`.
///
/// Wraps the iterator in `Rev`, preserving the inner iterator's state.
/// `Rev<I>` delegates forward `produces` to the inner `produces_back`. (#2217)
pub const ITERATOR_REV: &str = r"
    params: self
    ensures: result.iter() == self
";

/// Contract for `DoubleEndedIterator::next_back`.
///
/// Mirrors `Iterator::next` but consumes from the back:
/// - `None` → iterator is completed
/// - `Some(v)` → one-step reverse production with `produces_back`
pub const DOUBLE_ENDED_NEXT_BACK: &str = r"
    params: self
    ensures: match result {
        None => self.completed(),
        Some(v) => (*self).produces_back(seq![v], ^self),
    }
";

/// Contract for `Iterator::sum`.
///
/// Consumes the iterator, producing the sum of all elements. The result
/// is unconstrained beyond the iterator being fully consumed — the solver
/// cannot express generic summation without induction, but having a spec
/// prevents the opaque-call fallback from assuming `true` postcondition.
///
/// For concrete usage patterns (e.g., summing a known-length sequence),
/// the type constraint `result@ >= 0` for unsigned types is added.
pub const ITERATOR_SUM: &str = r"
    params: self
    ensures: result@ >= 0
";

/// Contract for `Iterator::count`.
///
/// Consumes the iterator, returning the number of elements. The result
/// is non-negative. For iterators with a known-length view, this equals
/// the view's length.
pub const ITERATOR_COUNT: &str = r"
    params: self
    ensures: result@ >= 0
";

/// Contract for `Iterator::for_each`.
///
/// Consumes the iterator, calling the closure on each element. Prevents
/// opaque-call fallback. Logically equivalent to a for loop.
pub const ITERATOR_FOR_EACH: &str = r"
    params: self, f
";

/// Contract for `Iterator::fold`.
///
/// Consumes the iterator with an accumulator. The result is
/// unconstrained beyond the iterator being fully consumed — fold
/// requires induction to express precisely. Having a spec prevents
/// the opaque-call `true` assumption.
pub const ITERATOR_FOLD: &str = r"
    params: self, init, f
";

/// Contract for `Iterator::any`.
///
/// Consumes the iterator (partially), returning whether any element
/// satisfies the predicate. Prevents opaque-call fallback.
pub const ITERATOR_ANY: &str = r"
    params: self, f
";

/// Contract for `Iterator::all`.
///
/// Consumes the iterator (partially), returning whether all elements
/// satisfy the predicate. Prevents opaque-call fallback.
pub const ITERATOR_ALL: &str = r"
    params: self, f
";

/// Contract for `Iterator::find`.
///
/// Returns the first element satisfying the predicate, or None.
/// Prevents opaque-call fallback.
pub const ITERATOR_FIND: &str = r"
    params: self, predicate
";

/// Contract for `Iterator::position`.
///
/// Returns the index of the first element satisfying the predicate.
/// The result (if Some) is a valid index into the produced sequence.
pub const ITERATOR_POSITION: &str = r"
    params: self, predicate
    ensures: match result {
        Some(i) => i@ >= 0,
        None => true,
    }
";

/// Contract for `Iterator::chain`.
///
/// Chains two iterators. The result iterator produces elements from
/// self first, then from other.
pub const ITERATOR_CHAIN: &str = r"
    params: self, other
    ensures: result.a() == self
";

/// Contract for `Iterator::peekable`.
///
/// Wraps the iterator in a Peekable adapter.
pub const ITERATOR_PEEKABLE: &str = r"
    params: self
    ensures: result.iter() == self
";

/// Contract for `Iterator::flat_map`.
///
/// Wraps the iterator and closure, preserving both in the result.
pub const ITER_FLAT_MAP: &str = r"
    params: self, f
    ensures: result.iter() == self
    ensures: result.func() == f
";

/// Contract for `Iterator::inspect`.
///
/// Wraps the iterator and closure. Does not change produced elements.
pub const ITER_INSPECT: &str = r"
    params: self, f
    ensures: result.iter() == self
";

/// Contract for `Iterator::step_by`.
///
/// Creates an iterator starting at the same point, but stepping by
/// the given amount at each iteration.
pub const ITER_STEP_BY: &str = r"
    params: self, step
    ensures: result.iter() == self
";

/// Contract for `Iterator::take_while`.
///
/// Creates an iterator that yields elements based on a predicate.
pub const ITER_TAKE_WHILE: &str = r"
    params: self, predicate
    ensures: result.iter() == self
    ensures: result.func() == predicate
";

/// Contract for `Iterator::skip_while`.
///
/// Creates an iterator that rejects elements based on a predicate.
pub const ITER_SKIP_WHILE: &str = r"
    params: self, predicate
    ensures: result.iter() == self
    ensures: result.func() == predicate
";

/// Contract for `Iterator::min`.
///
/// Returns the minimum element. Prevents opaque-call fallback.
pub const ITERATOR_MIN: &str = r"
    params: self
";

/// Contract for `Iterator::max`.
///
/// Returns the maximum element. Prevents opaque-call fallback.
pub const ITERATOR_MAX: &str = r"
    params: self
";

/// Contract for `Iterator::last`.
///
/// Consumes the iterator, returning the last element.
pub const ITERATOR_LAST: &str = r"
    params: self
";

/// Contract for `Iterator::nth`.
///
/// Returns the nth element of the iterator.
pub const ITERATOR_NTH: &str = r"
    params: self, n
";

/// Contract for `Iterator::flatten`.
///
/// Creates an iterator that flattens nested structure.
pub const ITER_FLATTEN: &str = r"
    params: self
    ensures: result.iter() == self
";

/// Contract for `Iterator::unzip`.
///
/// Converts an iterator of pairs into a pair of containers.
pub const ITERATOR_UNZIP: &str = r"
    params: self
";

/// Contract for `Iterator::min_by`.
///
/// Returns the element that gives the minimum value from the
/// specified function.
pub const ITERATOR_MIN_BY: &str = r"
    params: self, compare
";

/// Contract for `Iterator::max_by`.
///
/// Returns the element that gives the maximum value from the
/// specified function.
pub const ITERATOR_MAX_BY: &str = r"
    params: self, compare
";

/// Contract for `Iterator::min_by_key`.
///
/// Returns the element that gives the minimum value from the
/// specified key extraction function.
pub const ITERATOR_MIN_BY_KEY: &str = r"
    params: self, f
";

/// Contract for `Iterator::max_by_key`.
///
/// Returns the element that gives the maximum value from the
/// specified key extraction function.
pub const ITERATOR_MAX_BY_KEY: &str = r"
    params: self, f
";

/// Contract for `Iterator::product`.
///
/// Iterates over the entire iterator, multiplying all elements.
pub const ITERATOR_PRODUCT: &str = r"
    params: self
";

/// Contract for `Iterator::find_map`.
///
/// Applies function to the elements and returns the first non-None result.
pub const ITERATOR_FIND_MAP: &str = r"
    params: self, f
";

/// Contract for `Iterator::reduce`.
///
/// Reduces the elements to a single one, by repeatedly applying a reducing operation.
pub const ITERATOR_REDUCE: &str = r"
    params: self, f
";

/// Contract for `ExactSizeIterator::len`.
///
/// Returns the exact remaining length of the iterator.
pub const EXACT_SIZE_ITER_LEN: &str = r"
    params: self
    ensures: result@ >= 0
";

/// Contract for `Iterator::map_while`.
///
/// Wraps iterator with predicate-driven mapping that stops on None.
pub const ITER_MAP_WHILE: &str = r"
    params: self, predicate
";

/// Contract for `Iterator::scan`.
///
/// Wraps iterator with stateful transformation.
pub const ITER_SCAN: &str = r"
    params: self, initial_state, f
";

/// Contract for `Iterator::try_fold`.
///
/// Foldable that can fail early.
pub const ITERATOR_TRY_FOLD: &str = r"
    params: self, init, f
";

/// Contract for `Iterator::try_for_each`.
///
/// Applies fallible function to each element, stopping on first error.
pub const ITERATOR_TRY_FOR_EACH: &str = r"
    params: self, f
";

/// Contract for `Iterator::is_sorted`.
///
/// Returns true if elements are sorted.
pub const ITERATOR_IS_SORTED: &str = r"
    params: self
";

/// Contract for `Iterator::partition`.
///
/// Splits elements into two collections based on predicate.
pub const ITERATOR_PARTITION: &str = r"
    params: self, f
";

/// Contract for `Iterator::eq`.
///
/// Tests element-wise equality of two iterators.
pub const ITERATOR_EQ: &str = r"
    params: self, other
";

/// Contract for `Iterator::size_hint`.
///
/// Returns a lower bound and optional upper bound on remaining length.
/// Prevents opaque fallback from internal collect machinery.
pub const ITERATOR_SIZE_HINT: &str = r"
    params: self
";

/// Contract for `Iterator::by_ref`.
///
/// Borrows the iterator rather than consuming it.
pub const ITERATOR_BY_REF: &str = r"
    params: self
";

/// Contract for `Iterator::cmp`.
///
/// Lexicographic comparison of two iterators.
pub const ITERATOR_CMP: &str = r"
    params: self, other
";

/// Contract for `Iterator::partial_cmp`.
///
/// Lexicographic partial comparison of two iterators.
pub const ITERATOR_PARTIAL_CMP: &str = r"
    params: self, other
";

/// Contract for `Iterator::ne`.
///
/// Tests element-wise inequality of two iterators.
pub const ITERATOR_NE: &str = r"
    params: self, other
";

/// Contract for `Iterator::lt`.
///
/// Tests if self is lexicographically less than other.
pub const ITERATOR_LT: &str = r"
    params: self, other
";

/// Contract for `Iterator::le`.
///
/// Tests if self is lexicographically less than or equal to other.
pub const ITERATOR_LE: &str = r"
    params: self, other
";

/// Contract for `Iterator::gt`.
///
/// Tests if self is lexicographically greater than other.
pub const ITERATOR_GT: &str = r"
    params: self, other
";

/// Contract for `Iterator::ge`.
///
/// Tests if self is lexicographically greater than or equal to other.
pub const ITERATOR_GE: &str = r"
    params: self, other
";
