// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Internal specification string constants consumed by trust-wp-driver's
//! table-backed logical lookup path and related local tests.
//!
//! Ghost methods (`*_ghost`) are mutable in-place variants of the logical
//! Seq methods. They operate on `&mut self` inside `ghost!` blocks.
//! Logical methods return new `Seq` values (by-value Creusot semantics).

// ── Ghost (mutable in-place) method specs ──────────────────────────

/// Contract for `Seq::len_ghost` (ghost-block length query)
pub const LEN_GHOST: &str = r"
    params: self
    ensures: result == self.len()
";

/// Contract for `Seq::is_empty_ghost` (ghost-block emptiness check)
pub const IS_EMPTY_GHOST: &str = r"
    params: self
    ensures: result == (self.len() == 0)
";

/// Contract for `Seq::push_back_ghost` (mutable in-place append)
///
/// Post-state equals logical `push_back`. The encoder's Array+Length backing
/// provides element-level properties (length, new element, frame) via shape
/// constraints, so the spec only links the final state to the UF. This avoids
/// a `forall<i>` quantifier that overwhelms the solver in loop contexts where
/// `call_assumptions` flow into `effective_requires`. (#2116)
///
/// Args: self=arg0, x=arg1. Returns `()`.
pub const PUSH_BACK_GHOST: &str = r"
    params: self, arg1
    ensures: ^self == self.push_back(arg1)
";

/// Contract for `Seq::push_front_ghost` (mutable in-place prepend)
///
/// Post-state equals logical `push_front`. The encoder's Array+Length+Offset
/// backing provides element-level properties (length, new element at index 0,
/// element shifting) via shape constraints, so the spec only links the final
/// state to the UF. This avoids a `forall<i>` quantifier that overwhelms the
/// solver when `call_assumptions` flow into `effective_requires` for function-
/// level postcondition checks containing loop-body ghost mutations. (#2116)
///
/// Args: self=arg0, x=arg1. Returns `()`.
pub const PUSH_FRONT_GHOST: &str = r"
    params: self, arg1
    ensures: ^self == self.push_front(arg1)
";

/// Contract for `Seq::get_ghost` (immutable element access by Int index)
///
/// Args: self=arg0, index=arg1. Returns `Option<&T>`.
pub const GET_GHOST: &str = r"
    params: self, arg1
    ensures: match result {
        Some(v) => 0 <= arg1 && arg1 < self.len() && *v == self[arg1],
        None => arg1 < 0 || arg1 >= self.len(),
    }
";

/// Contract for `Seq::get_mut_ghost` (mutable element access by Int index)
///
/// Args: self=arg0, index=arg1. Returns `Option<&mut T>`.
/// Frame: non-accessed indices are unchanged in the post-state.
pub const GET_MUT_GHOST: &str = r"
    params: self, arg1
    ensures: match result {
        Some(v) => 0 <= arg1 && arg1 < self.len() && *v == self[arg1]
            && (^self).len() == self.len()
            && forall<i: Int> 0 <= i && i < self.len() && i != arg1 ==> (^self)[i] == self[i],
        None => arg1 < 0 || arg1 >= self.len(),
    }
";

/// Contract for `Seq::pop_back_ghost` (mutable in-place pop from end)
///
/// Returns the last element if non-empty; post-state has length - 1.
/// Frame: remaining elements are unchanged.
pub const POP_BACK_GHOST: &str = r"
    params: self
    ensures: match result {
        Some(v) => self.len() > 0 && v == self[self.len() - 1]
            && (^self).len() == self.len() - 1
            && forall<i: Int> 0 <= i && i < (^self).len() ==> (^self)[i] == self[i],
        None => self.len() == 0 && (^self).len() == 0,
    }
";

/// Contract for `Seq::pop_front_ghost` (mutable in-place pop from front)
///
/// Returns the first element if non-empty; post-state has remaining
/// elements shifted down by 1.
pub const POP_FRONT_GHOST: &str = r"
    params: self
    ensures: match result {
        Some(v) => self.len() > 0 && v == self[0]
            && (^self).len() == self.len() - 1
            && forall<i: Int> 0 <= i && i < (^self).len() ==> (^self)[i] == self[i + 1],
        None => self.len() == 0 && (^self).len() == 0,
    }
";

// ── Logical (by-value) method specs ────────────────────────────────

/// Contract for `Seq::empty` / `Seq::new`
pub const EMPTY: &str = r"
    params:
    ensures: result == seq_empty()
    ensures: result.len() == 0
";

/// Contract for `Seq::singleton`
/// Args: x=arg0
pub const SINGLETON: &str = r"
    params: arg0
    ensures: result.len() == 1
    ensures: result[0] == arg0
";

/// Contract for `Seq::len`
pub const LEN: &str = r"
    params: self
    ensures: result == self.len()
    ensures: result >= 0
";

/// Contract for `Seq::is_empty`
pub const IS_EMPTY: &str = r"
    params: self
    ensures: result == (self.len() == 0)
";

/// Contract for `Seq::push_back` (logical, returns new Seq)
/// Args: self=arg0, x=arg1
pub const PUSH_BACK: &str = r"
    params: self, arg1
    ensures: result.len() == self.len() + 1
    ensures: result[self.len()] == arg1
    ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i] == self[i]
";

/// Contract for `Seq::push_front` (logical, returns new Seq)
/// Args: self=arg0, x=arg1
pub const PUSH_FRONT: &str = r"
    params: self, arg1
    ensures: result.len() == self.len() + 1
    ensures: result[0] == arg1
    ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i + 1] == self[i]
";

/// Contract for `Seq::get` (returns Option<T>)
/// Args: self=arg0, ix=arg1
pub const GET: &str = r"
    params: self, arg1
    ensures: match result {
        Some(v) => 0 <= arg1 && arg1 < self.len() && v == self[arg1],
        None => arg1 < 0 || arg1 >= self.len(),
    }
";

/// Contract for `Seq::index_logic` (panics if out of bounds)
/// Args: self=arg0, ix=arg1
pub const INDEX_LOGIC: &str = r"
    params: self, arg1
    requires: 0 <= arg1 && arg1 < self.len()
    ensures: result == self[arg1]
";

/// Contract for `Seq::pop_back` (logical, returns new Seq without last element)
pub const POP_BACK: &str = r"
    params: self
    requires: self.len() > 0
    ensures: result.len() == self.len() - 1
    ensures: forall<i: Int> 0 <= i && i < result.len() ==> result[i] == self[i]
";

/// Contract for `Seq::tail` / `Seq::pop_front` (logical, returns new Seq
/// without first element)
pub const TAIL: &str = r"
    params: self
    requires: self.len() > 0
    ensures: result.len() == self.len() - 1
    ensures: forall<i: Int> 0 <= i && i < result.len() ==> result[i] == self[i + 1]
";

/// Contract for `Seq::subsequence`
/// Args: self=arg0, start=arg1, end=arg2
pub const SUBSEQUENCE: &str = r"
    params: self, arg1, arg2
    requires: 0 <= arg1 && arg1 <= arg2 && arg2 <= self.len()
    ensures: result.len() == arg2 - arg1
    ensures: forall<i: Int> 0 <= i && i < result.len() ==> result[i] == self[arg1 + i]
";

/// Contract for `Seq::concat`
/// Args: self=arg0, other=arg1
pub const CONCAT: &str = r"
    params: self, arg1
    ensures: result.len() == self.len() + arg1.len()
    ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i] == self[i]
    ensures: forall<i: Int> 0 <= i && i < arg1.len() ==> result[self.len() + i] == arg1[i]
";

/// Contract for `Seq::set` (returns new Seq with element replaced)
/// Args: self=arg0, ix=arg1, x=arg2
pub const SET: &str = r"
    params: self, arg1, arg2
    requires: 0 <= arg1 && arg1 < self.len()
    ensures: result.len() == self.len()
    ensures: result[arg1] == arg2
    ensures: forall<i: Int> 0 <= i && i < self.len() && i != arg1 ==> result[i] == self[i]
";

/// Contract for `Seq::contains`
/// Args: self=arg0, x=arg1
pub const CONTAINS: &str = r"
    params: self, arg1
    ensures: result == (exists<i: Int> 0 <= i && i < self.len() && self[i] == arg1)
";

/// Contract for `Seq::reverse`
///
/// Length-preserving with index-inversion. The empty-case clause
/// `self.len() == 0 ==> result == self` is the bridge needed by
/// loop initializers like `reverse_ghost` (#bucket-B-seq-iter):
/// at iteration 0, `result == Seq::empty()` and `produced == Seq::empty()`,
/// so the invariant `result == produced.reverse()` reduces to
/// `Seq::empty() == Seq::empty().reverse()`. Without an explicit empty
/// equality, `reverse` returns a fresh seq value distinct from
/// `Seq::empty()` even when length and indexing constraints match.
pub const REVERSE: &str = r"
    params: self
    ensures: result.len() == self.len()
    ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i] == self[self.len() - 1 - i]
    ensures: self.len() == 0 ==> result == self
";

/// Contract for `Seq::ext_eq`
/// Args: self=arg0, other=arg1
pub const EXT_EQ: &str = r"
    params: self, arg1
    ensures: result == (self.len() == arg1.len()
        && forall<i: Int> 0 <= i && i < self.len() ==> self[i] == arg1[i])
";

/// Contract for `Seq::into_inner` (identity on Seq)
pub const INTO_INNER: &str = r"
    params: self
    ensures: result == self
";

/// Contract for `<Seq<T> as Index<Int>>::index` (seq[i] syntax with Int index)
///
/// Delegates to `index_logic`: requires in-bounds, result equals `self[arg1]`.
/// This covers both `Index<Int>` and `Index<i32>` since the encoder coerces
/// i32 indices to Int.
///
/// Args: self=arg0, index=arg1
pub const INDEX: &str = r"
    params: self, arg1
    requires: 0 <= arg1 && arg1 < self.len()
    ensures: *result == self[arg1]
";

/// Contract for `<Seq<T> as Index<usize>>::index` (seq[i] syntax with usize)
///
/// Same as INDEX but for usize. The encoder converts usize to Int.
///
/// Args: self=arg0, index=arg1
pub const INDEX_USIZE: &str = r"
    params: self, arg1
    requires: arg1 < self.len()
    ensures: *result == self[arg1]
";

/// Contract for `Seq<&T>::to_owned_seq` (convert Seq<&T> to Seq<T>)
///
/// In Creusot pearlite, `&T == T` so this is the identity. We model it as
/// preserving length and element equality (after dereferencing).
pub const TO_OWNED_SEQ: &str = r"
    params: self
    ensures: result.len() == self.len()
    ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i] == *self[i]
";

/// Contract for `Seq::sorted` (entire sequence is in ascending order)
pub const SORTED: &str = r"
    params: self
    ensures: result == forall<i: Int, j: Int> 0 <= i && i <= j && j < self.len() ==> self[i] <= self[j]
";

/// Contract for `Seq::sorted_range` (subsequence is in ascending order)
/// Args: self=arg0, start=arg1, end=arg2
pub const SORTED_RANGE: &str = r"
    params: self, arg1, arg2
    requires: 0 <= arg1 && arg1 <= arg2 && arg2 <= self.len()
    ensures: result == forall<i: Int, j: Int> arg1 <= i && i <= j && j < arg2 ==> self[i] <= self[j]
";

/// Contract for `Seq::permutation_of` (same multiset of elements)
/// Args: self=arg0, other=arg1
pub const PERMUTATION_OF: &str = r"
    params: self, arg1
    ensures: result ==> self.len() == arg1.len()
";

/// Contract for `Seq::count` (number of occurrences of an element)
/// Args: self=arg0, x=arg1
pub const COUNT: &str = r"
    params: self, arg1
    ensures: result >= 0
    ensures: result <= self.len()
";

/// Contract for `Seq::exchange` (swap two elements)
/// Args: self=arg0, other=arg1, i=arg2, j=arg3
pub const EXCHANGE: &str = r"
    params: self, arg1, arg2, arg3
    ensures: result ==> self.len() == arg1.len()
    ensures: result ==> arg1[arg2] == self[arg3]
    ensures: result ==> arg1[arg3] == self[arg2]
    ensures: result ==> forall<k: Int> 0 <= k && k < self.len() && k != arg2 && k != arg3 ==> arg1[k] == self[k]
";
